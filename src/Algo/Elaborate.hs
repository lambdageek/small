{-# language RankNTypes, GADTs, TypeFamilies, GeneralizedNewtypeDeriving #-}
module Algo.Elaborate where

import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor.Identity
import Data.List (intercalate)

import Control.Applicative.Effect
import Control.Applicative.Unify
import qualified Data.Constraint.Simple as Simple
import Language.Monotype
import Language.Pho

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)

hasType' :: (HindleyMilner m,
             UVar m ~ u,
             UTerm m ~ Type v u)
         => Term' Identity (SchemeVar m) ->  UTerm m -> m ()
hasType' m w =
  case m of
    VarM x -> cinst (runIdentity x) w <&> const ()
    AppM m1 m2 ->
      exist (\u -> hasType' m1 (ArrT (UVT u) w) ~&&~ hasType' m2 (UVT u)) <&> const ()
    LamM f ->
      exist (\dom -> exist $ \cod ->
                w ~?~ (ArrT (UVT dom) (UVT cod))
                ~&&~
                cdef (UVT dom) (\x -> hasType' (f x) (UVT cod) *> pure f))
      <&> const ()
    LetM m1 f ->
      clet (\u -> hasType' m1 (UVT u)) (\x -> hasType' (f x) w) <&> const ()

     
hasType :: Term Identity -> Type v u -> ConstraintGen x u (Type v u) c y ()
hasType m w = hasType' m w

newtype U = U String

instance Show U where
  show (U s) = s

collectSimpleConstraints' :: (HasUVar u (t u))
                          => ConstraintGen (t u -> [Simple.Constraint t u]) u (t u) c y a
                          -> Effect () (Writer [Simple.Constraint t u]) a
collectSimpleConstraints' (ConstraintGen cg) = runAp phi cg
  where
    phi :: (HasUVar u (t u))
        => CG (t u -> [Simple.Constraint t u]) u (t u) c y a
        -> Effect () (Writer [Simple.Constraint t u]) a
    phi c_ =
      case c_ of
        Unify t1 t2 -> effect $ tell [Simple.Unify t1 t2]
        Exist f -> effect $ tell [Simple.Exist $ \v -> collectSimpleConstraints (f v)]
        CDef t cbody ->
          let c = \t' -> [Simple.Unify t t']
          in let ex = Simple.Exist (\u -> c (injUVar u))
                 bs = collectSimpleConstraints (cbody c)
             in effect $ tell (ex : bs)
        CLet cx cbody ->
          let c = collectSimpleConstraints . cx
          in let
            ex = Simple.Exist (\u -> c u)
            bs = collectSimpleConstraints (cbody (\t -> [Simple.Exist (\u -> [Simple.Unify t (injUVar u)] ++ c u)]))
            in effect $ tell (ex : bs)
        CInst x t -> effect $ tell (x t)

collectSimpleConstraints :: (HasUVar u (t u))
                         => ConstraintGen (t u -> [Simple.Constraint t u]) u (t u) c y a
                         -> [Simple.Constraint t u]
collectSimpleConstraints = snd . runWriter . runEffect . collectSimpleConstraints'

showConstraint :: (Show (t U), HasUVar U (t U)) => ConstraintGen (t U -> [Simple.Constraint t U]) U (t U) c y a -> String
showConstraint = showSimpleConstraints . collectSimpleConstraints

-- version of showConstraint with y unified to a dummy type.
showConstraint_ :: (Show (t U), HasUVar U (t U)) => ConstraintGen (t U -> [Simple.Constraint t U]) U (t U) c () a -> String
showConstraint_ = showConstraint

showSimpleConstraints :: (Show (t U)) => [Simple.Constraint t U] -> String
showSimpleConstraints ss = runReader (showSimpleConstraints' ss) (map U $ varNames ["u", "v", "w"])

showSimpleConstraints' :: (Show (t U)) => [Simple.Constraint t U] -> Reader [U] String
showSimpleConstraints' ss = do
  strs <- mapM showSimpleConstraint ss
  return (intercalate " & " strs)

showSimpleConstraint :: (Show (t U)) => Simple.Constraint t U -> Reader [U] String
showSimpleConstraint s =
  case s of
    Simple.Unify t1 t2 -> return (show t1 ++ " =?= " ++ show t2)
    Simple.Exist f -> do
      (u:us) <- ask
      c <- local (const us) $ showSimpleConstraints' (f u)
      return $ "∃(" ++ show u ++ "." ++ c ++ ")"
