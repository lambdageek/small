{-# language RankNTypes, GADTs #-}
module Algo.Elaborate where

import Control.Monad.Reader
import Control.Monad.Writer
import Data.List (intercalate)

import Control.Applicative.Effect
import Control.Applicative.Unify
import Language.Monotype
import Language.Pho




data TypeScheme v u = TSZ (Type v u) | TSS (v -> TypeScheme v u)

generalize' :: Type v v -> Type v a
generalize' t =
  case t of
    BaseT -> BaseT
    VarT v -> VarT v
    UVT v -> VarT v
    ArrT t1 t2 -> ArrT (generalize' t1) (generalize' t2)

-- | An abbreviation "let x=α.C₁[α] in C₂{x}" means "∃α.C₁[α] ∧ C₂{α.C₁[α]/x}" where
--   C{α.D[α]/x} is defined by cases on C as
--     True {α.D[α]/x}       = True
--     C₁{x}∧C₂{x} {α.D[α]/x} = C₁{α.D[α]/x} ∧ C₂{α.D[α]/x}
--     x τ {α.D[α]/x}        = D[τ/α]
--     y τ {α.D[α]/x}        = y τ       when x≠y
--     (let y=β.C₁[β]{x} in C₂{y}{x}) {α.D[α]/x} = let y = β.C₁[β]{α.D[α]/x} in C₂{y}{α.D[α]/x} where y and β are each fresh in α.D[α]
letC :: (ConstraintGenerating m, UVar m ~ u, UTerm m ~ t, HasUVar u t) => Schematic m a -> (Schematic m a -> m b) -> m ((UTerm m, a), b)
letC x body = exist (\a -> x (injUVar a)) ~&&~ body x

-- instantiation of a constraint-scheme on a type.
instC :: Schematic m a -> UTerm m -> m a
instC x w = x w

hasType' :: (ConstraintGenerating m, UVar m ~ u, UTerm m ~ Type v u) => Term' (Schematic m ()) -> UTerm m -> m ()
hasType' m w =
  case m of
    VarM x -> instC x w
    AppM m1 m2 ->
      exist (\u -> hasType' m1 (ArrT (UVT u) w) ~&&~ hasType' m2 (UVT u)) <&> (\_ -> ())
    LamM f ->
      exist (\dom -> exist $ \cod ->
                w ~?~ (ArrT (UVT dom) (UVT cod))
                ~&&~
                letC (~?~ UVT dom) (\x -> hasType' (f x) (UVT cod)))
      <&> const ()
    LetM m1 f ->
      letC (hasType' m1) (\x -> hasType' (f x) w) <&> const ()
      
hasType :: Term -> Type v u -> ConstraintGen u (Type v) ()
hasType m w = hasType' m w

newtype U = U String

instance Show U where
  show (U s) = s

collectSimpleConstraints' :: ConstraintGen u t a -> Effect () (Writer [SimpleConstraint t u]) a
collectSimpleConstraints' (ConstraintGen cg) = runAp phi cg
  where
    phi :: Constraint (ConstraintGen u t) u t a -> Effect () (Writer [SimpleConstraint t u]) a
    phi c =
      case c of
        Unify t1 t2 -> effect $ tell [SUnify t1 t2]
        Exist f -> effect $ tell [SExist $ \v -> collectSimpleConstraints (f v)]

collectSimpleConstraints :: ConstraintGen u t a -> [SimpleConstraint t u]
collectSimpleConstraints = snd . runWriter . runEffect . collectSimpleConstraints'

showConstraint :: (Show (t U)) => ConstraintGen U t a -> String
showConstraint = showSimpleConstraints . collectSimpleConstraints

showSimpleConstraints :: (Show (t U)) => [SimpleConstraint t U] -> String
showSimpleConstraints ss = runReader (showSimpleConstraints' ss) (map U $ varNames ["u", "v", "w"])

showSimpleConstraints' :: (Show (t U)) => [SimpleConstraint t U] -> Reader [U] String
showSimpleConstraints' ss = do
  strs <- mapM showSimpleConstraint ss
  return (intercalate " & " strs)

showSimpleConstraint :: (Show (t U)) => SimpleConstraint t U -> Reader [U] String
showSimpleConstraint s =
  case s of
    SUnify t1 t2 -> return (show t1 ++ " =?= " ++ show t2)
    SExist f -> do
      (u:us) <- ask
      c <- local (const us) $ showSimpleConstraints' (f u)
      return $ "∃(" ++ show u ++ "." ++ c ++ ")"
