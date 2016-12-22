{-# Language RankNTypes #-}
module Algo.DebPho where

import Control.Monad.Reader
import Data.Functor.Identity

import Language.Deb
import Language.Pho

var :: v -> Term' Identity v
var = VarM . Identity

ex0 :: Term Identity
ex0 = LamM $ \x -> var x

ex1 :: Term Identity
ex1 = LetM (LamM $ \x -> var x) $ \f -> LamM $ \x -> AppM (var f) (AppM (var f) (var x))

ex2 :: Term Identity
ex2 = LamM $ \x -> LamM $ \y -> AppM (var y) (LamM $ \_z -> (var x))


scopeDeb :: MonadReader Int m => (Int -> m a) -> m a
scopeDeb f = local (+1) (ask >>= f)

debruijn' :: Term' Identity Int -> Reader Int Expr
debruijn' m =
  case m of
    VarM n_ -> do
      let n = runIdentity n_
      k <- ask
      return $ VarE (k - n)
    AppM m1 m2 -> AppE <$> debruijn' m1 <*> debruijn' m2
    LamM f -> 
      LamE <$> scopeDeb (debruijn' . f)
    LetM m f -> LetE <$> debruijn' m <*> scopeDeb (debruijn' . f)

debruijn :: Term Identity -> Expr
debruijn m = runReader (debruijn' m) 0
      


hoark :: MonadReader [a] m => (Reader [a] b) -> m (a -> b)
hoark c = do
  vs <- ask
  return $ (\v -> runReader c (v:vs))

phoas' :: Expr -> Reader [a] (Term' Identity a)
phoas' e =
  case e of
    VarE n -> (VarM . Identity) <$> asks (!! n)
    AppE e1 e2 -> AppM <$> phoas' e1 <*> phoas' e2
    LamE e -> LamM <$> hoark (phoas' e)
    LetE e e' -> LetM <$> phoas' e <*> hoark (phoas' e')
    
phoas :: Expr -> Term Identity
phoas e = runReader (phoas' e) []
