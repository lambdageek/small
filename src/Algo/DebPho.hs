{-# Language RankNTypes #-}
module Algo.DebPho where

import Control.Monad.Reader

import Language.Deb
import Language.Pho

ex0 :: Term
ex0 = LamM $ \x -> VarM x

ex1 :: Term
ex1 = LetM (LamM $ \x -> VarM x) $ \f -> LamM $ \x -> AppM (VarM f) (AppM (VarM f) (VarM x))

ex2 :: Term
ex2 = LamM $ \x -> LamM $ \y -> AppM (VarM y) (LamM $ \_z -> (VarM x))


scopeDeb :: MonadReader Int m => (Int -> m a) -> m a
scopeDeb f = local (+1) (ask >>= f)

debruijn' :: Term' Int -> Reader Int Expr
debruijn' m =
  case m of
    VarM n -> do
      k <- ask
      return $ VarE (k - n)
    AppM m1 m2 -> AppE <$> debruijn' m1 <*> debruijn' m2
    LamM f -> 
      LamE <$> scopeDeb (debruijn' . f)
    LetM m f -> LetE <$> debruijn' m <*> scopeDeb (debruijn' . f)

debruijn :: Term -> Expr
debruijn m = runReader (debruijn' m) 0
      


hoark :: MonadReader [a] m => (Reader [a] b) -> m (a -> b)
hoark c = do
  vs <- ask
  return $ (\v -> runReader c (v:vs))

phoas' :: Expr -> Reader [a] (Term' a)
phoas' e =
  case e of
    VarE n -> VarM <$> asks (!! n)
    AppE e1 e2 -> AppM <$> phoas' e1 <*> phoas' e2
    LamE e -> LamM <$> hoark (phoas' e)
    LetE e e' -> LetM <$> phoas' e <*> hoark (phoas' e')
    
phoas :: Expr -> Term
phoas e = runReader (phoas' e) []
