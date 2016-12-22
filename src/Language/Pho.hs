{-# Language GeneralizedNewtypeDeriving, RankNTypes #-}
module Language.Pho where

import Control.Monad.Reader

data Term' f v =
  VarM (f v)
  | LamM (v -> Term' f v)
  | AppM (Term' f v) (Term' f v)
  | LetM (Term' f v) (v -> Term' f v)

type Term f = forall v . Term' f v

class Applicative m => MonadName m where
  scopeName :: (Name -> m a) -> m a

newtype NameSource a = NameSource { unNameSource :: Reader [Name] a }
  deriving (Functor, Applicative, Monad)

instance MonadName NameSource where
  scopeName f = NameSource $ do
    (name:names) <- ask
    local (const names) $ unNameSource (f name)

scopeWithName :: MonadName m => (Name -> m a) -> m (Name, a)
scopeWithName f = scopeName (\x -> (,) <$> pure x <*> f x)

newtype Name = Name { nameString :: String }

instance Show Name where
  show (Name n) = n

showTerm' :: (Show (f Name), MonadName m) => Term' f Name -> m String
showTerm' m =
  case m of
    VarM nm -> pure (show nm)
    LamM f -> showLam <$> scopeWithName (showTerm' . f)
    AppM m1 m2 -> showApp <$> showTerm' m1 <*> showTerm' m2
    LetM m f -> showLet <$> showTerm' m <*> scopeWithName (showTerm' . f)
  where
    showLam (x,s) = "lam(" ++ show x ++ "." ++ s ++ ")"
    showApp s1 s2 = "app(" ++ s1 ++ "; " ++ s2 ++ ")"
    showLet s (x,s') = "let(" ++ s ++ "; " ++ show x ++ "." ++ s' ++ ")"

instance (Show (f Name)) => Show (Term' f Name) where
  show = showTerm

showTerm :: (Show (f Name)) => Term' f Name -> String
showTerm m = runReader (unNameSource (showTerm' m)) (map Name $ varNames ["x", "y", "z", "i", "j", "k", "a", "b", "c", "d", "e", "f"])

varNames :: [String] -> [String]
varNames ptn = ptn ++ go 1 ptn 
  where
    go :: Int -> [String] -> [String]
    go n (x:xs) = (x ++ show n) : go n xs
    go n [] = (go $! n + 1) ptn

