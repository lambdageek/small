module Language.Monotype where

import qualified Data.Set as S
import Data.Traversable (foldMapDefault)

import Control.Applicative.Unify


data Type v u =
  BaseT
  | VarT v
  | UVT u
  | ArrT (Type v u) (Type v u)
    deriving (Eq)

instance (Show v, Show u) => Show (Type v u) where
  show BaseT = "b"
  show (VarT a) = show a
  show (UVT x) = show x
  show (ArrT t1 t2) = "arr(" ++ show t1 ++ "; " ++ show t2 ++ ")"

instance Functor (Type v) where
  fmap h t =
    case t of
      BaseT -> BaseT
      VarT v -> VarT v
      UVT u -> UVT (h u)
      ArrT t1 t2 -> ArrT (fmap h t1) (fmap h t2)

instance Traversable (Type v) where
  traverse h t =
    case t of
      BaseT -> pure BaseT
      VarT v -> pure (VarT v)
      UVT u -> UVT <$> h u
      ArrT t1 t2 -> ArrT <$> traverse h t1 <*> traverse h t2

instance HasUVar u (Type v u) where
  injUVar = UVT

instance Foldable (Type v) where
  foldMap = foldMapDefault

freeUVars :: Ord u => Type v u -> [u]
freeUVars = S.toList . foldMap (S.singleton) 

