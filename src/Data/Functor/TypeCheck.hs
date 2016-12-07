{-# language GADTs, TypeFamilies, GeneralizedNewtypeDeriving, RankNTypes, UndecidableInstances #-}
module Data.Functor.TypeCheck where

import Control.Monad.Free.Church
import Control.Monad.Cont

data TypeCheckF v t next where
  LookupCtx :: v -> (t -> next) -> TypeCheckF v t next
  ExtendCtx :: v -> t -> next -> TypeCheckF v t next

data Pair a b = Pair !a !b

data TypeCheckC v t a where
  LookupCtxC :: v -> TypeCheckC v t t
  ExtendCtxC :: v -> t -> TypeCheckC v t (Pair v t)
  
instance Functor (TypeCheckF v t) where
  fmap f (LookupCtx x k) = LookupCtx x (f . k)
  fmap f (ExtendCtx x ty k) = ExtendCtx x ty (f k)

lookupCtx :: MonadFree (TypeCheckF v t) m => v -> m t
lookupCtx v = liftF (LookupCtx v id)

extendCtx :: MonadFree (TypeCheckF v t) m => v -> t -> m a -> m a
extendCtx v t = wrap . ExtendCtx v t

newtype FF g a = FF {unFF :: forall r . (forall x . g x -> Cont r x) -> Cont r a}

instance Functor (FF g) where
  fmap f (FF m) = FF (\phi -> fmap f (m phi))

instance Applicative (FF g) where
  pure = ffpure
  (FF mf) <*> (FF mx) = FF (\phi -> mf phi <*> mx phi)

instance Monad (FF g) where
  return = pure
  (FF mx) >>= f = FF (\phi -> mx phi >>= \x -> unFF (f x) phi)

ffpure :: a -> FF g a
ffpure x = FF (\_phi -> pure x)

ffeff :: g a -> FF g a
ffeff eff = FF (\phi -> phi eff)

ffimpure :: g x -> (x -> FF g a) -> FF g a
ffimpure eff k = ffeff eff >>= k

retract :: Monad m => FF m a -> m a
retract (FF imp) = runCont (imp (\mx -> cont (\k -> mx >>= k))) return

instance MonadFree g (FF g) where
  wrap fmx = FF (\phi -> phi fmx >>= \(FF mx) -> mx phi)
