-- | An Applicative functor encapsulating a monadic computation that doesn't carry its parameter.
module Control.Applicative.Effect (
  Effect (..),
  effect
  ) where

-- | An Applicative that encapsulates some monadic effect and doesn't
-- care about its argument.  (It's not 'Data.Functor.Const.Const'
-- because that would require @m r@ to be a Monoid which is weird).
-- We need this in order to apply a natural transformation over a
-- 'Constraint' without actually having to solve an 'Exist' constraint
-- (because the GADT wants a result term in that case)
newtype Effect r m a = Effect { runEffect :: m r }

effect :: m r -> Effect r m a
effect = Effect

instance Functor (Effect r m) where
  fmap _ = effect . runEffect

instance (Applicative m, Monoid r) => Applicative (Effect r m) where
  pure _ = effect (pure mempty)
  ef <*> ex = effect (mappend <$> runEffect ef <*> runEffect ex)

