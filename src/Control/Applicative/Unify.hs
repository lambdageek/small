{-# language GADTs, TypeFamilies, RankNTypes, GeneralizedNewtypeDeriving, TypeOperators, DataKinds, PolyKinds #-}
module Control.Applicative.Unify (
  -- * Constraint Generating Applicative functor
  ConstraintGenerating (..)
  , HasUVar (..)
  , All (..)
  , HindleyMilner (..)
  , (<&>)
  -- * Free Constraint Generating Applicative functor
  , Constraint (..)
  , CG
  , ConstraintGen (..)
  -- * re-export Ap from free
  , module Control.Applicative.Free.Final
  ) where

import Control.Applicative.Free.Final (Ap(..), liftAp, runAp)

-- Hindley-Milner Elaboration in the Applicative Style
-- note that the constraint generation applicative functor is just the free applicative
-- over the two base operations of term (ie type) equality constraints t₁≐t₂ and
-- fresh unification variable selection.

data Constraint k x v t y a where
  Unify :: t v -> t v -> Constraint k x v t y ()
  Exist :: (v -> k a) -> Constraint k x v t y (t v, a)
  -- term variable definition
  CDef :: t v -> (x -> k a) -> Constraint k x v t y (y -> a)
  CLet :: (v -> k c1) -> (x -> k c2) -> Constraint k x v t y (All v (t v, All v c1), (y -> c2))

-- | Type @All a b@ is the n-ary simultanteous binder for n variables of type @a@ scoping over object @b@.
-- for example type schemes ∀α₁…αₙ.τ  are encoded as @All n f@ where @f [α₁,…,αₙ] = τ@
data All a b = All Int ([a] -> b)

type CG x v t y = Constraint (ConstraintGen x v t y) x v t y

newtype ConstraintGen x v t y a = ConstraintGen {unConstraintGen :: Ap (CG x v t y) a }
  deriving (Functor, Applicative)

class Applicative u => ConstraintGenerating u where
  type UVar u :: *
  type UTerm u :: *
  tt :: u ()
  (~&&~) :: u a -> u b -> u (a,b)
  exist :: (UVar u -> u a) -> u (UTerm u, a)
  (~?~) :: UTerm u -> UTerm u -> u ()

class ConstraintGenerating u => HindleyMilner u where
  type SchemeVar u :: *
  type WitnessVar u :: *
  cdef :: UTerm u -> (SchemeVar u -> u a) -> u (WitnessVar u -> a)
  clet :: (UVar u -> u c1) -> (SchemeVar u -> u c2) -> u (All (UVar u) (UTerm u, All (UVar u) c1), (WitnessVar u -> c2))

class HasUVar u t where
  injUVar :: u -> t

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)

instance ConstraintGenerating (ConstraintGen x v t y) where
  type UVar (ConstraintGen x v t y) = v
  type UTerm (ConstraintGen x v t y) = t v
  tt = pure ()
  c1 ~&&~ c2 = ConstraintGen ((,) <$> unConstraintGen c1 <*> unConstraintGen c2)
  t1 ~?~ t2 = ConstraintGen (liftAp (Unify t1 t2))
  exist f = ConstraintGen (liftAp (Exist f))


