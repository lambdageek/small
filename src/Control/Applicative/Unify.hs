{-# language GADTs, TypeFamilies, RankNTypes, GeneralizedNewtypeDeriving, TypeOperators, DataKinds, KindSignatures, PolyKinds #-}
module Control.Applicative.Unify (
  -- * Constraint Generating Applicative functor
  ConstraintGenerating (..)
  , HasUVar (..)
  , All (..)
  , HindleyMilner (..)
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

-- | @Constraint k x v t y a@ is a PHOAS-representation constraint algebra where
-- 
--   * @k :: ⋆ → ⋆@ ties the recursive knot
-- 
--   * @x :: ⋆@ the type of constraint-scheme variables, that is,
--     variables that are introduced during the constraint generation
--     phase that stand for constraints @α.C[α]@ with a distinguished
--     variable that will stand for different types wherever @x@
--     occurs in subsequent constraints.
--
--   * @v :: ⋆@ the type of unification variables
--
--   * @t :: ⋆→⋆@ the type of object language types parametrized by
--     the representation of unification variables.
--
--   * @y :: ⋆@ the type of constraint-scheme variables that are introduced during the witness construction phase.
--
--   * @a :: *@ the type of the witness constructed when the constraint is solved.
-- 
data Constraint (k :: * -> *) (x :: *) (v :: *) (t :: * -> *) (y :: *) (a :: *) where
  -- | @Unify t1 t2@ is the constraint @t₁ ≟ t₂@. The witness is the unit.
  Unify :: t v -> t v -> Constraint k x v t y ()
  -- | @Exist (\v -> C)@ is the constraint @∃α.C@. The witness is the
  -- pair @(τ, a)@ of the type @τ@ that unified with @α@ together with
  -- the witness @a@ for @C@.
  Exist :: (v -> k a) -> Constraint k x v t y (t v, a)
  -- | @CDef t (\x -> C)@ is the constraint @def x = τ in C@ which
  -- introduces the constraint scheme @α. α ≟ τ@ (where α is fresh in
  -- τ) in the constraint @C@.  That is every occurrence @x τ′@ must
  -- unify @τ ≟ τ′@.  The witness is @λy.a@ where @a[y]@ is the
  -- witness for @C[x]@
  CDef :: t v -> (x -> k a) -> Constraint k x v t y (y -> a)
  -- | @CLet (\v -> C1) (\x -> C2)@ is the constraint @let x = α.C₁ in
  -- C₂@ which introduces the constraint scheme @α.C₁@ in the
  -- constraint @C₂@.  That is, at every occurrence @x τ′@ must
  -- satisfy @C₁[τ′/α]@.  The witness is the triple @(All n (λ
  -- αs. (τ₁, All k (λ βs . w₁))), λy. w₂)@ where ∀αs.τ₁ is the
  -- "decoded type scheme" for the constraint α.C₁; λαsβs.w₁ is the
  -- witness for α.C₁ (note that it may have more free unification
  -- variables than τ₁); and @λy.w₂@ is the witness for @C₂[x]@
  CLet :: (v -> k c1) -> (x -> k c2) -> Constraint k x v t y (All v (t v, All v c1), (y -> c2))

-- | Type @All a b@ is the n-ary simultanteous binder for n variables of type @a@ scoping over object @b@.
-- for example type schemes ∀α₁…αₙ.τ  are encoded as @All n f@ where @f [α₁,…,αₙ] = τ@
data All a b = All Int ([a] -> b)

type CG x v t y = Constraint (ConstraintGen x v t y) x v t y

-- | The constraint generation applicative functor. It is the free applicative functor over
-- @'Constraint' (ConstraintGen x v t y) x v t y@
newtype ConstraintGen x v t y a = ConstraintGen {unConstraintGen :: Ap (CG x v t y) a }
  deriving (Functor, Applicative)

-- | The type class of constraint generating applicative functors
-- without definitions and let bindings.
-- Note that constraint construction has no notion of failure.
class Applicative u => ConstraintGenerating u where
  -- | Associated type of unification variables for @u@.
  type UVar u :: *
  -- | Associated type of the unification terms (that is, the types of the object language)
  type UTerm u :: *
  -- | The trivial constraint that is always satisfied
  tt :: u ()
  -- | The conjunction of two constraints
  (~&&~) :: u a -> u b -> u (a,b)
  -- | The constraint @∃α.C@
  exist :: (UVar u -> u a) -> u (UTerm u, a)
  -- | The constraint @t₁ ≟ t₂@ that unifies the types
  (~?~) :: UTerm u -> UTerm u -> u ()

-- | The type class of constraint generating applicative functors with definitions and let bindings.
class ConstraintGenerating u => HindleyMilner u where
  type SchemeVar u :: *
  type WitnessVar u :: *
  cdef :: UTerm u -> (SchemeVar u -> u a) -> u (WitnessVar u -> a)
  clet :: (UVar u -> u c1) -> (SchemeVar u -> u c2) -> u (All (UVar u) (UTerm u, All (UVar u) c1), (WitnessVar u -> c2))

-- | The class witnessing the injection of @u@ into @t@ where @u@ are
-- unification variables, and @t@ is the syntax of unification terms
-- (that is, the object language types).
class HasUVar u t where
  injUVar :: u -> t

instance ConstraintGenerating (ConstraintGen x v t y) where
  type UVar (ConstraintGen x v t y) = v
  type UTerm (ConstraintGen x v t y) = t v
  tt = pure ()
  c1 ~&&~ c2 = ConstraintGen ((,) <$> unConstraintGen c1 <*> unConstraintGen c2)
  t1 ~?~ t2 = ConstraintGen (liftAp (Unify t1 t2))
  exist f = ConstraintGen (liftAp (Exist f))


