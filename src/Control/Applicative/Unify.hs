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

import Control.Applicative.Free.Final (Ap(..), liftAp, runAp, hoistAp)

-- Hindley-Milner Elaboration in the Applicative Style
-- note that the constraint generation applicative functor is just the free applicative
-- over the two base operations of term (ie type) equality constraints t₁≐t₂ and
-- fresh unification variable selection.

-- | @Constraint k x v t c y a@ is a PHOAS-representation constraint algebra where
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
--   * @t :: ⋆@ the type of object language types.
--
--   * @c :: ⋆@ the type of type variables that are introduced during the witness construction phase.
-- 
--   * @y :: ⋆@ the type of constraint-scheme variables that are introduced during the witness construction phase.
--
--   * @a :: *@ the type of the witness constructed when the constraint is solved.
-- 
data Constraint (k :: * -> *) (x :: *) (v :: *) t (c :: *) (y :: *) (a :: *) where
  -- | @Unify t1 t2@ is the constraint @t₁ ≟ t₂@. The witness is the unit.
  Unify :: t -> t -> Constraint k x v t c y ()
  -- | @Exist (\v -> C)@ is the constraint @∃u.C@. The witness is the
  -- pair @(τ, a)@ of the type @τ@ that unified with @u@ together with
  -- the witness @a@ for @C@.
  Exist :: (v -> k a) -> Constraint k x v t c y (t, a)
  -- | @CDef t (\x -> C)@ is the constraint @def x = τ in C@ which
  -- introduces the constraint scheme @α. α ≟ τ@ (where α is fresh in
  -- τ) in the constraint @C@.  That is every occurrence @x τ′@ must
  -- unify @τ ≟ τ′@.  The witness is @λy.a@ where @a[y]@ is the
  -- witness for @C[x]@
  CDef :: t -> (x -> k a) -> Constraint k x v t c y (y -> a)
  -- | @CLet (\v -> C1) (\x -> C2)@ is the constraint @let x = α.C₁ in
  -- C₂@ which introduces the constraint scheme @α.C₁@ in the
  -- constraint @C₂@.  That is, at every occurrence @x τ′@ must
  -- satisfy @C₁[τ′/α]@.  The witness is the triple @(All n (λ
  -- αs. (τ₁, All k (λ βs . w₁))), λy. w₂)@ where ∀αs.τ₁ is the
  -- "decoded type scheme" for the constraint α.C₁; λαsβs.w₁ is the
  -- witness for α.C₁ (note that it may have more free unification
  -- variables than τ₁); and @λy.w₂@ is the witness for @C₂[x]@
  --
  -- As a constraint "let x=α.C₁[α] in C₂{x}" can be simplified to "∃u.C₁[u/α] ∧ C₂{α.C₁[α]/x}" where
  --   C{α.D[α]/x} is defined by cases on C as
  --     True {α.D[α]/x}       = True
  --     C₁{x}∧C₂{x} {α.D[α]/x} = C₁{α.D[α]/x} ∧ C₂{α.D[α]/x}
  --     x τ {α.D[α]/x}        = D[τ/α]
  --     y τ {α.D[α]/x}        = y τ       when x≠y
  --     (let y=β.C₁[β]{x} in C₂{y}{x}) {α.D[α]/x} = let y = β.C₁[β]{α.D[α]/x} in C₂{y}{α.D[α]/x}
  --                                       where y and β are each fresh in α.D[α]
  --
  -- But as a constraint with a witness it is primitive because we
  -- need to bake generalization into the witness.
  CLet :: (v -> k c1) -> (x -> k c2) -> Constraint k x v t c y (All c (t, All c c1), (y -> c2))
  -- | Constraint scheme instantiation.  If @x = α.C@ is a constraint
  -- scheme, the instantiation @x τ@ is a constraint @C[τ/α]@ where
  -- every occurence of α in C has been replaced by the given type.
  CInst :: x -> t -> Constraint k x v t c y ([t])

-- | Type @All c a@ is the n-ary simultanteous binder for n variables of type @c@ scoping over object @a@.
-- for example type schemes ∀α₁…αₙ.τ  are encoded as @All n f@ where @f [α₁,…,αₙ] = τ@
data All c a = All Int ([c] -> a)

type CG x v t c y = Constraint (ConstraintGen x v t c y) x v t c y

-- | The constraint generation applicative functor. It is the free applicative functor over
-- @'Constraint' (ConstraintGen x b v t c y) x b v t c y@
newtype ConstraintGen x v t c y a = ConstraintGen {unConstraintGen :: Ap (CG x v t c y) a }
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
  type WitnessTyVar u :: *
  cdef :: UTerm u -> (SchemeVar u -> u a) -> u (WitnessVar u -> a)
  clet :: (UVar u -> u c1) -> (SchemeVar u -> u c2) -> u (All (WitnessTyVar u) (UTerm u, All (WitnessTyVar u) c1), (WitnessVar u -> c2))
  cinst :: SchemeVar u -> UTerm u -> u ([UTerm u])

-- | The class witnessing the injection of @v@ into @t@ where @v@ are
-- unification variables, and @t@ is the syntax of unification terms
-- (that is, the object language types).
class HasUVar v t where
  injUVar :: v -> t

instance ConstraintGenerating (ConstraintGen x v t c y) where
  type UVar (ConstraintGen x v t c y) = v
  type UTerm (ConstraintGen x v t c y) = t
  tt = pure ()
  c1 ~&&~ c2 = ConstraintGen ((,) <$> unConstraintGen c1 <*> unConstraintGen c2)
  t1 ~?~ t2 = mkCG (Unify t1 t2)
  exist f = mkCG (Exist f)

mkCG :: CG x v t c y a -> ConstraintGen x v t c y a
mkCG = ConstraintGen . liftAp

instance HindleyMilner (ConstraintGen x v t c y) where
  type SchemeVar (ConstraintGen x v t c y) = x
  type WitnessVar (ConstraintGen x v t c y) = y
  type WitnessTyVar (ConstraintGen x v t c y) = c
  cdef t f = mkCG (CDef t f)
  clet c1 c2 = mkCG (CLet c1 c2)
  cinst x t = mkCG (CInst x t)

type ConstraintGen1v x t c y a = forall v . v -> ConstraintGen x v t c y a
