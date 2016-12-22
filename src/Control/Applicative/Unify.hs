{-# language GADTs, TypeFamilies, RankNTypes, GeneralizedNewtypeDeriving, TypeOperators, DataKinds, PolyKinds #-}
module Control.Applicative.Unify (
  -- * Constraint Generating Applicative functor
  ConstraintGenerating (..)
  , HasUVar (..)
  , (<&>)
  -- * Free Constraint Generating Applicative functor
  , Constraint (..)
  , CG
  , ConstraintGen (..)
  -- * Simple constraints
  , Schematic
  , SimpleConstraint (..)
  -- * re-export Ap from free
  , module Control.Applicative.Free.Final
  ) where

import Control.Applicative.Free.Final (Ap(..), liftAp, runAp)

-- Hindley-Milner Elaboration in the Applicative Style
-- note that the constraint generation applicative functor is just the free applicative
-- over the two base operations of term (ie type) equality constraints t₁≐t₂ and
-- fresh unification variable selection.

data Constraint k v t a where
  Unify :: t v -> t v -> Constraint k v t ()
  Exist :: (v -> k a) -> Constraint k v t (t v, a)

-- data Constraint' v t a where
--   TT :: Constraint' v t ()
--   And :: Constraint' v t a -> Constraint' v t b -> Constraint' v t (a,b)
--   Unify' :: t v -> t v -> Constraint' v t ()
--   Exist' :: (v -> Constraint' v t a) -> Constraint' v t (t v, a)
--   FMap :: (a -> b) -> Constraint' t v a -> Constraint' t v b

-- instance Functor (Constraint' v t) where
--   fmap f c =
--     case c of
--       FMap g c -> FMap (f . g) c
--       _ -> FMap f c

-- instance Applicative (Constraint' v t) where
--   pure x = FMap (const x) TT
--   cf <*> cx = FMap (uncurry ($)) (And cf cx)
      

type CG v t = Constraint (ConstraintGen v t) v t

newtype ConstraintGen v t a = ConstraintGen {unConstraintGen :: Ap (CG v t) a }
  deriving (Functor, Applicative)

class Applicative u => ConstraintGenerating u where
  type UVar u :: *
  type UTerm u :: *
  tt :: u ()
  (~&&~) :: u a -> u b -> u (a,b)
  exist :: (UVar u -> u a) -> u (UTerm u, a)
  (~?~) :: UTerm u -> UTerm u -> u ()

class HasUVar u t where
  injUVar :: u -> t

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)

instance ConstraintGenerating (ConstraintGen v t) where
  type UVar (ConstraintGen v t) = v
  type UTerm (ConstraintGen v t) = t v
  tt = pure ()
  c1 ~&&~ c2 = ConstraintGen ((,) <$> unConstraintGen c1 <*> unConstraintGen c2)
  t1 ~?~ t2 = ConstraintGen (liftAp (Unify t1 t2))
  exist f = ConstraintGen (liftAp (Exist f))


-- | A schematic constraint with a type hole.  Lambda-bound term
-- variables will be schemes that unify the expected type of the
-- variable with a single given type.  Let-bound term variables will
-- be schemes that capture the entire set of constraints generated for
-- the term being bound which will be copied anew into place wherever
-- the let-bound variable occurs.  This is what allows let-bound vars
-- to be instantiated at different types at each occurrence.
--
-- To explain Pottier's λβ.C meta-notation and the let-constraint "let
-- x=λβ.C₁ in C₂" and the application-constraint "x τ" we need to talk about
-- abstracting over terms, not just 
type Schematic m a = UTerm m ->  m a --  Type v u -> ConstraintGen u (Type v) a

-- simple constraints are True ([]), C₁∧C₂ (C1 ++ C2),
-- ∃α.C (SExist (λa.C)), or t₁≐t₂ (SUnify t1 t2)
data SimpleConstraint t v = SUnify (t v) (t v) | SExist (v -> [SimpleConstraint t v])

-- the working state of the solver is atomic constraints
-- -- atomic constraints are v₀≐v₁≐…≐vₙ≐t (AUnify) or True ([]) or C₁∧C₂ (C1 ++ C2) or ∃α.C (AExist λa.C)
-- data AtomicConstraint t v = AUnify v [v] (t v) | AExist (v -> [AtomicConstraint t v])

