module Data.Constraint.Atomic where

-- the working state of the solver is atomic constraints
-- -- atomic constraints are v₀≐v₁≐…≐vₙ≐t (AUnify) or True ([]) or C₁∧C₂ (C1 ++ C2) or ∃α.C (AExist λa.C)
data Constraint t v = Unify v [v] (t v) | Exist (v -> [Constraint t v])
