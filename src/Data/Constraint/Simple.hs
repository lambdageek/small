module Data.Constraint.Simple where

-- simple constraints are True ([]), C₁∧C₂ (C1 ++ C2),
-- ∃α.C (SExist (λa.C)), or t₁≐t₂ (SUnify t1 t2)
data Constraint t v = Unify (t v) (t v) | Exist (v -> [Constraint t v])

