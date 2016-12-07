{-# language GADTs, TypeFamilies, RankNTypes, GeneralizedNewtypeDeriving, TypeOperators, DataKinds, PolyKinds #-}
module Control.Applicative.Unify where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List (intercalate)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Traversable (foldMapDefault)

-- data Ap f a where
--   Pure :: a -> Ap f a
--   Ap :: f a -> Ap f (a -> b) -> Ap f b

-- runAp :: Applicative g => Ap f a -> (forall x . f x -> g x) -> g a
-- runAp (Pure x) _ = pure x
-- runAp (Ap fa afab) phi = (\x f -> f x) <$> phi fa <*> runAp afab phi

-- liftAp :: f a -> Ap f a
-- liftAp fa = Ap fa (Pure id)

-- instance Functor (Ap f) where
--   fmap h (Pure x) = Pure (h x)
--   fmap h (Ap fa apfb) = Ap fa (fmap (h .) apfb)

-- instance Applicative (Ap f) where
--   pure = Pure
--   Pure f <*> p = fmap f p
--   Ap f p <*> q = Ap f ((\g -> flip g) <$> p <*> q)

data Ap f a = Ap { runAp :: forall g . Applicative g => (forall x . f x -> g x) -> g a }
  
liftAp :: f a -> Ap f a
liftAp fa = Ap (\phi -> phi fa)

instance Functor (Ap f) where
  fmap h (Ap kgc) = Ap (\phi -> fmap h (kgc phi))

instance Applicative (Ap f) where
  pure x = Ap (const (pure x))
  (Ap kf) <*> (Ap kx) = Ap (\phi -> kf phi <*> kx phi)

retractAp :: Applicative f => Ap f a -> f a
retractAp (Ap ap) = ap id


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

data Type v u =
  BaseT
  | VarT v
  | UVT u
  | ArrT (Type v u) (Type v u)
    deriving (Eq)

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

data TypeScheme v u = TSZ (Type v u) | TSS (v -> TypeScheme v u)

instance (Show v, Show u) => Show (Type v u) where
  show BaseT = "b"
  show (VarT a) = show a
  show (UVT x) = show x
  show (ArrT t1 t2) = "arr(" ++ show t1 ++ "; " ++ show t2 ++ ")"

generalize' :: Type v v -> Type v a
generalize' t =
  case t of
    BaseT -> BaseT
    VarT v -> VarT v
    UVT v -> VarT v
    ArrT t1 t2 -> ArrT (generalize' t1) (generalize' t2)

freeUVars :: Ord u => Type v u -> [u]
freeUVars = S.toList . foldMap (S.singleton) 

data Term' x =
  VarM x
  | LamM (x -> Term' x)
  | AppM (Term' x) (Term' x)
  | LetM (Term' x) (x -> Term' x)

type Term = forall t . Term' t

showTerm' :: Term' String -> Reader [String] String
showTerm' m =
  case m of
    VarM s -> return s
    AppM m1 m2 -> do
      s1 <- showTerm' m1
      s2 <- showTerm' m2
      return $ "app(" ++ s1 ++ "; " ++ s2 ++ ")"
    LamM f -> do
      (x:xs) <- ask
      s <- local (const xs) $ showTerm' (f x)
      return $ "lam(" ++ x ++ "." ++ s ++ ")"
    LetM m1 f -> do
      s1 <- showTerm' m1
      (x:xs) <- ask
      s2 <- local (const xs) $ showTerm' (f x)
      return $ "let(" ++ s1 ++ "; " ++ x ++ "." ++ s2 ++ ")"

showTerm :: Term -> String
showTerm m = runReader (showTerm' m) (varNames ["x", "y", "z", "i", "j", "k", "a", "b", "c", "d", "e", "f"])

varNames :: [String] -> [String]
varNames ptn = ptn ++ go 1 ptn 
  where
    go :: Int -> [String] -> [String]
    go n (x:xs) = (x ++ show n) : go n xs
    go n [] = (go $! n + 1) ptn

ex0 :: Term
ex0 = LamM $ \x -> VarM x

ex1 :: Term
ex1 = LetM (LamM $ \x -> VarM x) $ \f -> LamM $ \x -> AppM (VarM f) (AppM (VarM f) (VarM x))

ex2 :: Term
ex2 = LamM $ \x -> LamM $ \y -> AppM (VarM y) (LamM $ \_z -> (VarM x))


-- | An abbreviation "let x=α.C₁[α] in C₂{x}" means "∃α.C₁[α] ∧ C₂{α.C₁[α]/x}" where
--   C{α.D[α]/x} is defined by cases on C as
--     True {α.D[α]/x}       = True
--     C₁{x}∧C₂{x} {α.D[α]/x} = C₁{α.D[α]/x} ∧ C₂{α.D[α]/x}
--     x τ {α.D[α]/x}        = D[τ/α]
--     y τ {α.D[α]/x}        = y τ       when x≠y
--     (let y=β.C₁[β]{x} in C₂{y}{x}) {α.D[α]/x} = let y = β.C₁[β]{α.D[α]/x} in C₂{y}{α.D[α]/x} where y and β are each fresh in α.D[α]
letC :: (ConstraintGenerating m, UVar m ~ u, UTerm m ~ t, HasUVar u t) => Schematic m a -> (Schematic m a -> m b) -> m ((UTerm m, a), b)
letC x body = exist (\a -> x (injUVar a)) ~&&~ body x

-- instantiation of a constraint-scheme on a type.
instC :: Schematic m a -> UTerm m -> m a
instC x w = x w

hasType' :: (ConstraintGenerating m, UVar m ~ u, UTerm m ~ Type v u) => Term' (Schematic m ()) -> UTerm m -> m ()
hasType' m w =
  case m of
    VarM x -> instC x w
    AppM m1 m2 ->
      exist (\u -> hasType' m1 (ArrT (UVT u) w) ~&&~ hasType' m2 (UVT u)) <&> (\_ -> ())
    LamM f ->
      exist (\dom -> exist $ \cod ->
                w ~?~ (ArrT (UVT dom) (UVT cod))
                ~&&~
                letC (~?~ UVT dom) (\x -> hasType' (f x) (UVT cod)))
      <&> const ()
    LetM m1 f ->
      letC (hasType' m1) (\x -> hasType' (f x) w) <&> const ()
      
hasType :: Term -> Type v u -> ConstraintGen u (Type v) ()
hasType m w = hasType' m w

newtype U = U String

instance Show U where
  show (U s) = s

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

instance (Monad m, Monoid r) => Applicative (Effect r m) where
  pure _ = effect (return mempty)
  ef <*> ex = effect (mappend <$> runEffect ef <*> runEffect ex)

collectSimpleConstraints' :: ConstraintGen u t a -> Effect () (Writer [SimpleConstraint t u]) a
collectSimpleConstraints' (ConstraintGen cg) = runAp cg phi
  where
    phi :: Constraint (ConstraintGen u t) u t a -> Effect () (Writer [SimpleConstraint t u]) a
    phi c =
      case c of
        Unify t1 t2 -> effect $ tell [SUnify t1 t2]
        Exist f -> effect $ tell [SExist $ \v -> collectSimpleConstraints (f v)]

collectSimpleConstraints :: ConstraintGen u t a -> [SimpleConstraint t u]
collectSimpleConstraints = snd . runWriter . runEffect . collectSimpleConstraints'

showConstraint :: (Show (t U)) => ConstraintGen U t a -> String
showConstraint = showSimpleConstraints . collectSimpleConstraints

showSimpleConstraints :: (Show (t U)) => [SimpleConstraint t U] -> String
showSimpleConstraints ss = runReader (showSimpleConstraints' ss) (map U $ varNames ["u", "v", "w"])

showSimpleConstraints' :: (Show (t U)) => [SimpleConstraint t U] -> Reader [U] String
showSimpleConstraints' ss = do
  strs <- mapM showSimpleConstraint ss
  return (intercalate " & " strs)

showSimpleConstraint :: (Show (t U)) => SimpleConstraint t U -> Reader [U] String
showSimpleConstraint s =
  case s of
    SUnify t1 t2 -> return (show t1 ++ " =?= " ++ show t2)
    SExist f -> do
      (u:us) <- ask
      c <- local (const us) $ showSimpleConstraints' (f u)
      return $ "?(" ++ show u ++ "." ++ c ++ ")"
