{-# language GADTs #-}
module Language.Small.TC where

import Language.Small.Expr

data Range b a = Range b a 

range :: b -> a -> Range b a
range = Range

data Constraint witness where
  CTrue :: Constraint ()
  CConj :: Constraint w1 -> Constraint w2 -> Constraint (w1, w2)
  CEq :: UnifVar -> UnifVar -> Constraint ()
  CExist :: (Range UnifVar (Constraint w)) -> Constraint (UnifVar, Type, w)
  CInstance :: Var -> UnifVar -> Constraint [Type]
  CDef :: Var -> UnifVar -> Constraint w -> Constraint w 
  CLet :: (Range UnifVar (Constraint w1)) -> Range Var (Constraint w2) -> Constraint (TypeScheme, (Range [TyVar] w1), w2)

data Constrained m a where
  Constrained ::  (Constraint w) ->  (w -> m a) -> Constrained m a


instance Functor m => Functor (Constrained m) where
  fmap f (Constrained rc k) = Constrained rc (fmap f . k)
  
instance Applicative m => Applicative (Constrained m) where
  pure x = Constrained CTrue (\() -> pure x)
  (Constrained rc1 kf) <*> (Constrained rc2 kx) =
    Constrained (CConj rc1 rc2) (\(w1, w2) -> kf w1 <*> kx w2)
  (Constrained rc1 kx) <* (Constrained rc2 _) = Constrained (CConj rc1 rc2) (kx . fst)
  (Constrained rc1 _) *> (Constrained rc2 ky) = Constrained (CConj rc1 rc2) (ky . snd)

(~~) :: Applicative m => UnifVar -> UnifVar -> Constrained m ()
x ~~ y = Constrained (CEq x y) pure

(<&>) :: Applicative m => Constrained m a -> Constrained m b -> Constrained m (a, b)
(Constrained rc1 k1) <&> (Constrained rc2 k2) = Constrained (CConj rc1 rc2) (\(w1, w2) -> (,) <$> k1 w1 <*> k2 w2)

class Monad m => ConstraintGenerator m where
  freshUnifVar :: m UnifVar
  freshStandsFor :: Type -> m UnifVar

class Monad m => ConstraintSolver m

exist_aux :: (ConstraintGenerator g, Monad m) => Type -> (UnifVar -> Constrained m a) -> g (Constrained m (Type, a))
exist_aux t f = do
  v <- freshStandsFor t
  return $ case f v of
             Constrained rc k -> do
               Constrained (CExist (range v rc)) (\(v', t', w) -> do
                                                     a <- k w
                                                     return (t', a))

-- (~~~) :: UnifVar -> Type -> 
  

-- checkExpr :: Monad m => Expr -> Constrained m Expr

