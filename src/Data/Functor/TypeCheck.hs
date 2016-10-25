{-# language GADTs, TypeFamilies #-}
module Data.Functor.TypeCheck where

import Control.Monad.Free

type family Variable (fam :: *) :: *

type family Type (fam :: *) :: *

data TypeCheckF fam next where
  LookupVarCtx :: Variable fam -> (Type fam -> next) -> TypeCheckF fam next
  ExtendCtx :: Variable fam -> Type fam -> next -> TypeCheckF fam next

instance Functor (TypeCheckF fam) where
  fmap f (LookupVarCtx x k) = LookupVarCtx x (f . k)
  fmap f (ExtendCtx x ty k) = ExtendCtx x ty (f k)

type FreeTypeCheck fam = Free (TypeCheckF fam)
