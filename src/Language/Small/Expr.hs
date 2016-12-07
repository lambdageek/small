{-# language DeriveGeneric #-}
module Language.Small.Expr where

import Unbound.Generics.LocallyNameless
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

type FieldId = String

type Var = Name Expr

data Expr =
  Var Var
  | Lam Type (Bind Var Expr)
  | App Expr Expr
  | Path ExprPath
  deriving (Show, Typeable, Generic)

data ExprPath = ExprPath { exprPathMod :: ModulePath
                         , exprPathVal :: FieldId
                         }
  deriving (Show, Typeable, Generic)

type TyVar = Name Type

data UnifVar = Name (UnifVar)
  deriving (Show, Typeable, Generic)

instance Alpha UnifVar

data Type =
  VarT TyVar
  | PathT TypePath
  | AppT Type Type
  | ForallT Kind (Bind TyVar Type)
  | U UnifVar
  deriving (Show, Typeable, Generic)

newtype TypeScheme = TypeScheme (Bind [TyVar] Type) -- all of kind TypeK for now
  deriving (Show, Typeable, Generic)

data Kind = TypeK
  deriving (Show, Typeable, Generic)

data TypePath = TypePath { typePathMod  :: ModulePath
                         , typePathType :: FieldId
                         }
  deriving (Show, Typeable, Generic)

type ModuleVar = Name ModulePath

data ModulePath = MPVar ModuleVar | MPProj ModulePath FieldId
  deriving (Show, Typeable, Generic)

instance Alpha Expr
instance Alpha ExprPath

instance Alpha Type
instance Alpha TypePath

instance Alpha Kind

instance Alpha ModulePath
