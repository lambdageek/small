module Language.Deb where

data Expr =
  VarE Int
  | LamE Expr
  | AppE Expr Expr
  | LetE Expr Expr

instance Show Expr where
  show e =
    case e of
      VarE n -> show n
      LamE e -> "lam(." ++ show e ++ ")"
      AppE e1 e2 -> "app(" ++ show e1 ++ "; " ++ show e2 ++ ")"
      LetE e e' -> "let(" ++ show e ++ "; ." ++ show e' ++ ")"
