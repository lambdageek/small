module Main where

-- import Language.Small

-- e =
--   let x = s2n "x"
--   in App (Var x) (Var x)

-- main :: IO ()
-- main = putStrLn (show e)

import Algo.DebPho
import Control.Applicative.Unify (ConstraintGen, HasUVar (..))
import Algo.Elaborate
import Language.Pho
import Language.Monotype (Type (..))

main :: IO ()
main = do
  print (debruijn ex1)
  putStrLn (showTerm ex1)
  let c :: ConstraintGen U (Type ()) ()
      c = hasType ex1 (injUVar $ U "x")
  putStrLn $ showConstraint c
