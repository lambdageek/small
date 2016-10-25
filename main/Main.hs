module Main where

import Language.Small

e =
  let x = s2n "x"
  in App (Var x) (Var x)

main :: IO ()
main = putStrLn (show e)
