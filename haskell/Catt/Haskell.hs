module Catt.Haskell where

data Test = Zero
          | Succ Test

unwrap :: Test -> Test
unwrap (Succ x) = x

