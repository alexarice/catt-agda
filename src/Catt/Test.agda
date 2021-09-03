module Catt.Test where

postulate
  A B C : Set
  f : ⦃ A ⦄ → B
  g : .⦃ B ⦄ → C

test : .⦃ A ⦄ → C
test = let
  instance x = f
  in g
