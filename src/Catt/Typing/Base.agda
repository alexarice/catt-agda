module Catt.Typing.Base where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Tree.Label

record Rule : Set₁ where
  field
    len : ℕ
    tgtCtx : Ctx len
    lhs : Tm len
    rhs : Tm len

record SRule : Set₁ where
  field
    len : ℕ
    tgtCtx : Ctx len
    lhs : STm (Other len)
    rhs : STm (Other len)
