module Catt.Typing.Base where

open import Catt.Prelude
open import Catt.Syntax

record Rule : Set₁ where
  field
    len : ℕ
    tgtCtx : Ctx len
    lhs : Tm len
    rhs : Tm len
