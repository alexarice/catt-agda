module Catt.Typing.Base where

open import Catt.Prelude
open import Catt.Syntax

record Rule : Set₁ where
  field
    Args : Set
    len : (a : Args) → ℕ
    tgtCtx : (a : Args) → Ctx (len a)
    lhs : (a : Args) → Tm (len a)
    rhs : (a : Args) → Tm (len a)
