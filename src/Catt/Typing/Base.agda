module Catt.Typing.Base where

open import Catt.Prelude
open import Catt.Syntax

record Rule : Set where
  field
    len : ℕ
    tgtCtx : Ctx len
    lhs : Tm len
    rhs : Tm len

RuleSet : Set₁
RuleSet = Rule → Set

_∈r_ : Rule → RuleSet → Set
r ∈r rules = Wrap (λ r rules → rules r) r rules
