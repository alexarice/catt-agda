open import Catt.Typing.Rule

module Catt.Support.Typing (rules : RuleSet) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Support

rulesWithSupp : RuleSet
rulesWithSupp r = rules r × SuppTm tgtCtx lhs ≡ SuppTm tgtCtx rhs
  where
    open Rule r

-- module _ where
--   open import Catt.Typing rulesWithSupp
--   open ≡-Reasoning
--   rulesWithSuppLift : (i : rulesWithSuppIndex) → LiftRule rule (rulesWithSupp i) → LiftRule rulesWithSupp (rulesWithSupp i)
--   rulesWithSuppLift (i ,, supp) r tty = {!!}
