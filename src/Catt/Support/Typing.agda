open import Catt.Typing.Rule

module Catt.Support.Typing {index : Set}
                           (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Support

open Rule

rulesWithSuppIndex : Set
rulesWithSuppIndex = Σ[ i ∈ index ] SuppTm (rule i .tgtCtx) (rule i .lhs) ≡ SuppTm (rule i .tgtCtx) (rule i .rhs)

rulesWithSupp : rulesWithSuppIndex → Rule
rulesWithSupp (i ,, _) = rule i

-- module _ where
--   open import Catt.Typing rulesWithSupp
--   open ≡-Reasoning
--   rulesWithSuppLift : (i : rulesWithSuppIndex) → LiftRule rule (rulesWithSupp i) → LiftRule rulesWithSupp (rulesWithSupp i)
--   rulesWithSuppLift (i ,, supp) r tty = {!!}
