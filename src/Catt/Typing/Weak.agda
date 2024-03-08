open import Catt.Typing.Rule

module Catt.Typing.Weak (ops : Op) where

open import Catt.Prelude

Weak-Rules : RuleSet
Weak-Rules r = ⊥

open import Catt.Typing ops Weak-Rules

weak-wk : WkCond Weak-Rules
weak-wk A ()

weak-susp : SuspCond Weak-Rules
weak-susp ()

weak-sub : SubCond ops Weak-Rules
weak-sub Γ σ ()

open Tame

weak-tame : (tame : TameOp ops) → Tame ops Weak-Rules
weak-tame tame .tame-op = tame
weak-tame tame .wk-cond = weak-wk
weak-tame tame .susp-cond = weak-susp
weak-tame tame .sub-cond = weak-sub

weak-conv : ConvCond ops Weak-Rules
weak-conv ()

weak-supp : SupportCond ops Weak-Rules
weak-supp ()
