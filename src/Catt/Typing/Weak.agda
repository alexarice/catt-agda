module Catt.Typing.Weak where

open import Catt.Prelude
open import Catt.Typing.Rule

Weak-Rules : RuleSet
Weak-Rules r = ⊥

open import Catt.Typing Weak-Rules public

open import Catt.Typing.Rule.Typed Weak-Rules

weak-lift : LiftCond Weak-Rules
weak-lift A ()

weak-susp : SuspCond Weak-Rules
weak-susp ()

weak-sub : SubCond Weak-Rules
weak-sub Γ σ ()

open Tame

weak-tame : Tame Weak-Rules
weak-tame .lift-cond = weak-lift
weak-tame .susp-cond = weak-susp
weak-tame .sub-cond = weak-sub

weak-conv : ConvCond Weak-Rules
weak-conv ()

weak-supp : SupportCond Weak-Rules
weak-supp ()
