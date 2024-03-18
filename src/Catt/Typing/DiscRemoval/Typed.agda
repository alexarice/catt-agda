open import Catt.Typing.Rule

module Catt.Typing.DiscRemoval.Typed (ops : Op)
                                     (standard-op : StandardOp ops)
                                     (rules : RuleSet)
                                     (wk-cond : WkCond rules) where

open import Catt.Prelude

open import Catt.Typing.DiscRemoval.Rule

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Globular.Typing ops rules
open import Catt.Discs.Typing ops standard-op rules wk-cond

dr-pres : PresCond′ ops rules DiscRemovalSet
dr-pres [ DR {n = n} Γ σ ] tty with coh-sub-ty tty
... | TyExt σty sty = TyConv sty (Ty-unique (disc-term-Ty n (TyExt σty sty)) tty)
