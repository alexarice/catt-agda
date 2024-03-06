open import Catt.Typing.Rule

module Catt.Typing.DiscRemoval.Typed (ops : Op)
                                     (standard-op : StandardOp ops)
                                     (rules : RuleSet)
                                     (lift-cond : LiftCond rules) where

open import Catt.Prelude

open import Catt.Typing.DiscRemoval.Rule

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Globular.Typing ops rules
open import Catt.Discs.Typing ops standard-op rules lift-cond

dr-conv : ConvCond′ ops rules DiscRemovalSet
dr-conv [ DR {n = n} Γ σ ] tty with coh-sub-ty tty
... | TyExt σty sty = TyConv sty (Ty-unique (disc-term-Ty n (TyExt σty sty)) tty)
