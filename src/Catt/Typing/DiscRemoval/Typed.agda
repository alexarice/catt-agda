open import Catt.Typing.Rule

module Catt.Typing.DiscRemoval.Typed (rules : RuleSet)
                                     (lift-cond : LiftCond rules) where

open import Catt.Prelude

open import Catt.Typing.DiscRemoval.Rule

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules
open import Catt.Globular.Typing rules lift-cond
open import Catt.Discs.Typing rules lift-cond

dr-conv : ConvCond′ rules DiscRemovalSet
dr-conv [ DR {n = n} Γ σ ] tty with coh-sub-ty tty
... | TyExt σty sty = TyConv sty (Ty-unique (disc-term-Ty n (TyExt σty sty)) tty)
