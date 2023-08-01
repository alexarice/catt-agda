module Catt.Typing.DiscRemoval.Base where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Discs
open import Catt.Typing.Rule

open Rule

DiscRemoval : (Γ : Ctx m)
            → (σ : Sub (disc-size n) m ⋆) → Rule
DiscRemoval Γ σ .len = _
DiscRemoval Γ σ .tgtCtx = Γ
DiscRemoval Γ σ .lhs = disc-term _ σ
DiscRemoval Γ σ .rhs = 0V [ σ ]tm
