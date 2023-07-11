module Catt.Typing.Rule where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Typing.Base public
open import Catt.Suspension
open import Catt.Support

module _ {index : Set} (rule : index → Rule) (r : Rule) where
  open import Catt.Typing rule
  open Rule r

  LiftRule : Set
  LiftRule = {A : Ty len}
           → {C : Ty len}
           → Typing-Tm (tgtCtx , A) (lift-tm lhs) (lift-ty C)
           → (lift-tm lhs) ≈[ tgtCtx , A ]tm (lift-tm rhs)

  SuspRule : Set
  SuspRule = {C : Ty len}
           → Typing-Tm (susp-ctx tgtCtx) (susp-tm lhs) (susp-ty C)
           → susp-tm lhs ≈[ susp-ctx tgtCtx ]tm susp-tm rhs

  SubRule : Set
  SubRule = ∀ {n}
          → {σ : Sub len n ⋆}
          → {Δ : Ctx n}
          → {C : Ty len}
          → Typing-Sub tgtCtx Δ σ
          → Typing-Tm Δ (lhs [ σ ]tm) (C [ σ ]ty)
          → lhs [ σ ]tm ≈[ Δ ]tm rhs [ σ ]tm

  SupportRule : Set
  SupportRule = {A : Ty len}
              → (tty : Typing-Tm tgtCtx lhs A)
              → SuppTm tgtCtx lhs ≡ SuppTm tgtCtx rhs

  ConvRule : Set
  ConvRule = {A : Ty len}
           → Typing-Tm tgtCtx lhs A
           → Typing-Tm tgtCtx rhs A
