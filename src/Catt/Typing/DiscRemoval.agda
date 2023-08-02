open import Catt.Typing.Base

module Catt.Typing.DiscRemoval {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties

open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule
open import Catt.Tree.Label.Typing rule

open import Catt.Typing.DiscRemoval.Base public

open Rule

HasDiscRemoval : Set
HasDiscRemoval = ∀ {m n}
               → .⦃ NonZero n ⦄
               → {Γ : Ctx m}
               → {σ : Sub (disc-size n) m ⋆}
               → {A : Ty m}
               → Typing-Tm Γ (disc-term n σ) A
               → disc-term n σ ≈[ Γ ]tm 0V [ σ ]tm

HasDiscRemoval-STm : Set
HasDiscRemoval-STm = ∀ {m n}
               → {Γ : Ctx m}
               → {X : MaybeTree m}
               → (S : Tree n)
               → .⦃ _ : is-linear S ⦄
               → .⦃ NonZero (tree-dim S) ⦄
               → (L : Label X S)
               → Typing-Label Γ (L ,, S⋆)
               → (unbiased-comp (tree-dim S) S >>= L ,, S⋆) ≈[ Γ ]stm L (is-linear-max-path S)

module Conditions (dr : HasDiscRemoval) where
  open import Catt.Typing.Rule rule

  lift-rule : .⦃ NonZero n ⦄
             → {σ : Sub (disc-size n) m ⋆}
             → LiftRule (DiscRemoval Γ σ)
  lift-rule {n = n} {σ = σ} tty = begin
    disc-term n (lift-sub σ)
      ≈⟨ dr tty ⟩
    0V [ lift-sub σ ]tm
      ≈⟨ reflexive≈tm (apply-lifted-sub-tm-≃ 0V σ) ⟩
    lift-tm (0V [ σ ]tm) ∎
    where
      open Reasoning (tm-setoid-≈ _)

  susp-rule : .⦃ NonZero n ⦄
            → {σ : Sub (disc-size n) m ⋆}
            → SuspRule (DiscRemoval Γ σ)
  susp-rule {n = n} {σ = σ} tty = begin
    susp-tm (disc-term n σ)
      ≈⟨ reflexive≈tm (disc-term-susp n σ) ⟩
    disc-term (suc n) (susp-sub σ)
      ≈⟨ dr (transport-typing tty (disc-term-susp n σ)) ⟩
    0V [ susp-sub σ ]tm
      ≈˘⟨ reflexive≈tm (susp-functorial-tm σ 0V) ⟩
    susp-tm (0V [ σ ]tm) ∎
    where
      open Reasoning (tm-setoid-≈ _)

  sub-rule : .⦃ NonZero n ⦄
           → {τ : Sub (disc-size n) m ⋆}
           → SubRule (DiscRemoval Γ τ)
  sub-rule {n = n} {τ = τ} {σ = σ} σty tty = begin
    disc-term n (σ ● τ)
      ≈⟨ dr tty ⟩
    0V [ σ ● τ ]tm
      ≈⟨ reflexive≈tm (assoc-tm σ τ 0V) ⟩
    0V [ τ ]tm [ σ ]tm ∎
    where
      open Reasoning (tm-setoid-≈ _)
