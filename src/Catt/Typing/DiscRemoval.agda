open import Catt.Typing.Base

module Catt.Typing.DiscRemoval {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Support
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Path
open import Catt.Typing.Properties.Base rule
open import Catt.Suspension
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Discs.Properties

HasDiscRemoval : Set
HasDiscRemoval = ∀ {m n}
               → .⦃ NonZero n ⦄
               → {Γ : Ctx m}
               → {σ : Sub (disc-size n) m ⋆}
               → Typing-Sub (Disc n) Γ σ
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

  lift-rule : .⦃ NonZero n ⦄
            → Typing-Sub (Disc n) (Γ , A) (liftSub σ)
            → liftTerm (disc-term n σ) ≈[ Γ , A ]tm liftTerm (0V [ σ ]tm)
  lift-rule {n = n} {σ = σ} σty = begin
    disc-term n (liftSub σ)
      ≈⟨ dr σty ⟩
    0V [ liftSub σ ]tm
      ≈⟨ reflexive≈tm (apply-lifted-sub-tm-≃ 0V σ) ⟩
    liftTerm (0V [ σ ]tm) ∎
    where
      open Reasoning (tm-setoid-≈ _)

  susp-rule : Typing-Sub (Disc (suc n)) (suspCtx Γ) (suspSub σ)
            → suspTm (disc-term n σ) ≈[ suspCtx Γ ]tm suspTm (0V [ σ ]tm)
  susp-rule {n = n} {σ = σ} σty = begin
    suspTm (disc-term n σ)
      ≈⟨ reflexive≈tm (Coh≃ (disc-susp n) (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n))) refl≃s) ⟩
    disc-term (suc n) (suspSub σ)
      ≈⟨ dr σty ⟩
    0V [ suspSub σ ]tm
      ≈˘⟨ reflexive≈tm (susp-functorial-tm σ 0V) ⟩
    suspTm (0V [ σ ]tm) ∎
    where
      open Reasoning (tm-setoid-≈ _)

  sub-rule : ⦃ NonZero n ⦄
           → {σ : Sub (disc-size n) m ⋆}
           → {τ : Sub m l ⋆}
           → Typing-Sub (Disc n) Δ (τ ● σ)
           → disc-term n σ [ τ ]tm ≈[ Δ ]tm 0V [ σ ]tm [ τ ]tm
  sub-rule {n = n} {σ = σ} {τ = τ} σty = begin
    disc-term n (τ ● σ)
      ≈⟨ dr σty ⟩
    0V [ τ ● σ ]tm
      ≈⟨ reflexive≈tm (assoc-tm τ σ 0V) ⟩
    0V [ σ ]tm [ τ ]tm ∎
    where
      open Reasoning (tm-setoid-≈ _)
