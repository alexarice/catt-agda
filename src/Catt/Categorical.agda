{-# OPTIONS --without-K #-}

module Catt.Categorical where

open import Catt.Syntax
open import Catt.FreeVars
open import Catt.Typing
open import Catt.Bundles
open import Data.Nat
open import Catt.Fin
open import Catt.Vec.Functional
open import Catt.Typing.Properties
open import Catt.Syntax.Equality

private
  variable
    n m : ℕ

id-sub : (n : ℕ) → Sub n n
id-sub n .get f = Var f

id-sub-is-id-ty : (A : Ty n) → A [ id-sub n ]ty ≡ty A
id-sub-is-id-tm : (t : Term n) → t [ id-sub n ]tm ≡tm t
id-sub-is-id-sub-left : (σ : Sub m n) → id-sub m ∘ σ ≡sub σ
id-sub-is-id-sub-right : (σ : Sub m n) → σ ∘ id-sub n ≡sub σ

id-sub-is-id-ty ⋆ = Star≡
id-sub-is-id-ty (t ─⟨ A ⟩⟶ u) = Arr≡ (id-sub-is-id-tm t) (id-sub-is-id-ty A) (id-sub-is-id-tm u)

id-sub-is-id-tm (Var x) = tm-refl
id-sub-is-id-tm (Coh Γ A σ) = Coh≡ ctx-refl ty-refl (id-sub-is-id-sub-left σ)

id-sub-is-id-sub-left σ i = id-sub-is-id-tm (get σ i)

id-sub-is-id-sub-right σ i = tm-refl

-- use more general lemma
id-sub-lemma-ty : (A : Ty n) → liftType A ≡ty A [ front (id-sub (suc n)) ]ty
id-sub-lemma-tm : (t : Term n) → liftTerm t ≡tm t [ front (id-sub (suc n)) ]tm
id-sub-lemma-sub : (σ : Sub m n) → liftSub σ ≡sub front (id-sub (suc m)) ∘ σ

id-sub-lemma-ty ⋆ = Star≡
id-sub-lemma-ty (t ─⟨ A ⟩⟶ u) = Arr≡ (id-sub-lemma-tm t) (id-sub-lemma-ty A) (id-sub-lemma-tm u)

id-sub-lemma-tm (Var x) = tm-refl
id-sub-lemma-tm (Coh Γ A σ) = Coh≡ ctx-refl ty-refl (id-sub-lemma-sub σ)

id-sub-lemma-sub σ i = id-sub-lemma-tm (get σ i)

id-sub-typing : (Γ : Ctx n) → Γ ⊢ → Γ ⊢ id-sub n :: Γ
id-sub-typing Γ (TypeCtxBase .Γ) = TypeSubEmpty (id-sub 0)
id-sub-typing Γ p@(TypeCtxStep .Γ x) = TypeSubStep (liftingSubLemma p (transport-sub ctx-refl ctx-refl (λ i → tm-refl) (id-sub-typing (front Γ) (typeCheck⇒ctxCheck x)))) x (TypeTermVar (fromℕ _) (TypeCtxStep Γ x) (id-sub-lemma-ty (get Γ (fromℕ _))))

typed-id-sub : (Γ : TypedCtx) → TypedSub Γ Γ
typed-id-sub Γ .sub = id-sub (size Γ)
typed-id-sub Γ .typing-sub = id-sub-typing (ctx Γ) (typing-ctx Γ)

typed-comp-sub : {Γ Δ Υ : TypedCtx} → TypedSub Δ Γ → TypedSub Υ Δ → TypedSub Υ Γ
typed-comp-sub σ τ .sub = sub σ ∘ sub τ
typed-comp-sub {Γ = Γ} σ τ .typing-sub = sub-comp-check (typing-ctx Γ) (typing-sub τ) (typing-sub σ)
