{-# OPTIONS --safe --without-K #-}

module Catt.Categorical where

open import Catt.Syntax
open import Catt.FreeVars
open import Catt.Typing
open import Catt.Bundles
open import Data.Nat
open import Catt.Fin
open import Catt.Syntax.Properties
open import Catt.Typing.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

private
  variable
    n m dim : ℕ

id-sub : (n : ℕ) → Sub n n
id-sub zero = ⟨⟩
id-sub (suc n) = ⟨ (liftSub (id-sub n)) , Var (fromℕ n) ⟩

id-sub-is-id-ty : (A : Ty n dim) → A [ id-sub n ]ty ≡ A
id-sub-is-id-tm : (t : Term n) → t [ id-sub n ]tm ≡ t
id-sub-is-id-sub-left : (σ : Sub m n) → id-sub n ∘ σ ≡ σ
id-sub-is-id-sub-right : (σ : Sub m n) → σ ∘ id-sub m ≡ σ

id-sub-is-id-ty ⋆ = refl
id-sub-is-id-ty (t ─⟨ A ⟩⟶ u)
  rewrite id-sub-is-id-tm t
  rewrite id-sub-is-id-ty A
  rewrite id-sub-is-id-tm u = refl

id-sub-is-id-tm (Var (fromℕ n)) = refl
id-sub-is-id-tm {suc n} (Var (inject x)) = begin
  Var x [ liftSub (id-sub n) ]tm ≡⟨ lift-sub-ap-tm (Var x) (id-sub n) ⟩
  liftTerm (Var x [ id-sub n ]tm) ≡⟨ cong liftTerm (id-sub-is-id-tm (Var x)) ⟩
  (Var (inject x)) ∎
id-sub-is-id-tm (Coh Γ A σ)
  rewrite id-sub-is-id-sub-right σ = refl

id-sub-is-id-sub-left {n = zero} ⟨⟩ = refl
id-sub-is-id-sub-left {n = suc n} ⟨ σ , t ⟩ = begin
  ⟨ liftSub (id-sub n) ∘ ⟨ σ , t ⟩ , t ⟩ ≡⟨ cong ⟨_, t ⟩ (sub-extend-sub (id-sub n) σ t) ⟩
  ⟨ id-sub n ∘ σ , t ⟩ ≡⟨ cong ⟨_, t ⟩ (id-sub-is-id-sub-left σ) ⟩
  ⟨ σ , t ⟩ ∎


id-sub-is-id-sub-right ⟨⟩ = refl
id-sub-is-id-sub-right ⟨ σ , x ⟩
  rewrite id-sub-is-id-sub-right σ
  rewrite id-sub-is-id-tm x = refl

id-sub-typing : (Γ : Ctx n) → Γ ⊢ → Γ ⊢ id-sub n :: Γ
id-sub-typing Γ TypeCtxBase = TypeSubEmpty
id-sub-typing {suc n} (Γ , A) p@(TypeCtxStep Γ b) = TypeSubStep (liftingSubLemma p (id-sub-typing Γ (typeCheck⇒ctxCheck b))) b (transport-tm refl i refl (TypeTermVar (fromℕ n) p))
  where
    i : liftType A ≡ A [ liftSub (id-sub _) ]ty
    i = begin
      liftType A ≡˘⟨ cong liftType (id-sub-is-id-ty A) ⟩
      liftType (A [ id-sub n ]ty) ≡˘⟨ lift-sub-ap-ty A (id-sub n) ⟩
      A [ liftSub (id-sub n) ]ty ∎

typed-id-sub : (Γ : TypedCtx) → TypedSub Γ Γ
typed-id-sub Γ .sub = id-sub (size Γ)
typed-id-sub Γ .typing-sub = id-sub-typing (ctx Γ) (typing-ctx Γ)

typed-comp-sub : {Γ Δ Υ : TypedCtx} → TypedSub Υ Δ → TypedSub Δ Γ → TypedSub Υ Γ
typed-comp-sub σ τ .sub = sub σ ∘ sub τ
typed-comp-sub {Γ = Γ} σ τ .typing-sub = sub-comp-check (typing-ctx Γ) (typing-sub σ) (typing-sub τ)
