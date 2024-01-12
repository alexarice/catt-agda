open import Catt.Typing.Base

module Catt.Typing {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Pasting

open Rule

infix 4 _≈[_]tm_ _≈[_]ty_ _≈[_]s_
data _≈[_]tm_ : Tm n → Ctx n → Tm n → Set
data _≈[_]ty_ : Ty n → Ctx n → Ty n → Set
data _≈[_]s_ : (σ : Sub n m A) → Ctx m → (τ : Sub n′ m B) → Set
data Typing-Ctx : (Γ : Ctx m) → Set
data Typing-Tm : (Γ : Ctx m) → Tm m → Ty m → Set
data Typing-Ty : (Γ : Ctx m) → Ty m → Set
data Typing-Sub : (Γ : Ctx m) → (Δ : Ctx n) → Sub m n A → Set

data _≈[_]tm_ where
  Var≈ : {i j : Fin n} → (toℕ i ≡ toℕ j) → (Var i) ≈[ Γ ]tm (Var j)
  Sym≈ : s ≈[ Γ ]tm t → t ≈[ Γ ]tm s
  Trans≈ : s ≈[ Γ ]tm t → t ≈[ Γ ]tm u → s ≈[ Γ ]tm u
  Coh≈ : A ≈[ Δ ]ty B → σ ≈[ Γ ]s τ → (Coh Δ A σ) ≈[ Γ ]tm (Coh Δ B τ)
  Rule≈ : (i : index)
        → {C : Ty (rule i .len)}
        → Typing-Tm (rule i .tgtCtx) (rule i .lhs) C
        → (rule i .lhs) ≈[ rule i .tgtCtx ]tm (rule i .rhs)

data _≈[_]ty_ where
  Star≈ : (⋆ {n = n}) ≈[ Γ ]ty ⋆
  Arr≈ : s ≈[ Γ ]tm s′ → A ≈[ Γ ]ty A′ → t ≈[ Γ ]tm t′ → (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′)

data _≈[_]s_ where
  Null≈ : A ≈[ Δ ]ty B → ⟨⟩ {A = A} ≈[ Δ ]s ⟨⟩ {A = B}
  Ext≈ : σ ≈[ Δ ]s τ → s ≈[ Δ ]tm t → ⟨ σ , s ⟩ ≈[ Δ ]s ⟨ τ , t ⟩

data Typing-Ctx where
  TyEmp : Typing-Ctx ∅
  TyAdd : Typing-Ctx Γ → Typing-Ty Γ A → Typing-Ctx (Γ , A)

data Typing-Tm where
  TyConv : Typing-Tm Γ s A → A ≈[ Γ ]ty B → Typing-Tm Γ s B
  TyVar : (i : Fin (ctxLength Γ)) → Typing-Tm Γ (Var i) (Γ ‼ i)
  TyCoh : .⦃ pd : Δ ⊢pd ⦄ → Typing-Ty Δ A → Typing-Sub Δ Γ σ → Typing-Tm Γ (Coh Δ A σ) (A [ σ ]ty)

data Typing-Ty where
  TyStar : Typing-Ty Γ ⋆
  TyArr : Typing-Tm Γ s A → Typing-Ty Γ A → Typing-Tm Γ t A → Typing-Ty Γ (s ─⟨ A ⟩⟶ t)

data Typing-Sub where
  TyNull : Typing-Ty Δ A → Typing-Sub ∅ Δ (⟨⟩ {A = A})
  TyExt : Typing-Sub Γ Δ σ → Typing-Tm Δ t (A [ σ ]ty) → Typing-Sub (Γ , A) Δ ⟨ σ , t ⟩
