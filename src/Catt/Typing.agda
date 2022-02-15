open import Catt.Prelude
open import Catt.Typing.Base

module Catt.Typing (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Catt.Support
open import Catt.Pasting

open Rule

private
  Index : Set
  Index = Fin index

data _≈[_]tm_ : Tm n → Ctx n → Tm n → Set
data _≈[_]ty_ : Ty n → Ctx n → Ty n → Set
data _≈[_]s_ : (σ : Sub n m A) → Ctx m → (τ : Sub n m B) → Set
data Typing-Ctx : (Γ : Ctx m) → Set
data Typing-Tm : (Γ : Ctx m) → Tm m → Ty m → Set
data Typing-Ty : (Γ : Ctx m) → Ty m → Set
data Typing-Sub : (Γ : Ctx m) → (Δ : Ctx n) → Sub m n A → Set

data _≈[_]tm_ where
  Var≈ : {i j : Fin n} → (toℕ i ≡ toℕ j) → (Var i) ≈[ Γ ]tm (Var j)
  Sym≈ : s ≈[ Γ ]tm t → t ≈[ Γ ]tm s
  Trans≈ : s ≈[ Γ ]tm t → t ≈[ Γ ]tm u → s ≈[ Γ ]tm u
  Coh≈ : A ≈[ Δ ]ty B → σ ≈[ Γ ]s τ → (Coh Δ A σ) ≈[ Γ ]tm (Coh Δ B τ)
  Rule≈ : (i : Index)
        → (a : rule i .Args)
        → {C : Ty (rule i .len a)}
        → Typing-Tm (rule i .tgtCtx a) (rule i .lhs a) C
        → (rule i .lhs a) ≈[ rule i .tgtCtx a ]tm (rule i .rhs a)

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
  TyVarZ : Typing-Ty Γ A → liftType A ≈[ Γ , A ]ty B → Typing-Tm (Γ , A) 0V B
  TyVarS : (i : Fin (ctxLength Γ)) → Typing-Tm Γ (Var i) A → liftType A ≈[ Γ , C ]ty B → Typing-Tm (Γ , C) (Var (suc i)) B
  TyCoh : .⦃ pd : Δ ⊢pd ⦄ → Typing-Ty Δ A → Typing-Sub Δ Γ σ → (b : Bool) → supp-condition b A Δ → (A [ σ ]ty) ≈[ Γ ]ty B → Typing-Tm Γ (Coh Δ A σ) B

data Typing-Ty where
  TyStar : Typing-Ty Γ ⋆
  TyArr : Typing-Tm Γ s A → Typing-Ty Γ A → Typing-Tm Γ t A → Typing-Ty Γ (s ─⟨ A ⟩⟶ t)

data Typing-Sub where
  TyNull : Typing-Ty Δ A → Typing-Sub ∅ Δ (⟨⟩ {A = A})
  TyExt : Typing-Sub Γ Δ σ → Typing-Ty Γ A → Typing-Tm Δ t (A [ σ ]ty) → Typing-Sub (Γ , A) Δ ⟨ σ , t ⟩
