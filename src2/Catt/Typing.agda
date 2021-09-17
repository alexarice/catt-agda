{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; toℕ)

module Catt.Typing (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Catt.Support

private
  Index : Set
  Index = Fin index

-- data _≈c_ : (Γ : Ctx m) → (Δ : Ctx m) → Set
data _≈[_]tm_ : Tm n → Ctx n → Tm n → Set
data _≈[_]ty_ : Ty n d → Ctx n → Ty n d′ → Set
data _≈[_]s_ : (σ : Sub n m) → Ctx m → (τ : Sub n m) → Set
data Typing-Ctx : (Γ : Ctx m) → Set
data Typing-Tm : (Γ : Ctx m) → Tm m → Ty m d → Set
data Typing-Ty : (Γ : Ctx m) → Ty m d → Set
data Typing-Sub : (Γ : Ctx m) → (Δ : Ctx n) → Sub m n → Set

-- data _≈c_ where
--   Emp≈ : ∅ ≈c ∅
--   Add≈ : Γ ≈c Γ′ → A ≈ty A′ → (Γ , A) ≈c (Γ′ , A′)

data _≈[_]tm_ where
  Var≈ : {i j : Fin n} → (toℕ i ≡ toℕ j) → (Var i) ≈[ Γ ]tm (Var j)
  Sym≈ : s ≈[ Γ ]tm t → t ≈[ Γ ]tm s
  Trans≈ : s ≈[ Γ ]tm t → t ≈[ Γ ]tm u → s ≈[ Γ ]tm u
  Coh≈ : A ≈[ Δ ]ty B → σ ≈[ Γ ]s τ → (Coh Δ A σ) ≈[ Γ ]tm (Coh Δ B τ)
  Rule≈ : (i : Index)
        → (a : rule i .Args)
        → (eqt : (j : eqtIndex (rule i)) → (rule i .eqtlhs j a) ≈[ rule i .eqtCtx j a ]tm (rule i .eqtrhs j a))
        → {C : Ty (rule i .len a) d}
        → Typing-Tm (rule i .tgtCtx a) (rule i .lhs a) C
        → (rule i .lhs a) ≈[ rule i .tgtCtx a ]tm (rule i .rhs a)

data _≈[_]ty_ where
  Star≈ : (⋆ {n = n}) ≈[ Γ ]ty ⋆
  Arr≈ : s ≈[ Γ ]tm s′ → A ≈[ Γ ]ty A′ → t ≈[ Γ ]tm t′ → (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′)

data _≈[_]s_ where
  Null≈ : ⟨⟩ {n = n} ≈[ Δ ]s ⟨⟩
  Ext≈ : σ ≈[ Δ ]s τ → s ≈[ Δ ]tm t → ⟨ σ , s ⟩ ≈[ Δ ]s ⟨ τ , t ⟩

data Typing-Ctx where
  TyEmp : Typing-Ctx ∅
  TyAdd : Typing-Ctx Γ → Typing-Ty Γ A → Typing-Ctx (Γ , A)

data Typing-Tm where
  -- TyVar : {Γ : Ctx n} → (i : Fin n) → {B : Ty n d} → (Γ ‼ i) ≈[ Γ ]ty B → Typing-Tm Γ (Var i) B
  TyVarZ : Γ ‼ zero ≈[ Γ ]ty B → Typing-Tm Γ 0V B
  TyVarS : (i : Fin (ctxLength Γ)) → Typing-Tm Γ (Var i) A → liftType A ≈[ Γ , C ]ty B → Typing-Tm (Γ , C) (Var (suc i)) B
  TyCoh : Δ ⊢pd₀ d → Typing-Ty Δ A → Typing-Sub Δ Γ σ → FVTy A ≡ full → (A [ σ ]ty) ≈[ Γ ]ty B → Typing-Tm Γ (Coh Δ A σ) B
  TyComp : (pd : Δ ⊢pd₀ d) → .⦃ _ : NonZero′ d ⦄ → Typing-Ty Δ (s ─⟨ A ⟩⟶ t) → Typing-Sub Δ Γ σ → FVTy A ∪ FVTm s ≡ supp-src pd → FVTy A ∪ FVTm t ≡ supp-tgt pd → ((s ─⟨ A ⟩⟶ t) [ σ ]ty) ≈[ Γ ]ty B → Typing-Tm Γ (Coh Δ (s ─⟨ A ⟩⟶ t) σ) B
  -- TyConv : Typing-Tm Γ t A → A ≈[ Γ ]ty B → Typing-Tm Γ t B

data Typing-Ty where
  TyStar : Typing-Ty Γ ⋆
  TyArr : Typing-Tm Γ s A → Typing-Ty Γ A → Typing-Tm Γ t A → Typing-Ty Γ (s ─⟨ A ⟩⟶ t)

data Typing-Sub where
  TyNull : Typing-Sub ∅ Δ ⟨⟩
  TyExt : Typing-Sub Γ Δ σ → Typing-Tm Δ t (A [ σ ]ty) → Typing-Sub (Γ , A) Δ ⟨ σ , t ⟩
