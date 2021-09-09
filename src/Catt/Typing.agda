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
open import Data.Nat.Induction
open import Catt.Pasting.Insertion
open import Catt.Pasting.Tree
open import Catt.Pasting.Properties
open import Catt.Support

private
  Index : Set
  Index = Fin index

data _≈c_ : (Γ : Ctx m) → (Δ : Ctx m′) → Set
data _≈tm_ : Tm n → Tm m → Set
data _≈ty_ : Ty n d → Ty m d′ → Set
data _≈s_ : (σ : Sub n m) → (τ : Sub n′ m′) → Set
data Typing-Ctx : (Γ : Ctx m) → Set
data Typing-Tm : (Γ : Ctx m) → Tm m → Ty m d → Set
data Typing-Ty : (Γ : Ctx m) → Ty m d → Set
data Typing-Sub : (Γ : Ctx m) → (Δ : Ctx n) → Sub m n → Set

data _≈c_ where
  Emp≈ : ∅ ≈c ∅
  Add≈ : Γ ≈c Γ′ → A ≈ty A′ → (Γ , A) ≈c (Γ′ , A′)

data _≈tm_ where
  Var≈ : n ≡ m → {i : Fin n} → {j : Fin m} → (toℕ i ≡ toℕ j) → (Var i) ≈tm (Var j)
  Sym≈ : s ≈tm t → t ≈tm s
  Trans≈ : s ≈tm t → t ≈tm u → s ≈tm u
  Coh≈ : Δ ≈c Γ → A ≈ty B → σ ≈s τ → (Coh Δ A σ) ≈tm (Coh Γ B τ)
  Rule≈ : (i : Index)
        → (a : rule i .Args)
        → (tct : (j : (tctIndex (rule i))) → Typing-Tm (rule i .tctCtx j a) (rule i .tct j a) (rule i .tctTy j a))
        → (eqt : (j : eqtIndex (rule i)) → (rule i .eqtlhs j a) ≈tm (rule i .eqtrhs j a))
        → (rule i .lhs a) ≈tm (rule i .rhs a)

data _≈ty_ where
  Star≈ : n ≡ m → (⋆ {n = n}) ≈ty (⋆ {n = m})
  Arr≈ : s ≈tm s′ → A ≈ty A′ → t ≈tm t′ → (s ─⟨ A ⟩⟶ t) ≈ty (s′ ─⟨ A′ ⟩⟶ t′)

data _≈s_ where
  Null≈ : n ≡ m → ⟨⟩ {n = n} ≈s ⟨⟩ {n = m}
  Ext≈ : σ ≈s τ → s ≈tm t → ⟨ σ , s ⟩ ≈s ⟨ τ , t ⟩

data Typing-Ctx where
  TyEmp : Typing-Ctx ∅
  TyAdd : Typing-Ctx Γ → Typing-Ty Γ A → Typing-Ctx (Γ , A)

data Typing-Tm where
  TyVar : {Γ : Ctx n} → (i : Fin n) → {B : Ty n d} → (Γ ‼ i) ≈ty B → Typing-Tm Γ (Var i) B
  TyCoh : Δ ⊢pd₀ d → Typing-Ty Δ A → Typing-Sub Δ Γ σ → FVTy A ≡ full → (A [ σ ]ty) ≈ty B → Typing-Tm Γ (Coh Δ A σ) B
  TyComp : (pd : Δ ⊢pd₀ (suc d)) → Typing-Ty Δ (s ─⟨ A ⟩⟶ t) → Typing-Sub Δ Γ σ → FVTy A ∪ FVTm s ≡ supp-src pd → FVTy A ∪ FVTm t ≡ supp-tgt pd → ((s ─⟨ A ⟩⟶ t) [ σ ]ty) ≈ty B → Typing-Tm Γ (Coh Δ (s ─⟨ A ⟩⟶ t) σ) B

data Typing-Ty where
  TyStar : Typing-Ty Γ ⋆
  TyArr : Typing-Tm Γ s A → Typing-Ty Γ A → Typing-Tm Γ t A → Typing-Ty Γ (s ─⟨ A ⟩⟶ t)

data Typing-Sub where
  TyNull : Typing-Sub ∅ Δ ⟨⟩
  TyExt : Typing-Sub Γ Δ σ → Typing-Ty Γ A → Typing-Tm Δ t (A [ σ ]ty) → Typing-Sub (Γ , A) Δ ⟨ σ , t ⟩
