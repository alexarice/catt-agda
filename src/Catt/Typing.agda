{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base

module Catt.Typing (Index : Set) (rule : Index → Rule) where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Induction
open import Catt.Pasting.Insertion
open import Catt.Pasting.Tree
open import Catt.Pasting.Properties
open import Catt.Support

data _≈c_ : (Γ : Ctx m) → (Δ : Ctx m′) → Set
data _≈tm_ : Tm Γ n → Tm Δ m → Set
data _≈ty_ : Ty Γ n → Ty Δ m → Set
data _≈s_ : (σ : Sub Γ Δ) → (τ : Sub Γ′ Δ′) → Set
data Typing-Ctx : (Γ : Ctx m) → Set
data Typing-Tm : (Γ : Ctx m) → Tm Γ (suc n) → Ty Γ n → Set
data Typing-Ty : (Γ : Ctx m) → Ty Γ n → Set
data Typing-Sub : (Γ : Ctx m) → (Δ : Ctx m′) → Sub Γ Δ → Set

data _≈c_ where
  Emp≈ : ∅ ≈c ∅
  Add≈ : Γ ≈c Γ′ → A ≈ty A′ → (Γ , A) ≈c (Γ′ , A′)

data _≈tm_ where
  Var≈ : {i : Fin (ctxLength Γ)} → {j : Fin (ctxLength Δ)} → (toℕ i ≡ toℕ j) → (Var {Γ = Γ} i) ≈tm (Var {Γ = Δ} j)
  Sym≈ : s ≈tm t → t ≈tm s
  Trans≈ : s ≈tm t → t ≈tm u → s ≈tm u
  Coh≈ : Δ ≈c Γ → A ≈ty B → σ ≈s τ → .{x : ctx-dim Δ ≤ ty-dim A} → .{y : ctx-dim Γ ≤ ty-dim B} → (Coh Δ A x σ) ≈tm (Coh Γ B y τ)
  Rule≈ : (i : Index)
        → (a : rule i .Args)
        → (tct : (j : rule i .tctIndex) → Typing-Tm (rule i .tctCtx j a) (rule i .tct j a) (rule i .tctTy j a))
        → (eqt : (j : rule i .eqtIndex) → (rule i .eqtlhs j a) ≈tm (rule i .eqtrhs j a))
        → (rule i .lhs a) ≈tm (rule i .rhs a)

data _≈ty_ where
  Star≈ : _≈ty_ {Γ = Γ} {Δ = Δ} ⋆ ⋆
  Arr≈ : s ≈tm s′ → A ≈ty A′ → t ≈tm t′ → (s ─⟨ A ⟩⟶ t) ≈ty (s′ ─⟨ A′ ⟩⟶ t′)

data _≈s_ where
  Null≈ : _≈s_ {Δ = Δ} {Δ′ = Δ′} ⟨⟩ ⟨⟩
  Ext≈ : σ ≈s τ → s ≈tm t → _≈s_ {Γ = Γ , A} {Γ′ = Γ′ , B} ⟨ σ , s ⟩ ⟨ τ , t ⟩

data Typing-Ctx where
  TyEmp : Typing-Ctx ∅
  TyAdd : Typing-Ctx Γ → Typing-Ty Γ A → Typing-Ctx (Γ , A)

data Typing-Tm where
  TyVar : (i : Fin (ctxLength Γ)) → {B : Ty Γ (lookupDim Γ i)} → (Γ ‼ i) ≈ty B → Typing-Tm Γ (Var i) B
  TyCoh : Δ ⊢pd₀ d → Typing-Ty Δ A → Typing-Sub Δ Γ σ → full ≃vs suppTy A → .{x : ctx-dim Δ ≤ ty-dim A} → (A [ σ ]ty) ≈ty B → Typing-Tm Γ (Coh Δ A x σ) B
  TyComp : (pd : Δ ⊢pd₀ (suc d)) → Typing-Ty Δ (s ─⟨ A ⟩⟶ t) → Typing-Sub Δ Γ σ → suppTm s ≃vs supp-src pd → suppTm t ≃vs supp-tgt pd → .{x : ctx-dim Δ ≤ suc (ty-dim A)} → ((s ─⟨ A ⟩⟶ t) [ σ ]ty) ≈ty B → Typing-Tm Γ (Coh Δ (s ─⟨ A ⟩⟶ t) x σ) B

data Typing-Ty where
  TyStar : Typing-Ty Γ ⋆
  TyArr : Typing-Tm Γ s A → Typing-Ty Γ A → Typing-Tm Γ t A → Typing-Ty Γ (s ─⟨ A ⟩⟶ t)

data Typing-Sub where
  TyNull : Typing-Sub ∅ Δ ⟨⟩
  TyExt : Typing-Sub Γ Δ σ → Typing-Ty Γ A → Typing-Tm Δ t (A [ σ ]ty) → Typing-Sub (Γ , A) Δ ⟨ σ , t ⟩
