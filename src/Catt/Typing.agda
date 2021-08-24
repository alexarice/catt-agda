{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Typing where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Induction
open import Catt.Pasting.Insertion
open import Catt.Pasting.Tree
open import Catt.Pasting.Properties
open import Catt.Support

-- data Equality-Ctx : (Γ : Ctx m) → (Δ : Ctx m′) → Set
data Equality-Tm : (Γ : Ctx m) → Tm Γ n → Tm Γ n → Set
data Equality-Ty : (Γ : Ctx m) → Ty Γ n → Ty Γ n → Set
data Equality-Sub : (Γ : Ctx m) → (Δ : Ctx m′) → (σ : Sub Γ Δ) → (τ : Sub Γ Δ) → Set
data Typing-Ctx : (Γ : Ctx m) → Set
data Typing-Tm : (Γ : Ctx m) → Tm Γ (suc n) → Ty Γ n → Set
data Typing-Ty : (Γ : Ctx m) → Ty Γ n → Set
data Typing-Sub : (Γ : Ctx m) → (Δ : Ctx m′) → Sub Γ Δ → Set
typing-implies-pd : .{x : ctx-dim Δ ≤ ty-dim A} → Typing-Tm Γ (Coh Δ A x σ) B → Δ ⊢pd₀ pred (ctx-dim Δ)

data Equality-Tm where
  VarZ≈ : (i : Fin (ctxLength Γ)) → Equality-Tm Γ (Var i) (Var i)
  Sym≈ : Equality-Tm Γ s t → Equality-Tm Γ t s
  Trans≈ : Equality-Tm Γ s t → Equality-Tm Γ t u → Equality-Tm Γ s u
  Coh≈ : Equality-Ty Δ A B → Equality-Sub Δ Γ σ τ → {x : ctx-dim Δ ≤ ty-dim A} → {y : ctx-dim Δ ≤ ty-dim B} → Equality-Tm Γ (Coh Δ A x σ) (Coh Δ B y τ)
  Ins≈ : {x : ctx-dim Δ ≤ ty-dim A}
       → (ty : Typing-Tm Γ (Coh Δ A x σ) B)
       → (P : Path (pd-to-tree (typing-implies-pd ty)))
       → (bp : is-branching-path P)
       → (T : Tree n)
       → {τ : Sub (tree-to-ctx T) Γ}
       → {C : Ty (tree-to-ctx T) (suc (height-of-branching P _))}
       → {D : Ty Γ (suc (height-of-branching P _))}
       → {y : ctx-dim (tree-to-ctx T) ≤ ty-dim C}
       → (ty2 : Typing-Tm Γ (Coh (tree-to-ctx T) C y τ) D)
       → Equality-Tm Γ (branching-path-to-var-pd (typing-implies-pd ty) P bp [ σ ]tm) (Coh (tree-to-ctx T) C y τ)
       → (lh : has-linear-height (path-length P) T)
       → (tlh : type-has-linear-height (path-length P) T lh C)
       → Equality-Tm Γ
                     (Coh Δ A x σ)
                     (Coh (tree-to-ctx (insertion-tree (pd-to-tree (typing-implies-pd ty))
                                                       P
                                                       T
                                                       lh))
                          (A [ (exterior-sub (pd-to-tree (typing-implies-pd ty))
                                             P
                                             bp
                                             T
                                             lh
                                             C y tlh) ∘ idSub≃ (sym≃c (reflexive≃c (pd-to-tree-to-ctx (typing-implies-pd ty)))) ]ty)
                          -- Use reasoning?
                          (≤-trans (≤-reflexive (tree-to-ctx-dim (insertion-tree (pd-to-tree (typing-implies-pd ty)) P T _))) (≤-trans (s≤s (insertion-reduces-dim (pd-to-tree (typing-implies-pd ty)) P T bp lh (≤-pred (≤-trans (≤-reflexive (sym (tree-to-ctx-dim T))) y)))) (≤-trans (≤-reflexive (pd-to-tree-dim (typing-implies-pd ty))) x)))
                          (sub-from-insertion (pd-to-tree (typing-implies-pd ty))
                                              P
                                              bp
                                              T
                                              lh
                                              C
                                              y
                                              tlh
                                              (σ ∘ (idSub≃ (reflexive≃c (pd-to-tree-to-ctx (typing-implies-pd ty)))))
                                              τ))

data Equality-Ty where
  Star≈ : Equality-Ty Γ ⋆ ⋆
  Arr≈ : Equality-Tm Γ s s′ → Equality-Ty Γ A A′ → Equality-Tm Γ t t′ → Equality-Ty Γ (s ─⟨ A ⟩⟶ t) (s′ ─⟨ A′ ⟩⟶ t′)

data Equality-Sub where
  Null≈ : Equality-Sub ∅ Δ ⟨⟩ ⟨⟩
  Ext≈ : Equality-Sub Γ Δ σ τ → Equality-Tm Δ s t → Equality-Sub (Γ , A) Δ ⟨ σ , s ⟩ ⟨ τ , t ⟩

data Typing-Ctx where
  TyEmp : Typing-Ctx ∅
  TyAdd : Typing-Ctx Γ → Typing-Ty Γ A → Typing-Ctx (Γ , A)

data Typing-Tm where
  TyVar : (i : Fin (ctxLength Γ)) → {B : Ty Γ (lookupDim Γ i)} → Equality-Ty Γ (Γ ‼ i) B → Typing-Tm Γ (Var i) B
  TyCoh : Δ ⊢pd₀ d → Typing-Ty Δ A → Typing-Sub Δ Γ σ → full ≃vs suppTy A → .{x : ctx-dim Δ ≤ ty-dim A} → Equality-Ty Γ (A [ σ ]ty) B → Typing-Tm Γ (Coh Δ A x σ) B
  TyComp : (pd : Δ ⊢pd₀ (suc d)) → Typing-Ty Δ (s ─⟨ A ⟩⟶ t) → Typing-Sub Δ Γ σ → suppTm s ≃vs supp-src pd → suppTm t ≃vs supp-tgt pd → .{x : ctx-dim Δ ≤ suc (ty-dim A)} → Equality-Ty Γ ((s ─⟨ A ⟩⟶ t) [ σ ]ty) B → Typing-Tm Γ (Coh Δ (s ─⟨ A ⟩⟶ t) x σ) B

data Typing-Ty where
  TyStar : Typing-Ty Γ ⋆
  TyArr : Typing-Tm Γ s A → Typing-Ty Γ A → Typing-Tm Γ t A → Typing-Ty Γ (s ─⟨ A ⟩⟶ t)

data Typing-Sub where
  TyNull : Typing-Sub ∅ Δ ⟨⟩
  TyExt : Typing-Sub Γ Δ σ → Typing-Ty Γ A → Typing-Tm Δ t (A [ σ ]ty) → Typing-Sub (Γ , A) Δ ⟨ σ , t ⟩

pd-dim-lem : Δ ⊢pd₀ d → Δ ⊢pd₀ pred (ctx-dim Δ)
pd-dim-lem pd with cong pred (sym (pd-dim-is-ctx-dim pd))
... | refl = pd

typing-implies-pd (TyCoh x x₁ x₂ x₃ x₄) = pd-dim-lem x
typing-implies-pd (TyComp x x₁ x₂ x₃ x₄ x₅) = pd-dim-lem x
