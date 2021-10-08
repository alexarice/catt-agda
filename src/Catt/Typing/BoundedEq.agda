{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; toℕ)

module Catt.Typing.BoundedEq (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Syntax
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Catt.Tree
open import Catt.Globular

open import Catt.Typing index rule
open Rule


-- modifyRule : ℕ → Rule → Rule
-- modifyRule n r .Args = Σ[ a ∈ r .Args ] tm-height (r .tgtCtx a) (r .lhs a) ≤ n
-- modifyRule n r .len (a ,, p) = r .len a
-- modifyRule n r .tgtCtx (a ,, p) = r .tgtCtx a
-- modifyRule n r .lhs (a ,, p) = r .lhs a
-- modifyRule n r .rhs (a ,, p) = r .rhs a

-- _≈⟨_⟩[_]tm_ : Tm n → ℕ → Ctx n → Tm n → Set
-- s ≈⟨ d ⟩[ Γ ]tm t = s ≈[ Γ ]tm t
--   where open import Catt.Typing index (λ i → modifyRule d (rule i))

-- _≈⟨_⟩[_]ty_ : Ty n → ℕ → Ctx n → Ty n → Set
-- A ≈⟨ d ⟩[ Γ ]ty B = A ≈[ Γ ]ty B
--   where open import Catt.Typing index (λ i → modifyRule d (rule i))

-- _≈⟨_⟩[_]s_ : Sub m n A → ℕ → Ctx n → Sub m n B → Set
-- σ ≈⟨ d ⟩[ Γ ]s τ = σ ≈[ Γ ]s τ
--   where open import Catt.Typing index (λ i → modifyRule d (rule i))

-- module _ (d : ℕ) where
--   open import Catt.Typing index rule
--   import Catt.Typing index (λ i → modifyRule d (rule i)) as P

--   typing-to-bounded-tm : (Γ : Ctx n) → (t : Tm n) → (A : Ty n) → ty-dim A ≤ d → Typing-Tm Γ t A → P.Typing-Tm Γ t A
--   typing-to-bounded-tm Γ .(Var zero) A p (TyVarZ x) = P.TyVarZ {!!}
--   typing-to-bounded-tm .(_ , _) .(Var (suc i)) A p (TyVarS i tty x) = {!!}
--   typing-to-bounded-tm Γ .(Coh _ _ _) A p (TyCoh x x₁ b x₂ x₃) = {!!}

--   RuleB≈ : (i : Fin index)
--          → (a : rule i .Args)
--          → {C : Ty (rule i .len a)}
--          → Typing-Tm (rule i .tgtCtx a) (rule i .lhs a) C
--          → tm-height (rule i .tgtCtx a) (rule i .lhs a) ≤ d
--          → (rule i .lhs a) ≈⟨ d ⟩[ rule i .tgtCtx a ]tm (rule i .rhs a)
--   RuleB≈ i a tty p = P.Rule≈ i (a ,, p) {!!}


data _≈⟨_⟩[_]tm_ : Tm n → ℕ → Ctx n → Tm n → Set
data _≈⟨_⟩[_]ty_ : Ty n → ℕ → Ctx n → Ty n → Set
data _≈⟨_⟩[_]s_ : (σ : Sub n m A) → ℕ → Ctx m → (τ : Sub n m B) → Set

data _≈⟨_⟩[_]tm_ where
  VarB≈ : {i j : Fin n} → (toℕ i ≡ toℕ j) → (Var i) ≈⟨ d ⟩[ Γ ]tm (Var j)
  SymB≈ : s ≈⟨ d ⟩[ Γ ]tm t → t ≈⟨ d ⟩[ Γ ]tm s
  TransB≈ : s ≈⟨ d ⟩[ Γ ]tm t → t ≈⟨ d ⟩[ Γ ]tm u → s ≈⟨ d ⟩[ Γ ]tm u
  CohB≈ : A ≈⟨ d ⟩[ tree-to-ctx T ]ty B → σ ≈⟨ d ⟩[ Γ ]s τ → (Coh T A σ) ≈⟨ d ⟩[ Γ ]tm (Coh T B τ)
  RuleB≈ : (i : Fin index)
         → (a : rule i .Args)
         → {C : Ty (rule i .len a)}
         → Typing-Tm (rule i .tgtCtx a) (rule i .lhs a) C
         → BoundedTm d (rule i .tgtCtx a) (rule i .lhs a)
         → (rule i .lhs a) ≈⟨ d ⟩[ rule i .tgtCtx a ]tm (rule i .rhs a)

data _≈⟨_⟩[_]ty_ where
  StarB≈ : (⋆ {n = n}) ≈⟨ d ⟩[ Γ ]ty ⋆
  ArrB≈ : s ≈⟨ d ⟩[ Γ ]tm s′ → A ≈⟨ d ⟩[ Γ ]ty A′ → t ≈⟨ d ⟩[ Γ ]tm t′ → (s ─⟨ A ⟩⟶ t) ≈⟨ d ⟩[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′)

data _≈⟨_⟩[_]s_ where
  NullB≈ : A ≈⟨ d ⟩[ Δ ]ty B → ⟨⟩ {A = A} ≈⟨ d ⟩[ Δ ]s ⟨⟩ {A = B}
  ExtB≈ : σ ≈⟨ d ⟩[ Δ ]s τ → s ≈⟨ d ⟩[ Δ ]tm t → ⟨ σ , s ⟩ ≈⟨ d ⟩[ Δ ]s ⟨ τ , t ⟩
