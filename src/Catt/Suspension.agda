{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension where

open import Catt.Syntax.Base
open import Data.Nat
open import Data.Fin using (Fin;zero;suc;inject₁;fromℕ)
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁)
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
-- open import Catt.Variables

suspCtx : Ctx n → Ctx (2 + n)
suspTy : Ty n → Ty (2 + n)
getFst : Tm (2 + n)
getSnd : Tm (2 + n)
suspTm : Tm n → Tm (2 + n)
restrict : Sub (2 + n) m A → (s t : Tm m) → Sub n m (s ─⟨ A ⟩⟶ t)
unrestrict : Sub n m (s ─⟨ A ⟩⟶ t) → Sub (2 + n) m A
suspSubRes : (σ : Sub n m A) → Sub n (2 + m) (suspTy A)
suspSub : Sub n m ⋆ → Sub (2 + n) (2 + m) ⋆

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = getFst ─⟨ ⋆ ⟩⟶ getSnd
suspTy (s ─⟨ A ⟩⟶ t) = suspTm s ─⟨ suspTy A ⟩⟶ suspTm t

getFst = Var (fromℕ _)

getSnd = Var (inject₁ (fromℕ _))

suspTm (Var i) = Var (inject₁ (inject₁ i))
suspTm (Coh Δ A σ) = Coh (suspCtx Δ) (suspTy A) (suspSub σ)

restrict ⟨ ⟨ ⟨⟩ , _ ⟩ , _ ⟩ s t = ⟨⟩
restrict ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ s t = ⟨ restrict σ s t , u ⟩

unrestrict {s = s} {A = A} {t = t} ⟨⟩  = ⟨ ⟨ ⟨⟩ {A = A} , s ⟩ , t ⟩
unrestrict ⟨ σ , u ⟩ = ⟨ unrestrict σ , u ⟩

suspSubRes ⟨⟩ = ⟨⟩
suspSubRes ⟨ σ , t ⟩ = ⟨ suspSubRes σ , suspTm t ⟩

suspSub σ = unrestrict (suspSubRes σ)

-- newLength : (d : ℕ) → (n : ℕ) → ℕ
-- newLength zero n = n
-- newLength (suc d) n = newLength d (2 + n)

-- n-fold-suspTree : (d : ℕ) → (T : Tree n) → (Tree (newLength d n))
-- n-fold-suspTree zero T = T
-- n-fold-suspTree (suc d) T = n-fold-suspTree d (suspTree T)

-- n-fold-suspTy : (d : ℕ) → (A : Ty (suc n)) → Ty (suc (newLength d n))
-- n-fold-suspTy zero A = A
-- n-fold-suspTy (suc d) A = n-fold-suspTy d (suspTy A)

-- n-fold-suspSub : (d : ℕ) → (σ : Sub (suc n) (suc m) ⋆) → Sub (suc (newLength d n)) (suc (newLength d m)) ⋆
-- n-fold-suspSub zero σ = σ
-- n-fold-suspSub (suc d) σ = n-fold-suspSub d (suspSub σ)

-- full-unrestrict : Sub (suc n) m A → Sub (suc (newLength (ty-dim A) n)) m ⋆
-- full-unrestrict {A = ⋆} σ = σ
-- full-unrestrict {A = s ─⟨ A ⟩⟶ t} σ = full-unrestrict {A = A} (unrestrict σ)

-- suspension-vars : (i : Fin (2 + n)) → ((i ≡ fromℕ _) ⊎ (i ≡ inject₁ (fromℕ _))) ⊎ Σ[ j ∈ Fin n ] i ≡ inject₁ (inject₁ j)
-- suspension-vars {n = zero} zero = inj₁ (inj₂ refl)
-- suspension-vars {n = zero} (suc zero) = inj₁ (inj₁ refl)
-- suspension-vars {n = suc n} zero = inj₂ (zero ,, refl)
-- suspension-vars {n = suc n} (suc i) with suspension-vars i
-- ... | inj₁ (inj₁ x) = inj₁ (inj₁ (cong suc x))
-- ... | inj₁ (inj₂ y) = inj₁ (inj₂ (cong suc y))
-- ... | inj₂ (j ,, p) = inj₂ ((suc j) ,, (cong suc p))

-- susp-var-split : VarSplit n m l → VarSplit (2 + n) (2 + m) (2 + l)
-- susp-var-split vs i with suspension-vars i
-- ... | inj₁ (inj₁ _) = inj₂ (fromℕ _)
-- ... | inj₁ (inj₂ _) = inj₂ (inject₁ (fromℕ _))
-- ... | inj₂ (j ,, _) with vs j
-- ... | inj₁ j = inj₁ (inject₁ (inject₁ j))
-- ... | inj₂ j = inj₂ (inject₁ (inject₁ j))
