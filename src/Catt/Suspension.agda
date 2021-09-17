{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension where

open import Catt.Syntax
open import Data.Nat
open import Data.Fin using (Fin;zero;suc;inject₁;fromℕ)
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁)
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Variables

suspTree : Tree n → Tree (2 + n)
suspCtx : Ctx n → Ctx (2 + n)
suspTy : Ty n d → Ty (2 + n) (suc d)
getFst : Tm (2 + n)
getSnd : Tm (2 + n)
suspTm : Tm n → Tm (2 + n)
suspSub : Sub n m → Sub (2 + n) (2 + m)

suspTree T = Join T Sing

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = getFst ─⟨ ⋆ ⟩⟶ getSnd
suspTy (s ─⟨ A ⟩⟶ t) = suspTm s ─⟨ suspTy A ⟩⟶ suspTm t

getFst = Var (fromℕ _)

getSnd = Var (inject₁ (fromℕ _))

suspTm (Var i) = Var (inject₁ (inject₁ i))
suspTm (Coh T A σ) = Coh (suspTree T) (suspTy A) (suspSub σ)

suspSub ⟨⟩ = ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩
suspSub ⟨ σ , t ⟩ = ⟨ suspSub σ , suspTm t ⟩

suspension-vars : (i : Fin (2 + n)) → ((i ≡ fromℕ _) ⊎ (i ≡ inject₁ (fromℕ _))) ⊎ Σ[ j ∈ Fin n ] i ≡ inject₁ (inject₁ j)
suspension-vars {n = zero} zero = inj₁ (inj₂ refl)
suspension-vars {n = zero} (suc zero) = inj₁ (inj₁ refl)
suspension-vars {n = suc n} zero = inj₂ (zero ,, refl)
suspension-vars {n = suc n} (suc i) with suspension-vars i
... | inj₁ (inj₁ x) = inj₁ (inj₁ (cong suc x))
... | inj₁ (inj₂ y) = inj₁ (inj₂ (cong suc y))
... | inj₂ (j ,, p) = inj₂ ((suc j) ,, (cong suc p))

susp-var-split : VarSplit n m l → VarSplit (2 + n) (2 + m) (2 + l)
susp-var-split vs i with suspension-vars i
... | inj₁ (inj₁ _) = inj₂ (fromℕ _)
... | inj₁ (inj₂ _) = inj₂ (inject₁ (fromℕ _))
... | inj₂ (j ,, _) with vs j
... | inj₁ j = inj₁ (inject₁ (inject₁ j))
... | inj₂ j = inj₂ (inject₁ (inject₁ j))
