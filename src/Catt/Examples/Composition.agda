{-# OPTIONS --safe --without-K #-}

module Catt.Examples.Composition where

open import Catt.Base
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Catt.Examples.Base

private
  variable
    n : ℕ
    dim-1 : ℕ

2-comp : (dim-1 : ℕ) → Ctx (5 + dim-1 * 2)
2-comp dim-1 with build-disk (suc dim-1)
... | Γ , A , B , C = Γ , A , B , C , liftTypeN 3 A , Var (inject (inject (fromℕ _))) ─⟨ liftTypeN 4 A ⟩⟶ Var (fromℕ _)

2-comp-pdb : (dim-1 : ℕ) → 2-comp dim-1 ⊢pd Var (fromℕ _) ∷ proj₂ (2-comp dim-1 ‼ fromℕ _) [ 0 ][ suc dim-1 ]
2-comp-pdb dim-1 with build-disk (suc dim-1) | build-disk-pd (suc dim-1) | build-disk-dim-lem (suc dim-1)
... | Γ , A , B , C | pdb | refl = {!!}

2-comp-pd : (dim-1 : ℕ) → 2-comp dim-1 ⊢pd₀ suc dim-1
2-comp-pd dim-1 = Finish (proj₂ (proj₂ (reduce-to-0 (2-comp-pdb dim-1))))

2-comp-ty : (dim-1 : ℕ) → Ty (5 + dim-1 * 2) (suc dim-1)
2-comp-ty dim-1 = Var (inject (inject (inject (inject (fromℕ _))))) ─⟨ base ⟩⟶ Var (inject (fromℕ _))
  where
    lem : proj₁ (2-comp dim-1 ‼ inject (fromℕ _)) ≡ dim-1
    lem with build-disk dim-1 | build-disk-dim-lem dim-1
    ... | Γ , A | p = p

    lem2 : ∀ {n} {dim dim′} → dim ≡ dim′ → Ty n dim → Ty n dim′
    lem2 refl A = A

    base : Ty (5 + dim-1 * 2) dim-1
    base = lem2 lem (proj₂ (2-comp dim-1 ‼ inject (fromℕ _)))

2-comp-sub : TermAndType n (suc dim-1) → TermAndType n (suc dim-1) → Sub n (5 + (dim-1 * 2))
2-comp-sub {n} {dim-1} A@(x ,, t ─⟨ aty ⟩⟶ u) B@(y ,, t₁ ─⟨ bty ⟩⟶ u₁) = ⟨ ⟨ ⟨ ⟨ build-disk-sub dim-1 n (TermAndTypeSrc A) , u ⟩ , x ⟩ , u₁ ⟩ , y ⟩

2-compose : TermAndType n (suc dim-1) → TermAndType n (suc dim-1) → TermAndType n (suc dim-1)
2-compose {n} {dim-1} A@(atm ,, t ─⟨ aty ⟩⟶ _) B@(btm ,, _ ─⟨ bty ⟩⟶ u) = Coh (2-comp dim-1) (2-comp-ty dim-1) (2-comp-sub A B) ,, t ─⟨ aty ⟩⟶ u
