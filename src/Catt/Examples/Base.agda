{-# OPTIONS --safe --without-K #-}

module Catt.Examples.Base where

open import Catt.Base
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

private
  variable
    n : ℕ
    dim : ℕ
    dim′ : ℕ

build-disk : (dim : ℕ) → Ctx (suc (dim * 2))
build-disk zero = ∅ , ⋆
build-disk (suc dim) with build-disk dim
... | Δ , A = Δ , A , liftType A , Var (inject (fromℕ _)) ─⟨ liftTypeN 2 A ⟩⟶ Var (fromℕ _)

build-disk-dim-lem : (dim : ℕ) → proj₁ (last (build-disk dim)) ≡ dim
build-disk-dim-lem zero = refl
build-disk-dim-lem (suc dim) with build-disk dim | build-disk-dim-lem dim
... | Δ , A | refl = refl

build-disk-pd : (dim : ℕ) →
                build-disk dim ⊢pd Var (fromℕ _) ∷ proj₂ (last (build-disk dim)) [ 0 ][ dim ]
build-disk-pd zero = Base
build-disk-pd (suc dim) with build-disk dim | build-disk-pd dim | build-disk-dim-lem dim
... | Δ , A | pd | refl = ExtendM pd

build-disk-on-ctx : Ctx (suc n) → (dim : ℕ) → Ctx (suc (dim * 2 + n))
build-disk-on-ctx Γ zero = Γ
build-disk-on-ctx Γ (suc dim) with build-disk-on-ctx Γ dim
... | Δ , A = Δ , A , liftType A , Var (inject (fromℕ _)) ─⟨ liftTypeN 2 A ⟩⟶ Var (fromℕ _)

build-disk-sub : (dim-1 : ℕ) → (n : ℕ) → TermAndType n dim-1 → Sub n (suc (dim-1 * 2))
build-disk-sub zero n (x ,, ⋆) = ⟨ ⟨⟩ , x ⟩
build-disk-sub (suc dim-1) n A@(x ,, t ─⟨ B ⟩⟶ u) = ⟨ ⟨ (build-disk-sub dim-1 n (TermAndTypeSrc A)) , u ⟩ , x ⟩

build-disk-ctx-dim-lem : (Γ : Ctx (suc n)) → (dim : ℕ) → proj₁ (last (build-disk-on-ctx Γ dim)) ≡ dim + proj₁ (last Γ)
build-disk-ctx-dim-lem Γ zero = refl
build-disk-ctx-dim-lem Γ (suc dim) with build-disk-on-ctx Γ dim | build-disk-ctx-dim-lem Γ dim
... | Δ , A | refl = refl

build-disk-on-ctx-pd : {Γ : Ctx (suc n)} →
                       Γ ⊢pd Var (fromℕ _) ∷ proj₂ (last Γ) [ 0 ][ dim′ ] →
                       (dim : ℕ) →
                       build-disk-on-ctx Γ dim ⊢pd Var (fromℕ _) ∷ proj₂ (last (build-disk-on-ctx Γ dim)) [ 0 ][ dim + dim′ ]
build-disk-on-ctx-pd pdb zero = pdb
build-disk-on-ctx-pd {Γ = Γ} pdb (suc dim) with build-disk-on-ctx Γ dim | build-disk-on-ctx-pd pdb dim | build-disk-ctx-dim-lem Γ dim | pdb-dim-lemma pdb
... | Δ , A | pd | refl | refl = ExtendM pd
