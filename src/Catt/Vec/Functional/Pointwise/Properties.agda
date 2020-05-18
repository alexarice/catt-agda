{-# OPTIONS --without-K --safe #-}

module Catt.Vec.Functional.Pointwise.Properties where

open import Catt.Vec.Functional.Pointwise
open import Catt.Vec.Functional
open import Catt.Fin
open import Catt.Fin.Properties
open import Data.Nat
open import Level using (Level; 0ℓ)
open import Relation.Binary

private
  variable
    a b a′ b′ r s ℓ : Level
    A : ℕ → Set a
    B : ℕ → Set b
    A′ : ℕ → Set a′
    B′ : ℕ → Set b′

module _ {R : ∀ {n} → Rel (A n) ℓ} where

  refl : (∀ {m} → Reflexive {A = A m} (R {m})) → ∀ {n} → Reflexive {A = VectorD A n} (Pointwise R)
  refl r i = r

  sym : (∀ {m} → Symmetric (R {m})) → ∀ {n} → Symmetric {A = VectorD A n} (Pointwise R)
  sym s xsys i = s (xsys i)

  trans : (∀ {m} → Transitive (R {m})) → ∀ {n} → Transitive {A = VectorD A n} (Pointwise R)
  trans t xsys yszs i = t (xsys i) (yszs i)

  decidable : (∀ {m} → Decidable (R {m})) → ∀ {n} → Decidable {A = VectorD A n} (Pointwise R)
  decidable r? xs ys = all? (λ i → r? (get xs i) (get ys i))


  isEquivalence : (∀ m → IsEquivalence (R {m})) → ∀ n → IsEquivalence {A = VectorD A n} (Pointwise R)
  isEquivalence eq n = record
    { refl  = refl (λ {i} → IsEquivalence.refl (eq i))
    ; sym   = sym (λ {i} → IsEquivalence.sym (eq i))
    ; trans = trans (λ {i} → IsEquivalence.trans (eq i))
    }

  isDecEquivalence : (∀ m → IsDecEquivalence (R {m})) → ∀ n →
                     IsDecEquivalence {A = VectorD A n} (Pointwise R)
  isDecEquivalence isDecEq n = record
    { isEquivalence = isEquivalence (λ m → IsDecEquivalence.isEquivalence (isDecEq m)) n
    ; _≟_           = decidable (λ {i} → IsDecEquivalence._≟_ (isDecEq i))
    }


setoid :(ℕ → Setoid a ℓ) → ℕ → Setoid a ℓ
setoid S n = record
  { isEquivalence = isEquivalence (λ i → Setoid.isEquivalence (S i)) n
  }

decSetoid : (ℕ → DecSetoid a ℓ) → ℕ → DecSetoid a ℓ
decSetoid S n = record
  { isDecEquivalence = isDecEquivalence (λ i → DecSetoid.isDecEquivalence (S i)) n
  }

------------------------------------------------------------------------
-- map

module _ {R : ∀ {n} → REL (A n) (B n) r} {S : ∀ {n} → REL (A′ n) (B′ n) s} {f : ∀ n → A n → A′ n} {g : ∀ n → B n → B′ n} where

  map⁺ : (∀ {n x y} → R x y → S (f n x) (g n y)) →
         ∀ {n} {xs : VectorD A n} {ys : VectorD B n} →
         Pointwise R xs ys → Pointwise S (map f xs) (map g ys)
  map⁺ f rs i = f (rs i)

------------------------------------------------------------------------
-- head

module _ (R : ∀ {n} → REL (A n) (B n) r) {n} {xs : VectorD A (suc n)} {ys} where

  last⁺ : Pointwise R xs ys → R (last xs) (last ys)
  last⁺ rs = rs (fromℕ n)

------------------------------------------------------------------------
-- tail

module _ (R : ∀ {n} → REL (A n) (B n) r) {n} {xs : VectorD A (suc n)} {ys} where

  front⁺ : Pointwise R xs ys → Pointwise R (front xs) (front ys)
  front⁺ rs i = rs (inject i)
