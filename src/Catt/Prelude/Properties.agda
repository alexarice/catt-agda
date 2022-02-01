{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Prelude.Properties where

open import Catt.Prelude

open import Data.Nat.Properties public
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁;toℕ-fromℕ;toℕ-lower₁;inject₁-lower₁;inject₁-injective) public
open import Data.Bool.Properties using (∨-identityʳ;∨-assoc;∨-comm;∨-idem;∨-zeroʳ) public
import Relation.Binary.Reasoning.Setoid
import Relation.Binary.Reasoning.PartialOrder
open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MaxOp as MaxOp

module Reasoning = Relation.Binary.Reasoning.Setoid
module PReasoning = Relation.Binary.Reasoning.PartialOrder

suc-pred : (n : ℕ) → .⦃ NonZero n ⦄ → suc (pred n) ≡ n
suc-pred (suc n) = refl

extract-is-zero : (n : ℕ) → .⦃ IsZero n ⦄ → n ≡ 0
extract-is-zero zero = refl

NonZero-subst : n ≡ m → NonZero n → NonZero m
NonZero-subst refl x = x

IsZero-subst : n ≡ m → IsZero n → IsZero m
IsZero-subst refl x = x

NonZero-⊥ : n ≤ 0 → .⦃ NonZero n ⦄ → ⊥
NonZero-⊥ {zero} p ⦃ () ⦄
NonZero-⊥ {suc n} ()

max-lem : (m : ℕ) → max m zero ≡ m
max-lem zero = refl
max-lem (suc m) = cong suc (max-lem m)

max-prop₁ : m ≤ n → max m n ≡ n
max-prop₁ z≤n = refl
max-prop₁ (s≤s p) = cong suc (max-prop₁ p)

max-prop₂ : m ≥ n → max m n ≡ m
max-prop₂ z≤n = max-lem _
max-prop₂ (s≤s p) = cong suc (max-prop₂ p)

max-operator : MaxOperator ≤-totalPreorder
max-operator = record
  { _⊔_ = max
  ; x≤y⇒x⊔y≈y = max-prop₁
  ; x≥y⇒x⊔y≈x = max-prop₂
  }

private module max-properties = MaxOp max-operator

open max-properties public
  using ()
  renaming
  ( ⊔-cong       to  max-cong
  ; ⊔-congʳ      to  max-congʳ
  ; ⊔-congˡ      to  max-congˡ
  ; ⊔-idem       to  max-idem
  ; ⊔-sel        to  max-sel
  ; ⊔-assoc      to  max-assoc
  ; ⊔-comm       to  max-comm

  ; ⊔-identityˡ  to  max-identityˡ
  ; ⊔-identityʳ  to  max-identityʳ
  ; ⊔-identity   to  max-identity
  ; ⊔-zeroˡ      to  max-zeroˡ
  ; ⊔-zeroʳ      to  max-zeroʳ
  ; ⊔-zero       to  max-zero

  ; ⊔-isMagma                 to  max-isMagma
  ; ⊔-isSemigroup             to  max-isSemigroup
  ; ⊔-isCommutativeSemigroup  to  max-isCommutativeSemigroup
  ; ⊔-isBand                  to  max-isBand
  ; ⊔-isSemilattice           to  max-isSemilattice
  ; ⊔-isMonoid                to  max-isMonoid
  ; ⊔-isSelectiveMagma        to  max-isSelectiveMagma

  ; ⊔-magma                   to  max-magma
  ; ⊔-semigroup               to  max-semigroup
  ; ⊔-commutativeSemigroup    to  max-commutativeSemigroup
  ; ⊔-band                    to  max-band
  ; ⊔-semilattice             to  max-semilattice
  ; ⊔-monoid                  to  max-monoid
  ; ⊔-selectiveMagma          to  max-selectiveMagma

  ; x⊔y≈y⇒x≤y  to max-prop-inv₁
  ; x⊔y≈x⇒y≤x  to max-prop-inv₂
  ; x≤x⊔y      to max-inc₁
  ; x≤y⊔x      to max-inc₂

  ; ⊔-lub              to  max-lub
  ; ⊔-triangulate      to  max-triangulate
  ; ⊔-mono-≤           to  max-mono-≤
  ; ⊔-monoˡ-≤          to  max-monoˡ-≤
  ; ⊔-monoʳ-≤          to  max-monoʳ-≤
  )
