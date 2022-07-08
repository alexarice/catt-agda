module Catt.Prelude.Properties where

open import Catt.Prelude

open import Data.Nat.Properties public
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁;toℕ-fromℕ;toℕ-lower₁;inject₁-lower₁;inject₁-injective; toℕ-cast) public
open import Data.Bool.Properties using (∨-identityʳ;∨-assoc;∨-comm;∨-idem;∨-zeroʳ) public
open import Relation.Binary using (Setoid) public
import Relation.Binary.Reasoning.Setoid
import Relation.Binary.Reasoning.PartialOrder
import Relation.Binary.Reasoning.StrictPartialOrder
open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp

module Reasoning = Relation.Binary.Reasoning.Setoid
module PReasoning = Relation.Binary.Reasoning.PartialOrder
module SPReasoning = Relation.Binary.Reasoning.StrictPartialOrder

suc-pred : (n : ℕ) → .⦃ NonZero n ⦄ → suc (pred n) ≡ n
suc-pred (suc n) = refl

suc-pred-≤ : (n : ℕ) → n ≤ suc (pred n)
suc-pred-≤ zero = z≤n
suc-pred-≤ (suc n) = ≤-refl

extract-is-zero : (n : ℕ) → .⦃ IsZero n ⦄ → n ≡ 0
extract-is-zero zero = refl

NonZero-subst : n ≡ m → NonZero n → NonZero m
NonZero-subst refl x = x

IsZero-subst : n ≡ m → IsZero n → IsZero m
IsZero-subst refl x = x

NonZero-⊥ : n ≤ 0 → .⦃ NonZero n ⦄ → ⊥
NonZero-⊥ {zero} p ⦃ () ⦄
NonZero-⊥ {suc n} ()

⊔-lem : (n m : ℕ) → suc n ⊔ m ≡ suc (pred m ⊔ n)
⊔-lem n zero = refl
⊔-lem n (suc m) = cong suc (⊔-comm n m)

proof-≡ : {I : Set} → {P : I → Set} → (c : Cases P) → {i : I} → doesC c ≡ i → P i
proof-≡ {P = P} (case _ proof) refl = proof

cases-≡ : {I A : Set} → {P : I → Set} → (c : Cases P) → (f : ∀ i (p : P i) → A) → {i : I} → (p : doesC c ≡ i) → cases c f ≡ f i (proof-≡ c p)
cases-≡ (case doesC₁ proofC₁) f refl = refl

-- ≤t-refl : n ≤t n
-- ≤t-refl {zero} = tt
-- ≤t-refl {suc n} = ≤t-refl {n}

-- ≤t-reflexive : n ≡ m → n ≤t m
-- ≤t-reflexive {n} refl = ≤t-refl {n}

-- ≤t-trans : n ≤t m → m ≤t l → n ≤t l
-- ≤t-trans {zero} {m} {l} p q = tt
-- ≤t-trans {suc n} {suc m} {suc l} p q = ≤t-trans {n} {m} {l} p q

-- ≤t-antisym : n ≤t m → m ≤t n → n ≡ m
-- ≤t-antisym {zero} {zero} p q = refl
-- ≤t-antisym {suc n} {suc m} p q = cong suc (≤t-antisym p q)

-- ≤t-isPreorder : Relation.Binary.IsPreorder _≡_ _≤t_
-- ≤t-isPreorder = record
--   { isEquivalence = isEquivalence
--   ; reflexive     = ≤t-reflexive
--   ; trans         = ≤t-trans
--   }
