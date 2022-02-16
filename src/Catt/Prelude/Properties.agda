module Catt.Prelude.Properties where

open import Catt.Prelude

open import Data.Nat.Properties public
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁;toℕ-fromℕ;toℕ-lower₁;inject₁-lower₁;inject₁-injective) public
open import Data.Bool.Properties using (∨-identityʳ;∨-assoc;∨-comm;∨-idem;∨-zeroʳ) public
open import Relation.Nullary public
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
