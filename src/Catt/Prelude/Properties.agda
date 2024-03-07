module Catt.Prelude.Properties where

open import Catt.Prelude

open import Data.Nat.Properties public
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁;toℕ-fromℕ;toℕ-lower₁;inject₁-lower₁;inject₁-injective; toℕ-cast) public
open import Data.Bool.Properties using (∨-identityʳ;∨-assoc;∨-comm;∨-idem;∨-zeroʳ;∨-commutativeMonoid;∨-idempotentCommutativeMonoid;if-float;T-≡;T-not-≡) public
open import Relation.Binary using (Setoid) public
import Relation.Binary.Reasoning.Setoid
import Relation.Binary.Reasoning.PartialOrder
import Relation.Binary.Reasoning.StrictPartialOrder
open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp
open import Algebra.Bundles

module Reasoning = Relation.Binary.Reasoning.Setoid
module PReasoning = Relation.Binary.Reasoning.PartialOrder
module SPReasoning = Relation.Binary.Reasoning.StrictPartialOrder

suc-pred-≤ : (n : ℕ) → n ≤ suc (pred n)
suc-pred-≤ zero = z≤n
suc-pred-≤ (suc n) = ≤-refl

≤-step′ : suc n ≤ m → n ≤ m
≤-step′ (s≤s z≤n) = z≤n
≤-step′ (s≤s (s≤s p)) = s≤s (≤-step′ (s≤s p))

≤-from-≃n : n ≃n m → n ≤ m
≤-from-≃n {n = zero} p = z≤n
≤-from-≃n {n = suc n} {m = suc m} p = s≤s (≤-from-≃n it)

refl≃n : n ≃n n
refl≃n {n = zero} = tt
refl≃n {n = suc n} = inst ⦃ refl≃n ⦄

sym≃n : n ≃n m → m ≃n n
sym≃n {n = zero} {m = zero} p = tt
sym≃n {n = suc n} {m = suc m} p = inst ⦃ sym≃n it ⦄

trans≃n : n ≃n m → m ≃n o → n ≃n o
trans≃n {n = zero} {m = zero} {o = zero} p q = tt
trans≃n {n = suc n} {m = suc m} {o = suc o} p q = inst ⦃ trans≃n it it ⦄

extract-is-zero : (n : ℕ) → .⦃ IsZero n ⦄ → n ≡ 0
extract-is-zero zero = refl

NonZero-subst : n ≡ m → NonZero n → NonZero m
NonZero-subst refl x = x

IsZero-subst : n ≡ m → IsZero n → IsZero m
IsZero-subst refl x = x

NonZero-⊥ : n ≤ 0 → .⦃ NonZero n ⦄ → ⊥
NonZero-⊥ {zero} p ⦃ () ⦄
NonZero-⊥ {suc n} ()

NonZero-≤ : .(n ≤ m) → .(NonZero n) → NonZero m
NonZero-≤ {suc n} {suc m} p x = it

⊔-lem : (n m : ℕ) → suc n ⊔ m ≡ suc (pred m ⊔ n)
⊔-lem n zero = refl
⊔-lem n (suc m) = cong suc (⊔-comm n m)

Truth-left : (b b′ : Bool) → Truth b → Truth (b ∨ b′)
Truth-left true b′ p = tt

Truth-right : (b b′ : Bool) → Truth b′ → Truth (b ∨ b′)
Truth-right false true p = tt
Truth-right true true p = tt

Truth-not-left : (b b′ : Bool) → Truth (not (b ∨ b′)) → Truth (not b)
Truth-not-left false b′ p = tt

Truth-not-right : (b b′ : Bool) → Truth (not (b ∨ b′)) → Truth (not b′)
Truth-not-right false false p = tt

Truth-prop : {b : Bool} → Truth b → b ≡ true
Truth-prop {b = true} p = refl

Truth-prop′ : {b : Bool} → b ≡ true → Truth b
Truth-prop′ refl = tt

Truth-not-prop : {b : Bool} → Truth (not b) → b ≡ false
Truth-not-prop {b = false} p = refl

∨-monoid : Monoid _ _
∨-monoid = CommutativeMonoid.monoid ∨-commutativeMonoid

cong₃ : ∀ {A B C D : Set} {x x′ y y′ z z′} → (f : A → B → C → D) → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl

if-lem : (b : Bool) → (if b then true else false) ≡ b
if-lem false = refl
if-lem true = refl

if-lem-const : {A : Set} → (b : Bool) → (x : A) → (if b then x else x) ≡ x
if-lem-const false x = refl
if-lem-const true x = refl

≃n-to-≡ : n ≃n m → n ≡ m
≃n-to-≡ {n = zero} {m = zero} p = refl
≃n-to-≡ {n = suc n} {m = suc m} p = cong suc (≃n-to-≡ it)

≡-to-≃n : n ≡ m → n ≃n m
≡-to-≃n refl = refl≃n

Odd-is-NonZero : (n : ℕ) → Odd n → NonZero n
Odd-is-NonZero (suc n) odd = it
