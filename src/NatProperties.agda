{-# OPTIONS --without-K --safe #-}

module NatProperties where

open import Data.Bool using (T)
open import Data.Bool.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Binary
open import Function.Base
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

0≤‴n : ∀{n} → 0 ≤‴ n
0≤‴n {n} = m≤‴m+k refl

<ᵇ⇒<‴ : ∀ {m n} → T (m <ᵇ n) → m <‴ n
<ᵇ⇒<‴ {m} {n} leq = ≤″⇒≤‴ (<ᵇ⇒<″ leq)

<‴⇒<ᵇ : ∀ {m n} → m <‴ n → T (m <ᵇ n)
<‴⇒<ᵇ leq = <″⇒<ᵇ (≤‴⇒≤″ leq)

infix 4 _<‴?_ _≤‴?_ _≥‴?_ _>‴?_

_<‴?_ : Decidable _<‴_
m <‴? n = map′ <ᵇ⇒<‴ <‴⇒<ᵇ (T? (m <ᵇ n))

_≤‴?_ : Decidable _≤‴_
zero ≤‴? n = yes 0≤‴n
suc m ≤‴? n = m <‴? n

_≥‴?_ : Decidable _≥‴_
_≥‴?_ = flip _≤‴?_

_>‴?_ : Decidable _>‴_
_>‴?_ = flip _<‴?_

¬<‴∧≤‴⇒≡ : ∀ {n m} → ¬ n <‴ m → n ≤‴ m → n ≡ m
¬<‴∧≤‴⇒≡ nlt ≤‴-refl = refl
¬<‴∧≤‴⇒≡ nlt (≤‴-step leq) = ⊥-elim (nlt leq)

≤⇒≤‴ : _≤_ ⇒ _≤‴_
≤⇒≤‴ = ≤″⇒≤‴ ∘ ≤⇒≤″

≤‴⇒≤ : _≤‴_ ⇒ _≤_
≤‴⇒≤ = ≤″⇒≤ ∘ ≤‴⇒≤″

1>i⇒0≡i : ∀ {i} → 1 > i → 0 ≡ i
1>i⇒0≡i (s≤s z≤n) = refl

1>‴i⇒0≡i : ∀ {i} → 1 >‴ i → 0 ≡ i
1>‴i⇒0≡i p = 1>i⇒0≡i (≤‴⇒≤ p)
