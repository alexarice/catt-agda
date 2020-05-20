{-# OPTIONS --safe --without-K #-}

module Catt.Fin.Properties where

open import Data.Nat
open import Catt.Fin
open import Relation.Unary
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality
open import Data.Product

_≡f?_ : ∀ {n} → DecidableEquality (Fin n)
fromℕ n ≡f? fromℕ .n = yes refl
fromℕ n ≡f? inject j = no λ ()
inject i ≡f? fromℕ _ = no λ ()
inject i ≡f? inject j = map′ (cong inject) (λ where refl → refl) (i ≡f? j)

restrict : ∀ {n p} → ((Fin (suc n)) → Set p) → (Fin n → Set p)
restrict P i = P (inject i)

restrictDec : ∀ {n p} {P : Fin (suc n) → Set p} → Decidable P → Decidable (restrict P)
restrictDec P? i = P? (inject i)

any? : ∀ {n p} {P : Fin n → Set p} → Decidable P → Dec (∃ P)
any? {zero}  P? = no λ { (() , _) }
any? {suc n} P? with P? (fromℕ n) | any? (restrictDec P?)
... | yes p | q = yes (-, p)
... | no p | yes (fst , snd) = yes (-, snd)
... | no p | no q = no (λ where
  (fromℕ .n , snd) → p snd
  (inject fst , snd) → q (-, snd))

all? : ∀ {n p} {P : Pred (Fin n) p} →
       Decidable P → Dec (∀ f → P f)
all? {zero} P? = yes λ ()
all? {suc n} P? with P? (fromℕ n) | all? (restrictDec P?)
... | yes p | yes q = yes (λ where
  (fromℕ .n) → p
  (inject x) → q x)
... | yes p | no q = no (λ x → q (λ y → x (inject y)))
... | no p | q = no (λ x → p (x (fromℕ n)))
