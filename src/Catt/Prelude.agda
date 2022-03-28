module Catt.Prelude where

open import Data.Nat hiding (NonZero) public
open import Data.Bool using (not;Bool;true;false;_∨_;if_then_else_) renaming (T to Truth) public
open import Data.Fin using (Fin; zero; suc; inject₁; fromℕ; toℕ) renaming (_≟_ to _f≟_) public
open import Relation.Binary.PropositionalEquality public
open import Data.Product renaming (_,_ to _,,_) hiding (map) public
open import Relation.Binary.Definitions
open import Data.Empty using (⊥) public
open import Data.Unit using (⊤; tt) public
open import Level using (0ℓ) public

variable
  n n′ m m′ l l′ l″ o d d′ d″ : ℕ
  X Y Z : Set

⊥-elim : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim ()

ISet : Set₁
ISet = ℕ → Set

⊤ISet : ISet
⊤ISet n = ⊤

ISetRel : ISet → Set₁
ISetRel X = ∀ {n} {m} → X n → X m → Set

FullISetRel : (X : ISet) → ISetRel X
FullISetRel X _ _ = ⊤

variable
  Xr Yr : ISet

ISRRefl : ISetRel Xr → Set
ISRRefl {Xr = Xr} _∼_ = ∀ {l} {x : Xr l} → x ∼ x

ISRSym : ISetRel Xr → Set
ISRSym {Xr = Xr} _∼_ = ∀ {l l′} {x : Xr l} {y : Xr l′} → x ∼ y → y ∼ x

ISRTrans : ISetRel Xr → Set
ISRTrans {Xr = Xr} _∼_ = ∀ {l l′ l″} {x : Xr l} {y : Xr l′} {z : Xr l″} → x ∼ y → y ∼ z → x ∼ z

record NonZero (n : ℕ) : Set where
  field
    nonZero : Truth (not (n ≡ᵇ 0))

record IsZero (n : ℕ) : Set where
  field
    isZero : Truth (n ≡ᵇ 0)

-- Instances

instance
  nonZero : ∀ {n} → NonZero (suc n)
  nonZero = _

  isZero : IsZero zero
  isZero = _

it : ∀ {a} {A : Set a} → {{A}} → A
it {{x}} = x

tri-cases : {X : Set} → {x y : ℕ} → Tri (x < y) (x ≡ y) (x > y) → X → X → X → X
tri-cases (tri< _ _ _) X Y Z = X
tri-cases (tri≈ _ _ _) X Y Z = Y
tri-cases (tri> _ _ _) X Y Z = Z

tri-case< : {X : Set} {x y : ℕ} → x < y → (t : Tri (x < y) (x ≡ y) (x > y)) → (A B C : X) → tri-cases t A B C ≡ A
tri-case< p (tri< a ¬b ¬c) A B C = refl
tri-case< p (tri≈ ¬a b ¬c) A B C = ⊥-elim (¬a p)
tri-case< p (tri> ¬a ¬b c) A B C = ⊥-elim (¬a p)

tri-case≡ : {X : Set} {x y : ℕ} → x ≡ y → (t : Tri (x < y) (x ≡ y) (x > y)) → (A B C : X) → tri-cases t A B C ≡ B
tri-case≡ p (tri< a ¬b ¬c) A B C = ⊥-elim (¬b p)
tri-case≡ p (tri≈ ¬a b ¬c) A B C = refl
tri-case≡ p (tri> ¬a ¬b c) A B C = ⊥-elim (¬b p)

tri-case> : {X : Set} {x y : ℕ} → x > y → (t : Tri (x < y) (x ≡ y) (x > y)) → (A B C : X) → tri-cases t A B C ≡ C
tri-case> p (tri< a ¬b ¬c) A B C = ⊥-elim (¬c p)
tri-case> p (tri≈ ¬a b ¬c) A B C = ⊥-elim (¬c p)
tri-case> p (tri> ¬a ¬b c) A B C = refl
