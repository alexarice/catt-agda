module Catt.Prelude where

open import Data.Nat public
open import Data.Bool using (not;Bool;true;false;_∨_;_∧_;if_then_else_) renaming (T to Truth) public
open import Data.Fin using (Fin; zero; suc; inject₁; fromℕ; toℕ; cast; opposite; splitAt; _↑ˡ_; _↑ʳ_) renaming (_≟_ to _f≟_; _<?_ to _f<?_) public
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]r) public
open import Data.Product renaming (_,_ to _,,_) hiding (map) public
open import Relation.Binary.Definitions hiding (Irrelevant) public
open import Data.Empty using (⊥) public
open import Data.Empty.Irrelevant public
open import Data.Unit using (⊤; tt) public
open import Relation.Nullary using (¬_; Irrelevant; Dec; yes; no; recompute) public
open import Data.Fin.Patterns public
open import Data.Wrap public
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′) renaming (map to map⊎) public
open import Function using (it; _∘_; Equivalence) public

open Reveal_·_is_ public
open Equivalence public

infixr 2 _×′_
record _×′_ (A : Set) (B : Set) : Set where
  constructor build
  field
    ⦃ p₁ ⦄ : A
    ⦃ p₂ ⦄ : B

open _×′_ public

record WrapInst (A : Set) : Set where
  constructor inst
  field
    ⦃ wrapped ⦄ : A

open WrapInst public

variable
  n n′ m m′ l l′ o d d′ d″ : ℕ

record IsZero (n : ℕ) : Set where
  field
    isZero : Truth (n ≡ᵇ 0)

infix 4 _≃n_
_≃n_ : ℕ → ℕ → Set
zero ≃n zero = ⊤
zero ≃n suc m = ⊥
suc n ≃n zero = ⊥
suc n ≃n suc m = WrapInst (n ≃n m)

-- Instances

instance
  isZero : IsZero zero
  isZero = _

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

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

Odd Even : ℕ → Set
Odd zero = ⊥
Odd (suc n) = Even n
Even zero = ⊤
Even (suc n) = Odd n
