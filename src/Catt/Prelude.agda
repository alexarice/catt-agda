module Catt.Prelude where

open import Data.Nat hiding (NonZero) public
open import Data.Bool using (not;Bool;true;false;_∨_;if_then_else_) renaming (T to Truth) public
open import Data.Fin using (Fin; zero; suc; inject₁; fromℕ; toℕ; cast; opposite; splitAt; inject+; raise) renaming (_≟_ to _f≟_; _<?_ to _f<?_) public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Product renaming (_,_ to _,,_) hiding (map) public
open import Relation.Binary.Definitions
open import Data.Empty using (⊥) public
open import Data.Unit using (⊤; tt) public
open import Relation.Nullary public
open import Data.Fin.Patterns public

variable
  -- X Y Z : Set
  n n′ m m′ l l′ o d d′ d″ : ℕ

⊥-elim : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim ()

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

record Cases {I : Set} (P : I → Set) : Set where
  constructor case
  field
    doesC : I
    proofC : P doesC

open Cases public

cases : {I A : Set} → {P : I → Set} → Cases P → (∀ i (p : P i) → A) → A
cases (case d p) f = f d p

record IrrelΣ {a b} (A : Set a) (B : A → Set b) : Set (a Agda.Primitive.⊔ b) where
  constructor ⟦_⟧
  field
    carrier : A
    .⦃ prop ⦄ : B carrier

open IrrelΣ public

IrrelΣ-syntax : ∀ {a} {b} (A : Set a) → (A → Set b) → Set (a Agda.Primitive.⊔ b)
IrrelΣ-syntax = IrrelΣ

syntax IrrelΣ-syntax A (λ x → B) = IΣ[ x ∈ A ] B
