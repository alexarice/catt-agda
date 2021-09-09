{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Support.Properties where

open import Catt.Syntax
open import Catt.Support
open import Relation.Binary
open import Data.Nat
open import Data.Bool
open import Data.Bool.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import Algebra.Definitions

∪-assoc : Associative _≡_ (_∪_ {n})
∪-assoc emp emp emp = refl
∪-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (∨-assoc x y z) (∪-assoc xs ys zs)

∪-left-unit : LeftIdentity _≡_ empty (_∪_ {n})
∪-left-unit emp = refl
∪-left-unit (x ∷ xs) = cong₂ _∷_ refl (∪-left-unit xs)

∪-right-unit : RightIdentity _≡_ empty (_∪_ {n})
∪-right-unit emp = refl
∪-right-unit (x ∷ xs) = cong₂ _∷_ (∨-identityʳ x) (∪-right-unit xs)

∪-comm : Commutative _≡_ (_∪_ {n})
∪-comm emp emp = refl
∪-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (∨-comm x y) (∪-comm xs ys)

∪-idem : Idempotent _≡_ (_∪_ {n})
∪-idem emp = refl
∪-idem (x ∷ xs) = cong₂ _∷_ (∨-idem x) (∪-idem xs)

module _ {n : ℕ} where

  open import Algebra.Definitions {A = VarSet n} _≡_
  open import Algebra.Structures {A = VarSet n} _≡_

  ∪-isMagma : IsMagma (_∪_)
  ∪-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong = cong₂ _∪_
    }

  ∪-isSemigroup : IsSemigroup _∪_
  ∪-isSemigroup = record
    { isMagma = ∪-isMagma
    ; assoc = ∪-assoc
    }

  -- ∪-isCommutativeSemigroup : IsCommutativeSemigroup _∪_

-- empty-left-unit : (vs : VarSet n) → empty ∪ vs ≃vs vs
-- empty-left-unit emp = refl≃vs
-- empty-left-unit (ewf vs) = ≃VFalse (empty-left-unit vs)
-- empty-left-unit (ewt vs) = ≃VTrue (empty-left-unit vs)

-- empty-right-unit : (vs : VarSet n) → vs ∪ empty ≃vs vs
-- empty-right-unit emp = refl≃vs
-- empty-right-unit (ewf vs) = ≃VFalse (empty-right-unit vs)
-- empty-right-unit (ewt vs) = ≃VTrue (empty-right-unit vs)
