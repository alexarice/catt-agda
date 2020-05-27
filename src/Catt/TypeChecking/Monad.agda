{-# OPTIONS --without-K --safe --exact-split #-}

open import Category.Monad

module Catt.TypeChecking.Monad {F : Set → Set} (M : RawMonad F) where

open import Data.Sum.Base
open import Data.String
open import Function
open import Level using (0ℓ)
open import Relation.Nullary
open import Category.Applicative

open import Data.Sum.Categorical.Left String 0ℓ as S using (Sumₗ)

TCM : Set → Set
TCM = F ∘′ S.Sumₗ

private
  monad : RawMonad TCM
  monad = S.monadT M

module _ {A : Set} where

  open RawMonad M

  tc-ok : A → TCM A
  tc-ok x = return (inj₂ x)
  tc-fail : String → TCM A
  tc-fail s = return (inj₁ s)

  add-stack : String → TCM A → TCM A
  add-stack s m = m >>= λ where
    (inj₁ s′) → tc-fail $ s ++ "\n" ++ s′
    (inj₂ x) → tc-ok x

  alt : TCM A → TCM A → TCM A
  alt a b = do
    inj₁ x ← a
      where inj₂ α → return (inj₂ α)
    inj₁ y ← b
      where inj₂ β → return (inj₂ β)
    tc-fail ("Alt failed: " ++ x ++ " , " ++ y)

  decToTCM : String → Dec A → TCM A
  decToTCM s (yes p) = tc-ok p
  decToTCM s (no p) = tc-fail s

private
  applicativeZero : RawApplicativeZero TCM
  applicativeZero = record
    { applicative = RawMonad.rawIApplicative monad
    ; ∅ = tc-fail ""
    }

  -- This isn't actually an alternative but oh well
  alternative : RawAlternative TCM
  alternative = record
    { applicativeZero = applicativeZero
    ; _∣_ = alt
    }

monadPlus : RawMonadPlus TCM
monadPlus = record
  { monad = monad
  ; alternative = alternative
  }

open RawMonadPlus monadPlus public renaming (_⊛_ to _<*>_)
