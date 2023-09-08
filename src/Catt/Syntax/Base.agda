module Catt.Syntax.Base where

open import Catt.Prelude

open import Data.Fin.Patterns

data Ctx : @0 ℕ → Set
data Ty : @0 ℕ → Set
data Tm : @0 ℕ → Set
data Sub : (@0 n m : ℕ) → (@0 A : Ty m) → Set

variable
  Γ Γ′ Δ Δ′ Υ Θ : Ctx n
  A A′ B C D : Ty n
  s s′ t t′ u : Tm n
  σ σ′ τ τ′ μ : Sub n m A

-- infixl 25 _,_
data Ctx where
  C1 : Ctx 0
  C2 : (Γ : Ctx n) → (A : Ty n) → Ctx (suc n)
{-# COMPILE AGDA2HS Ctx #-}

-- ctxLength : (Γ : Ctx n) → ℕ
-- ctxLength {n = n} Γ = n

-- infix 30 _─⟨_⟩⟶_
data Ty where
  Ty1 : ∀ {@0 n} → Ty n
  Ty2 : ∀ {@0 n} → (s : Tm n) → (A : Ty n) → (t : Tm n) → Ty n
{-# COMPILE AGDA2HS Ty #-}

data Sub where
  S1 : ∀ {@0 n A} → Sub 0 n A
  S2 : ∀ {@0 n m A} → (σ : Sub n m A) → (t : Tm m) → Sub (suc n) m A
{-# COMPILE AGDA2HS Sub #-}

data Tm where
  Var : ∀ {@0 n} → (m : ℕ) → @0 (m < n) → Tm n
  Coh : ∀ {@0 n m} → (Δ : Ctx (suc n)) → (A : Ty (suc n)) → (σ : Sub (suc n) m Ty1) → Tm m
{-# COMPILE AGDA2HS Tm #-}


pattern 0V {n} = Var {n} 0F
pattern 1V {n} = Var {n} 1F
pattern 2V {n} = Var {n} 2F
pattern 3V {n} = Var {n} 3F
pattern 4V {n} = Var {n} 4F
pattern 5V {n} = Var {n} 5F
pattern 6V {n} = Var {n} 6F
pattern 7V {n} = Var {n} 7F
pattern 8V {n} = Var {n} 8F
pattern 9V {n} = Var {n} 9F
