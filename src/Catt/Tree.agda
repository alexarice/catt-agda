{-# OPTIONS --without-K --safe --postfix-projections #-}

module Catt.Tree where

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

record GlobSet (cells : ℕ → Set) : Set where
  field
    src : (n : ℕ) → cells (suc n) → cells n
    tgt : (n : ℕ) → cells (suc n) → cells n
    coh1 : ∀ n a → src n (src (suc n) a) ≡ src n (tgt (suc n) a)
    coh2 : ∀ n a → tgt n (src (suc n) a) ≡ tgt n (tgt (suc n) a)

open GlobSet

record TruncateAlg (A : Set) : Set where
  field
    truncate : ℕ → Bool → A → A
    dim : A → ℕ
    truncCoh : ∀ n a b b′ → truncate n b (truncate (suc n) b′ a) ≡ truncate n b a

open TruncateAlg

glob→trunc : {cells : ℕ → Set} → GlobSet cells → TruncateAlg (Σ ℕ cells)
glob→trunc {cells} gs .truncate n b (m , x) = go cells m x n (if b then (tgt gs) else (src gs))
  where
  go : (c : ℕ → Set) → (m : ℕ) → c m → ℕ → (func : ∀ o → c (suc o) → c o) → Σ ℕ c
  go c zero x n func = zero , x
  go c (suc m) x zero func = go c m (func m x) zero func
  go c (suc m) x (suc n) func = let (m′ , x′) = go (λ a → c (suc a)) m x n λ o → func (suc o) in suc m′ , x′
glob→trunc gs .dim (m , _) = m
glob→trunc gs .truncCoh n (m , x) b b′ = {!!}
