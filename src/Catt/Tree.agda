{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree where

open import Catt.Syntax
open import Catt.Connection
open import Catt.Suspension
open import Data.Nat
open import Data.Fin using (fromℕ)
open import Data.Empty
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

data Tree : ℕ → Set where
  Sing : Tree 0
  Join : (S : Tree n) → (T : Tree m) → Tree (m + (2 + n))

variable
  S S′ T T′ U : Tree n

singleton-ctx : Ctx 1
singleton-ctx = ∅ , ⋆

tree-size : Tree n → ℕ
tree-size {n} T = n

tree-to-ctx : (T : Tree m) → Ctx (suc m)
tree-last-var : (T : Tree n) → Tm (suc n)

tree-to-ctx Sing = singleton-ctx
tree-to-ctx (Join S T) = connect-susp (tree-to-ctx S) (tree-to-ctx T)

tree-fst-var : (T : Tree n) → Tm (suc n)
tree-fst-var T = Var (fromℕ _)

tree-last-var Sing = 0V
tree-last-var (Join S T) = tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

connect-tree-length : (S : Tree n) → (T : Tree m) → ℕ
connect-tree-length {m = m} Sing T = m
connect-tree-length (Join {x} S S′) T = connect-tree-length S′ T + (2 + x)

connect-tree : (S : Tree n) → (T : Tree m) → Tree (connect-tree-length S T)
connect-tree Sing T = T
connect-tree (Join S S′) T = Join S (connect-tree S′ T)

suspTree : Tree n → Tree (2 + n)
suspTree T = Join T Sing

max : ℕ → ℕ → ℕ
max zero m = m
max (suc n) m = suc (max n (pred m))

max-lem : (n : ℕ) → max n zero ≡ n
max-lem zero = refl
max-lem (suc n) = cong suc (max-lem n)

test1 : n ≤ m → max n m ≡ m
test1 z≤n = refl
test1 (s≤s p) = cong suc (test1 p)

test2 : n ≥ m → max n m ≡ n
test2 z≤n = max-lem _
test2 (s≤s p) = cong suc (test2 p)

tree-dim : Tree n → ℕ
tree-dim Sing = 0
tree-dim (Join S T) = max (suc (tree-dim S)) (tree-dim T)

is-linear : Tree n → Set
is-linear Sing = ⊤
is-linear (Join S Sing) = is-linear S
is-linear (Join S (Join _ _)) = ⊥

is-linear-dec : (T : Tree n) → Dec (is-linear T)
is-linear-dec Sing = yes tt
is-linear-dec (Join S Sing) = is-linear-dec S
is-linear-dec (Join S (Join T T₁)) = no (λ x → x)

tree-bd-len : (d : ℕ) → (T : Tree n) → ℕ
tree-bd-len zero T = 0
tree-bd-len (suc d) Sing = 0
tree-bd-len (suc d) (Join S T) = tree-bd-len (suc d) T + (2 + tree-bd-len d S)

tree-bd : (d : ℕ) → (T : Tree n) → Tree (tree-bd-len d T)
tree-bd zero T = Sing
tree-bd (suc d) Sing = Sing
tree-bd (suc d) (Join S T) = Join (tree-bd d S) (tree-bd (suc d) T)

tree-inc : (d : ℕ) → (T : Tree n) → (b : Bool) → Sub (suc (tree-bd-len d T)) (suc n) ⋆
tree-inc zero T false = ⟨ ⟨⟩ , (Var (fromℕ _)) ⟩
tree-inc zero T true = ⟨ ⟨⟩ , (tree-last-var T) ⟩
tree-inc (suc d) Sing b = ⟨ ⟨⟩ , 0V ⟩
tree-inc (suc d) (Join S T) b = sub-between-connect-susps (tree-inc d S b) (tree-inc (suc d) T b)

n-disk : (n : ℕ) → Tree (n * 2)
n-disk zero = Sing
n-disk (suc n) = Join (n-disk n) Sing

n-disk-is-linear : (n : ℕ) → is-linear (n-disk n)
n-disk-is-linear zero = tt
n-disk-is-linear (suc n) = n-disk-is-linear n

tree-dim-n-disk : (n : ℕ) → tree-dim (n-disk n) ≡ n
tree-dim-n-disk zero = refl
tree-dim-n-disk (suc n) = cong suc (trans (max-lem (tree-dim (n-disk n))) (tree-dim-n-disk n)) -- cong suc (tree-dim-n-disk n)
