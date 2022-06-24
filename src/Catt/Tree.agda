module Catt.Tree where

open import Catt.Prelude
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

tree-dim : Tree n → ℕ
tree-dim Sing = 0
tree-dim (Join S T) = suc (pred (tree-dim T) ⊔ tree-dim S)

is-linear : Tree n → Set
is-linear Sing = ⊤
is-linear (Join S Sing) = is-linear S
is-linear (Join S (Join _ _)) = ⊥

is-linear-dec : (T : Tree n) → Dec (is-linear T)
is-linear-dec Sing = yes tt
is-linear-dec (Join S Sing) = is-linear-dec S
is-linear-dec (Join S (Join T T₁)) = no (λ x → x)

n-disc : (n : ℕ) → Tree (n * 2)
n-disc zero = Sing
n-disc (suc n) = Join (n-disc n) Sing

n-disc-is-linear : (n : ℕ) → is-linear (n-disc n)
n-disc-is-linear zero = tt
n-disc-is-linear (suc n) = n-disc-is-linear n

is-join : Tree n → Set
is-join Sing = ⊥
is-join (Join S T) = ⊤

is-sing : Tree n → Set
is-sing Sing = ⊤
is-sing (Join S T) = ⊥
