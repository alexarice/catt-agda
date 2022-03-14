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

data Tree (X : Set) : ℕ → Set where
  Sing : X → Tree X 0
  Join : X → (S : Tree X n) → (T : Tree X m) → Tree X (m + (2 + n))

variable
  S S′ T T′ U : Tree X n

Tree⊤ : ℕ → Set
Tree⊤ = Tree ⊤

singleton-ctx : Ctx 1
singleton-ctx = ∅ , ⋆

tree-size : Tree X n → ℕ
tree-size {n = n} T = n

tree-to-ctx : (T : Tree X m) → Ctx (suc m)
tree-last-var : (T : Tree X n) → Tm (suc n)

tree-to-ctx (Sing _) = singleton-ctx
tree-to-ctx (Join _ S T) = connect-susp (tree-to-ctx S) (tree-to-ctx T)

tree-fst-var : (T : Tree X n) → Tm (suc n)
tree-fst-var T = Var (fromℕ _)

tree-last-var (Sing _) = 0V
tree-last-var (Join _ S T) = tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

connect-tree-length : (S : Tree X n) → (T : Tree X m) → ℕ
connect-tree-length {m = m} (Sing _) T = m
connect-tree-length (Join {x} _ S S′) T = connect-tree-length S′ T + (2 + x)

replace-label : X → Tree X n → Tree X n
replace-label x (Sing _) = Sing x
replace-label x (Join _ S T) = Join x S T

connect-tree : (S : Tree X n) → (T : Tree X m) → Tree X (connect-tree-length S T)
connect-tree (Sing x) T = replace-label x T
connect-tree (Join x S S′) T = Join x S (connect-tree S′ T)

suspTree : X → X → Tree X n → Tree X (2 + n)
suspTree x y T = Join x T (Sing y)

tree-dim : Tree X n → ℕ
tree-dim (Sing _) = 0
tree-dim (Join _ S T) = suc (pred (tree-dim T) ⊔ tree-dim S)

is-linear : Tree X n → Set
is-linear (Sing _) = ⊤
is-linear (Join _ S (Sing _)) = is-linear S
is-linear (Join _ S (Join _ _ _)) = ⊥

is-linear-dec : (T : Tree X n) → Dec (is-linear T)
is-linear-dec (Sing _) = yes tt
is-linear-dec (Join _ S (Sing _)) = is-linear-dec S
is-linear-dec (Join _ S (Join _ _ _)) = no (λ x → x)

tree-bd-len : (d : ℕ) → (T : Tree X n) → ℕ
tree-bd-len zero T = 0
tree-bd-len (suc d) (Sing _) = 0
tree-bd-len (suc d) (Join _ S T) = tree-bd-len (suc d) T + (2 + tree-bd-len d S)

tree-bd : (d : ℕ) → (T : Tree ⊤ n) → Tree ⊤ (tree-bd-len d T)
tree-bd zero T = Sing tt
tree-bd (suc d) (Sing _) = Sing tt
tree-bd (suc d) (Join _ S T) = Join tt (tree-bd d S) (tree-bd (suc d) T)

tree-inc : (d : ℕ) → (T : Tree X n) → (b : Bool) → Sub (suc (tree-bd-len d T)) (suc n) ⋆
tree-inc zero T false = ⟨ ⟨⟩ , (Var (fromℕ _)) ⟩
tree-inc zero T true = ⟨ ⟨⟩ , (tree-last-var T) ⟩
tree-inc (suc d) (Sing _) b = ⟨ ⟨⟩ , 0V ⟩
tree-inc (suc d) (Join _ S T) b = sub-between-connect-susps (tree-inc d S b) (tree-inc (suc d) T b)

n-disc : (n : ℕ) → Tree⊤ (n * 2)
n-disc zero = Sing tt
n-disc (suc n) = Join tt (n-disc n) (Sing tt)

n-disc-is-linear : (n : ℕ) → is-linear (n-disc n)
n-disc-is-linear zero = tt
n-disc-is-linear (suc n) = n-disc-is-linear n
