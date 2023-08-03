module Catt.Tree where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection

data Tree : ℕ → Set where
  Sing : Tree 0
  Join : (S : Tree n) → (T : Tree m) → Tree (m + (2 + n))

variable
  S S′ T T′ U U′ : Tree n

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

linear-height : Tree n → ℕ
linear-height Sing = 0
linear-height (Join T Sing) = suc (linear-height T)
linear-height (Join T (Join T₁ T₂)) = 0

connect-tree-length : (S : Tree n) → (T : Tree m) → ℕ
connect-tree-length {m = m} Sing T = m
connect-tree-length (Join {x} S S′) T = connect-tree-length S′ T + (2 + x)

connect-tree : (S : Tree n) → (T : Tree m) → Tree (connect-tree-length S T)
connect-tree Sing T = T
connect-tree (Join S S′) T = Join S (connect-tree S′ T)

susp-tree : Tree n → Tree (2 + n)
susp-tree T = Join T Sing

tree-dim : Tree n → ℕ
tree-dim Sing = 0
tree-dim (Join S T) = suc (pred (tree-dim T) ⊔ tree-dim S)

has-linear-height : ℕ → Tree n → Set
has-linear-height zero T = ⊤
has-linear-height (suc n) Sing = ⊥
has-linear-height (suc n) (Join T Sing) = has-linear-height n T
has-linear-height (suc n) (Join T (Join _ _)) = ⊥

is-linear : Tree n → Set
is-linear T = has-linear-height (tree-dim T) T

non-linear : Tree n → Set
non-linear Sing = ⊥
non-linear (Join T Sing) = non-linear T
non-linear (Join T (Join T₁ T₂)) = ⊤

is-linear-dec : (T : Tree n) → Dec (is-linear T)
is-linear-dec Sing = yes tt
is-linear-dec (Join S Sing) = is-linear-dec S
is-linear-dec (Join S (Join T T₁)) = no (λ x → x)

n-disc : (n : ℕ) → Tree (double n)
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
