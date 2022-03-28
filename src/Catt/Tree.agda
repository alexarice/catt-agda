module Catt.Tree where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Connection
open import Catt.Suspension
open import Relation.Nullary

data Tree (Xr : ISet) (l : ℕ) : ℕ → Set where
  Sing : Xr l → Tree Xr l 0
  Join : Xr l → (S : Tree Xr l n) → (T : Tree Xr l m) → Tree Xr l (m + (2 + n))

variable
  S S′ T T′ U : Tree Xr l n

Tree⊤ : ℕ → Set
Tree⊤ = Tree ⊤ISet 0

pattern Sing⊤ = Sing tt
pattern Join⊤ x y = Join tt x y

singleton-ctx : Ctx 1
singleton-ctx = ∅ , ⋆

tree-size : Tree Xr l n → ℕ
tree-size {n = n} T = n

tree-to-ctx : (T : Tree Xr l m) → Ctx (suc m)
tree-last-var : (T : Tree Xr l n) → Tm (suc n)

tree-to-ctx (Sing _) = singleton-ctx
tree-to-ctx (Join _ S T) = connect-susp (tree-to-ctx S) (tree-to-ctx T)

tree-fst-var : (T : Tree Xr l n) → Tm (suc n)
tree-fst-var T = Var (fromℕ _)

tree-last-var (Sing _) = 0V
tree-last-var (Join _ S T) = tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

replace-label : Xr l → Tree Xr l n → Tree Xr l n
replace-label x (Sing _) = Sing x
replace-label x (Join _ S T) = Join x S T

connect-tree-length : (S : Tree Xr l n) → (T : Tree Xr l m) → ℕ
connect-tree-length {m = m} (Sing _) T = m
connect-tree-length (Join {x} _ S S′) T = connect-tree-length S′ T + (2 + x)

connect-tree : (S : Tree Xr l n) → (T : Tree Xr l m) → Tree Xr l (connect-tree-length S T)
connect-tree (Sing x) T = replace-label x T
connect-tree (Join x S S′) T = Join x S (connect-tree S′ T)

first-label : Tree Xr l n → Xr l
first-label (Sing x) = x
first-label (Join x S T) = x

map-tree : (f : Xr l → Yr l′) → Tree Xr l n → Tree Yr l′ n
map-tree f (Sing x) = Sing (f x)
map-tree f (Join x S T) = Join (f x) (map-tree f S) (map-tree f T)

suspTree : Xr l → Xr l → Tree Xr l n → Tree Xr l (2 + n)
suspTree x y T = Join x T (Sing y)

suspTree⊤ : Tree⊤ n → Tree⊤ (2 + n)
suspTree⊤ T = suspTree tt tt T

tree-dim : Tree Xr l n → ℕ
tree-dim (Sing _) = 0
tree-dim (Join _ S T) = suc (pred (tree-dim T) ⊔ tree-dim S)

is-linear : Tree Xr l n → Set
is-linear (Sing _) = ⊤
is-linear (Join _ S (Sing _)) = is-linear S
is-linear (Join _ S (Join _ _ _)) = ⊥

is-linear-dec : (T : Tree Xr l n) → Dec (is-linear T)
is-linear-dec (Sing _) = yes tt
is-linear-dec (Join _ S (Sing _)) = is-linear-dec S
is-linear-dec (Join _ S (Join _ _ _)) = no (λ x → x)

tree-bd-len : (d : ℕ) → (T : Tree Xr l n) → ℕ
tree-bd-len zero T = 0
tree-bd-len (suc d) (Sing _) = 0
tree-bd-len (suc d) (Join _ S T) = tree-bd-len (suc d) T + (2 + tree-bd-len d S)

tree-bd : (d : ℕ) → (T : Tree⊤ n) → Tree⊤ (tree-bd-len d T)
tree-bd zero T = Sing tt
tree-bd (suc d) (Sing _) = Sing tt
tree-bd (suc d) (Join _ S T) = Join tt (tree-bd d S) (tree-bd (suc d) T)

tree-inc : (d : ℕ) → (T : Tree Xr l n) → (b : Bool) → Sub (suc (tree-bd-len d T)) (suc n) ⋆
tree-inc zero T false = ⟨ ⟨⟩ , (Var (fromℕ _)) ⟩
tree-inc zero T true = ⟨ ⟨⟩ , (tree-last-var T) ⟩
tree-inc (suc d) (Sing _) b = ⟨ ⟨⟩ , 0V ⟩
tree-inc (suc d) (Join _ S T) b = sub-between-connect-susps (tree-inc d S b) (tree-inc (suc d) T b)

n-disc : (n : ℕ) → Tree⊤ (n * 2)
n-disc zero = Sing⊤
n-disc (suc n) = Join⊤ (n-disc n) Sing⊤

n-disc-is-linear : (n : ℕ) → is-linear (n-disc n)
n-disc-is-linear zero = tt
n-disc-is-linear (suc n) = n-disc-is-linear n
