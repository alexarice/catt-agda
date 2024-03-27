module Catt.Tree where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Wedge
open import Reflection
open import Agda.Builtin.List

data Tree : ℕ → Set where
  Sing : Tree 0
  Join : (S : Tree n) → (T : Tree m) → Tree (m + (2 + n))

variable
  S S′ T T′ U U′ : Tree n

singleton-ctx : Ctx 1
singleton-ctx = ∅ , ⋆

tree-size : Tree n → ℕ
tree-size {n} T = n

⌊_⌋ : (T : Tree m) → Ctx (suc m)

⌊ Sing ⌋ = singleton-ctx
⌊ Join S T ⌋ = wedge-susp ⌊ S ⌋ ⌊ T ⌋

tree-fst-var : (T : Tree n) → Tm (suc n)
tree-fst-var T = Var (fromℕ _)

tree-last-var : (T : Tree n) → Tm (suc n)
tree-last-var Sing = 0V
tree-last-var (Join S T) = tree-last-var T [ wedge-susp-inc-right (tree-size S) (tree-size T) ]tm

trunk-height : Tree n → ℕ
trunk-height Sing = 0
trunk-height (Join T Sing) = suc (trunk-height T)
trunk-height (Join T (Join T₁ T₂)) = 0

++t-length : (S : Tree n) → (T : Tree m) → ℕ
++t-length {m = m} Sing T = m
++t-length (Join {x} S S′) T = ++t-length S′ T + (2 + x)

infixr 6 _++t_
_++t_ : (S : Tree n) → (T : Tree m) → Tree (++t-length S T)
Sing ++t T = T
Join S S′ ++t T = Join S (S′ ++t T)

pattern Susp T = Join T Sing

susp-tree-n : (d : ℕ) → Tree n → Tree (d * 2 + n)
susp-tree-n zero T = T
susp-tree-n (suc d) T = Susp (susp-tree-n d T)

tree-dim : Tree n → ℕ
tree-dim Sing = 0
tree-dim (Join S T) = suc (pred (tree-dim T) ⊔ tree-dim S)

has-trunk-height : (n : ℕ) → Tree m → Set
has-trunk-height zero T = ⊤
has-trunk-height (suc n) Sing = ⊥
has-trunk-height (suc n) (Join T Sing) = WrapInst (has-trunk-height n T)
has-trunk-height (suc n) (Join T (Join _ _)) = ⊥

chop-trunk : (n : ℕ) → (T : Tree m) → .⦃ has-trunk-height n T ⦄ → Tree (m ∸ (n * 2))
chop-trunk zero T = T
chop-trunk (suc n) (Join T Sing) = chop-trunk n T

is-linear : Tree n → Set
is-linear T = has-trunk-height (tree-dim T) T

non-linear : Tree n → Set
non-linear Sing = ⊥
non-linear (Join T Sing) = non-linear T
non-linear (Join T (Join T₁ T₂)) = ⊤

is-linear-dec : (T : Tree n) → Dec (is-linear T)
is-linear-dec Sing = yes it
is-linear-dec (Join S Sing) with is-linear-dec S
... | yes x = yes (inst ⦃ x ⦄)
... | no x = no (λ y → x (y .wrapped))
is-linear-dec (Join S (Join T T₁)) = no (λ x → x)

n-disc : (n : ℕ) → Tree (double n)
n-disc zero = Sing
n-disc (suc n) = Join (n-disc n) Sing

instance
  n-disc-is-linear : ∀ {n} → is-linear (n-disc n)
  n-disc-is-linear {zero} = tt
  n-disc-is-linear {suc n} = inst

  is-linear-susp : ∀ {T : Tree n} → ⦃ is-linear T ⦄ → is-linear (Susp T)
  is-linear-susp = inst

is-join : Tree n → Set
is-join Sing = ⊥
is-join (Join S T) = ⊤

is-sing : Tree n → Set
is-sing Sing = ⊤
is-sing (Join S T) = ⊥
