{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Insertion where

open import Catt.Syntax
open import Data.Nat
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Catt.Pasting.Properties
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Data.Empty
open import Data.Unit
open import Catt.Connection
open import Catt.Connection.Properties

data Path : Tree n → Set where
  PHere : (T : Tree n) → Path T
  PExt : {S : Tree m} {T : Tree n} → Path T → Path (Join S T)
  PShift : {S : Tree m} {T : Tree n} → Path S → Path (Join S T)

path-length : {T : Tree n} → Path T → ℕ
path-length (PHere _) = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P

has-linear-height : ℕ → Tree n → Set
has-linear-height zero T = ⊤
has-linear-height (suc n) Sing = ⊥
has-linear-height (suc n) (Join Sing T) = has-linear-height n T
has-linear-height (suc n) (Join (Join T T₂) T₁) = ⊥

insertion-tree-size :  (S : Tree n) → (P : Path S) → (T : Tree m) → .(has-linear-height (path-length P) T) → ℕ
insertion-tree : (S : Tree n) → (P : Path S) → (T : Tree m) → .(lh : has-linear-height (path-length P) T) → Tree (insertion-tree-size S P T lh)

insertion-tree-size {m = m} S (PHere .S) T lh = m
insertion-tree-size (Join {n} S₁ S₂) (PExt P) (Join Sing T) lh = suc (suc (insertion-tree-size S₂ P T lh + n))
insertion-tree-size (Join {m = m} S₁ S₂) (PShift P) T lh = suc (suc (m + insertion-tree-size S₁ P T lh))

insertion-tree S (PHere .S) T lh = T
insertion-tree (Join S₁ S₂) (PExt P) (Join Sing T) lh = Join S₁ (insertion-tree S₂ P T lh)
insertion-tree (Join S₁ S₂) (PShift P) T lh = Join (insertion-tree S₁ P T lh) S₂

interior-sub : (S : Tree n) → (P : Path S) → (T : Tree m) → .(lh : has-linear-height (path-length P) T) → Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S P T lh))
interior-sub S (PHere .S) T lh = idSub (tree-to-ctx T)
interior-sub (Join S₁ S₂) (PExt P) (Join Sing T) lh = connect-inc-right (tree-to-ctx S₁) (getFocusTerm (tree-to-pdb zero S₁ _)) (suspCtx (tree-to-ctx (insertion-tree S₂ P T _))) ∘ suspSub (interior-sub S₂ P T lh) ∘ idSub≃ (connect-pdb-left-unit (suspCtx (tree-to-ctx T)))
interior-sub (Join S₁ S₂) (PShift P) T lh = connect-inc-left (tree-to-ctx (insertion-tree S₁ P T _)) (getFocusTerm (tree-to-pdb zero (insertion-tree S₁ P T _) _)) (suspCtx (tree-to-ctx S₂)) ∘ interior-sub S₁ P T lh

is-linear : Tree n → Set
is-linear Sing = ⊤
is-linear (Join Sing T) = is-linear T
is-linear (Join (Join S S₁) T) = ⊥

is-branching-path : {T : Tree n} → Path T → Set
is-branching-path (PHere T) = is-linear T
is-branching-path (PExt P) = is-branching-path P
is-branching-path (PShift P) = is-branching-path P

height-of-linear : (T : Tree n) → .(is-linear T) → ℕ
height-of-linear Sing il = 0
height-of-linear (Join Sing T) il = suc (height-of-linear T il)

height-of-branching : {T : Tree n} → (P : Path T) → .(is-branching-path P) → ℕ
height-of-branching (PHere T) bp = height-of-linear T bp
height-of-branching (PExt P) bp = suc (height-of-branching P bp)
height-of-branching (PShift P) bp = height-of-branching P bp

type-has-linear-height : ℕ → (A : Ty Γ n) → Set
type-has-linear-height = {!!}

exterior-sub : (S : Tree n)
             → (P : Path S)
             → .(bp : is-branching-path P)
             → (T : Tree m)
             → .(lh : has-linear-height (path-length P) T)
             → (A : Ty (tree-to-ctx T) (height-of-branching P bp))
             → .(type-has-linear-height (path-length P) A)
             → Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S P T lh))
exterior-sub S (PHere .S) bp T lh A tlh = {!!}
exterior-sub (Join S₁ S₂) (PExt P) bp T lh A tlh = {!!}
exterior-sub (Join S₁ S₂) (PShift P) bp T lh A tlh = {!!}
