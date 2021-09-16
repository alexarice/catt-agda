{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Insertion where

open import Catt.Syntax
-- open import Catt.Dimension
open import Data.Nat
open import Data.Nat.Properties
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Catt.Pasting.Properties
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Suspension.Properties
-- open import Catt.Unsuspension
open import Data.Empty
open import Data.Unit using (⊤;tt)
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Product renaming (_,_ to _,,_)
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ; inject₁)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles
open import Data.Sum
open import Catt.Variables
open import Catt.Globular
open import Catt.Syntax.Properties
open import Catt.Pasting.Unbiased
open import Relation.Nullary
open import Data.Nat.Properties

data Path : Tree n → Set where
  PHere : {S : Tree m} → {T : Tree n} → Path (Join S T)
  PExt : {S : Tree m} {T : Tree n} → Path S → Path (Join S T)
  PShift : {S : Tree m} {T : Tree n} → Path T → Path (Join S T)

path-length : {T : Tree n} → Path T → ℕ
path-length PHere = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P

has-linear-height : ℕ → Tree n → Set
has-linear-height zero T = ⊤
has-linear-height (suc n) Sing = ⊥
has-linear-height (suc n) (Join T Sing) = has-linear-height n T
has-linear-height (suc n) (Join T (Join _ _)) = ⊥

insertion-tree-size :  (S : Tree n) → (P : Path S) → (T : Tree m) → .⦃ has-linear-height (path-length P) T ⦄ → ℕ
insertion-tree : (S : Tree n) → (P : Path S) → (T : Tree m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → Tree (insertion-tree-size S P T)

insertion-tree-size {m = m} (Join S₁ S₂) (PHere) T = connect-tree-length T S₂
insertion-tree-size (Join {m = m} S₁ S₂) (PExt P) (Join T Sing) = m + suc (suc (insertion-tree-size S₁ P T))
insertion-tree-size (Join {n = n} S₁ S₂) (PShift P) T = insertion-tree-size S₂ P T + suc (suc n)

insertion-tree (Join S₁ S₂) PHere T = connect-tree T S₂
insertion-tree (Join S₁ S₂) (PExt P) (Join T Sing) = Join (insertion-tree S₁ P T) S₂
insertion-tree (Join S₁ S₂) (PShift P) T = Join S₁ (insertion-tree S₂ P T)

interior-sub : (S : Tree n) → (P : Path S) → (T : Tree m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → Sub (suc m) (suc (insertion-tree-size S P T))
interior-sub (Join S₁ S₂) PHere T = idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-pd-inc-left (tree-to-pd T) _
interior-sub (Join S₁ S₂) (PExt P) (Join T Sing) = connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ∘ suspSub (interior-sub S₁ P T)
interior-sub (Join S₁ S₂) (PShift P) T = connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ∘ interior-sub S₂ P T

is-branching-path : {T : Tree n} → Path T → Set
is-branching-path {T = Join S T} PHere = is-linear S
is-branching-path (PExt P) = is-branching-path P
is-branching-path (PShift P) = is-branching-path P

height-of-branching : {T : Tree n} → (P : Path T) → .⦃ is-branching-path P ⦄ → ℕ
height-of-branching {T = Join S T} PHere = suc (height-of-linear S)
height-of-branching (PExt P) = suc (height-of-branching P)
height-of-branching (PShift P) = height-of-branching P

branching-path-to-var : (T : Tree n) → (P : Path T) → .⦃ bp : is-branching-path P ⦄ → Tm (suc n)
branching-path-to-var (Join S T) (PHere) = 0V [ connect-pd-inc-left (susp-pd (tree-to-pd S)) (tree-size T) ]tm
branching-path-to-var (Join S T) (PExt P) = suspTm (branching-path-to-var S P) [ connect-pd-inc-left (susp-pd (tree-to-pd S)) (tree-size T) ]tm
branching-path-to-var (Join S T) (PShift P) ⦃ bp ⦄ = branching-path-to-var T P ⦃ bp ⦄ [ connect-pd-inc-right (susp-pd (tree-to-pd S)) (tree-size T) ]tm

exterior-sub : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → .⦃ p : height-of-branching P ≡ tree-to-pd-dim T ⦄
             → Sub (suc n) (suc (insertion-tree-size S P T))
exterior-sub (Join S₁ S₂) PHere T ⦃ p = p ⦄
  = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connect-pds (susp-pd (tree-to-pd S₁))
                              (tree-to-pd T)
                              (sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) (unbiased-type (tree-to-pd T)) (idSub _))
                                ∘ idSub≃ (trans≃c (linear-tree-compat (susp-tree S₁)) (disc-≡ p)))
                              (idSub _)
exterior-sub (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ =
  sub-between-connect-pds (susp-pd (tree-to-pd S₁))
                          (susp-pd (tree-to-pd (insertion-tree S₁ P T)))
                          (suspSub (exterior-sub S₁ P T ⦃ p = cong pred p ⦄))
                          (idSub _)
exterior-sub (Join S₁ S₂) (PShift P) T =
  sub-between-connect-pds (susp-pd (tree-to-pd S₁))
                          (susp-pd (tree-to-pd S₁))
                          (idSub _)
                          (exterior-sub S₂ P T)

insertion-var-split : (S : Tree n)
                    → (P : Path S)
                    → .⦃ bp : is-branching-path P ⦄
                    → (T : Tree m)
                    → .⦃ lh : has-linear-height (path-length P) T ⦄
                    → VarSplit (suc (insertion-tree-size S P T)) (suc n) (suc m)
insertion-var-split (Join S₁ S₂) PHere T i with connect-pd-var-split (tree-to-pd T) (tree-size S₂) (idSub≃-func (connect-tree-to-ctx T S₂) i)
... | inj₁ j = inj₂ j
... | inj₂ j = inj₁ (varToVarFunction (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-right-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ j)
insertion-var-split (Join S₁ S₂) (PExt P) (Join T Sing) i with connect-pd-var-split (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) i
... | inj₂ j = inj₁ (varToVarFunction (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-right-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ j)
... | inj₁ j with susp-var-split (insertion-var-split S₁ P T) j
... | inj₁ k = inj₁ (varToVarFunction (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-left-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ k)
... | inj₂ k = inj₂ k
insertion-var-split (Join S₁ S₂) (PShift P) T i with connect-pd-var-split-right (susp-pd (tree-to-pd S₁)) (tree-size (insertion-tree S₂ P T)) i
... | inj₁ j = inj₁ (varToVarFunction (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-left-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ j)
... | inj₂ j with insertion-var-split S₂ P T j
... | inj₁ k = inj₁ (varToVarFunction (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-right-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ k)
... | inj₂ k = inj₂ k

sub-from-insertion-func : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l)
                        → (τ : Sub (suc m) l)
                        → (i : Fin (suc (insertion-tree-size S P T)))
                        → Tm l
sub-from-insertion-func S P T σ τ i with insertion-var-split S P T i
... | inj₁ j = Var j [ σ ]tm
... | inj₂ j = Var j [ τ ]tm

sub-from-insertion : (S : Tree n)
                   → (P : Path S)
                   → .⦃ bp : is-branching-path P ⦄
                   → (T : Tree m)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → (σ : Sub (suc n) l)
                   → (τ : Sub (suc m) l)
                   → Sub (suc (insertion-tree-size S P T)) l
sub-from-insertion S P T σ τ = sub-from-function (sub-from-insertion-func S P T σ τ)
