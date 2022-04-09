module Catt.Tree.Insertion where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Variables
open import Catt.Variables.Properties

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

interior-sub : (S : Tree n) → (P : Path S) → (T : Tree m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → Sub (suc m) (suc (insertion-tree-size S P T)) ⋆
interior-sub (Join S₁ S₂) PHere T = idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _
interior-sub (Join S₁ S₂) (PExt P) (Join T Sing) = connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂) ∘ suspSub (interior-sub S₁ P T)
interior-sub (Join S₁ S₂) (PShift P) T = connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ∘ interior-sub S₂ P T

is-branching-path : {T : Tree n} → Path T → Set
is-branching-path {T = Join S T} PHere = is-linear S
is-branching-path (PExt P) = is-branching-path P
is-branching-path (PShift P) = is-branching-path P

height-of-branching : {T : Tree n} → (P : Path T) → .⦃ is-branching-path P ⦄ → ℕ
height-of-branching {T = Join S T} PHere = suc (tree-dim S)
height-of-branching (PExt P) = suc (height-of-branching P)
height-of-branching (PShift P) = height-of-branching P

branching-path-to-var : (T : Tree n) → (P : Path T) → .⦃ bp : is-branching-path P ⦄ → Tm (suc n)
branching-path-to-var (Join S T) (PHere) = 0V [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var (Join S T) (PExt P) = suspTm (branching-path-to-var S P) [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var (Join S T) (PShift P) ⦃ bp ⦄ = branching-path-to-var T P ⦃ bp ⦄ [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

exterior-sub : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → Sub (suc n) (suc (insertion-tree-size S P T)) ⋆
exterior-sub (Join S₁ S₂) PHere T
  = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)
exterior-sub (Join S₁ S₂) (PExt P) (Join T Sing) =
  sub-between-connect-susps (exterior-sub S₁ P T)
                            idSub
exterior-sub (Join S₁ S₂) (PShift P) T =
  sub-between-connect-susps idSub
                            (exterior-sub S₂ P T)

sub-from-insertion : (S : Tree n)
                   → (P : Path S)
                   → .⦃ bp : is-branching-path P ⦄
                   → (T : Tree m)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → (σ : Sub (suc n) l A)
                   → (τ : Sub (suc m) l A)
                   → Sub (suc (insertion-tree-size S P T)) l A
sub-from-insertion (Join S₁ S₂) PHere T σ τ
  = sub-from-connect τ
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ∘ (idSub≃ (connect-tree-to-ctx T S₂))
sub-from-insertion (Join S₁ S₂) (PExt P) (Join T Sing) σ τ
  = sub-from-connect (unrestrict (sub-from-insertion S₁ P T (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (getFst [ τ ]tm) (getSnd [ τ ]tm))
                                                             (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
sub-from-insertion (Join S₁ S₂) (PShift P) T σ τ
  = sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
