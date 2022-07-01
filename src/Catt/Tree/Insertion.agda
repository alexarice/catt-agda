module Catt.Tree.Insertion where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Label
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Variables
open import Catt.Variables.Properties

has-linear-height : ℕ → Tree n → Set
has-linear-height zero T = ⊤
has-linear-height (suc n) Sing = ⊥
has-linear-height (suc n) (Join T Sing) = has-linear-height n T
has-linear-height (suc n) (Join T (Join _ _)) = ⊥

data BranchingPoint : Tree n → Set where
  BPHere : .⦃ is-linear S ⦄ → BranchingPoint (Join S T)
  BPExt : BranchingPoint S → BranchingPoint (Join S T)
  BPShift : BranchingPoint T → BranchingPoint (Join S T)

bp-height : BranchingPoint T → ℕ
bp-height (BPHere) = 0
bp-height (BPExt bp) = suc (bp-height bp)
bp-height (BPShift bp) = bp-height bp

bp-antilinear : (p : BranchingPoint S) → (T : Tree n) → .⦃ _ : has-linear-height (bp-height p) T ⦄ → Set
bp-antilinear BPHere T = anti-linear T
bp-antilinear (BPExt p) (Join T Sing) = bp-antilinear p T
bp-antilinear (BPShift p) T = bp-antilinear p T

height-of-branching : {T : Tree n} → (p : BranchingPoint T) → ℕ
height-of-branching {T = Join S T} (BPHere) = suc (tree-dim S)
height-of-branching (BPExt P) = suc (height-of-branching P)
height-of-branching (BPShift P) = height-of-branching P

insertion-tree-size :  (S : Tree n) → (p : BranchingPoint S) → (T : Tree m) → .⦃ has-linear-height (bp-height p) T ⦄ → ℕ
insertion-tree : (S : Tree n) → (p : BranchingPoint S) → (T : Tree m) → .⦃ _ : has-linear-height (bp-height p) T ⦄ → Tree (insertion-tree-size S p T)

insertion-tree-size {m = m} (Join S₁ S₂) (BPHere) T = connect-tree-length T S₂
insertion-tree-size (Join {m = m} S₁ S₂) (BPExt P) (Join T Sing) = m + suc (suc (insertion-tree-size S₁ P T))
insertion-tree-size (Join {n = n} S₁ S₂) (BPShift P) T = insertion-tree-size S₂ P T + suc (suc n)

insertion-tree (Join S₁ S₂) (BPHere) T = connect-tree T S₂
insertion-tree (Join S₁ S₂) (BPExt P) (Join T Sing) = Join (insertion-tree S₁ P T) S₂
insertion-tree (Join S₁ S₂) (BPShift P) T = Join S₁ (insertion-tree S₂ P T)

interior-sub-label : (S : Tree n)
                  → (p : BranchingPoint S)
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height (bp-height p) T ⦄
                  → Label (someTree (insertion-tree S p T)) T
interior-sub-label (Join S₁ S₂) BPHere T = ap (connect-tree-inc-left T S₂)
interior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing) PHere = SHere
interior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing) (PExt P) = SExt (interior-sub-label S₁ p T P)
interior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing) (PShift PHere) = SShift SHere
interior-sub-label (Join S₁ S₂) (BPShift p) T P = SShift (interior-sub-label S₂ p T P)

interior-sub : (S : Tree n)
             → (p : BranchingPoint S)
             → (T : Tree m)
             → .⦃ _ : has-linear-height (bp-height p) T ⦄
             → Sub (suc m) (suc (insertion-tree-size S p T)) ⋆
interior-sub S p T = label-to-sub (interior-sub-label S p T ,, ⋆)

branching-path-to-path : (T : Tree n) → (p : BranchingPoint T) → Path T
branching-path-to-path (Join S T) BPHere = PExt (is-linear-max-path S)
branching-path-to-path (Join S T) (BPExt p) = PExt (branching-path-to-path S p)
branching-path-to-path (Join S T) (BPShift p) = PShift (branching-path-to-path T p)

branching-path-to-var : (T : Tree n) → (p : BranchingPoint T) → Tm (suc n)
branching-path-to-var (Join S T) (BPHere) = 0V [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var (Join S T) (BPExt P) = suspTm (branching-path-to-var S P) [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var (Join S T) (BPShift P) = branching-path-to-var T P [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

branching-path-to-type : (T : Tree n) → (P : BranchingPoint T) → Ty (suc n)
branching-path-to-type (Join S T) (BPHere) = suspTy (unbiased-type (tree-dim S) S) [ connect-susp-inc-left (tree-size S) (tree-size T) ]ty
branching-path-to-type (Join S T) (BPExt P) = suspTy (branching-path-to-type S P) [ connect-susp-inc-left (tree-size S) (tree-size T) ]ty
branching-path-to-type (Join S T) (BPShift P) = branching-path-to-type T P [ connect-susp-inc-right (tree-size S) (tree-size T) ]ty

exterior-sub-label : (S : Tree n)
                  → (p : BranchingPoint S)
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height (bp-height p) T ⦄
                  → Label (someTree (insertion-tree S p T)) S
exterior-sub-label (Join S₁ S₂) BPHere T
  = label-between-connect-trees (label-from-linear-tree-unbiased (suspTree S₁) T 0) SPath
exterior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing)
  = label-between-joins (exterior-sub-label S₁ p T) SPath
exterior-sub-label (Join S₁ S₂) (BPShift p) T
  = label-between-joins SPath (exterior-sub-label S₂ p T)

exterior-sub : (S : Tree n)
             → (p : BranchingPoint S)
             → (T : Tree m)
             → .⦃ _ : has-linear-height (bp-height p) T ⦄
             → Sub (suc (tree-size S)) (suc (insertion-tree-size S p T)) ⋆
exterior-sub S p T = label-to-sub (exterior-sub-label S p T ,, ⋆)

sub-from-insertion-label : (S : Tree n)
                        → (p : BranchingPoint S)
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (bp-height p) T ⦄
                        → (L : Label X S)
                        → (M : Label X T)
                        → Label X (insertion-tree S p T)
sub-from-insertion-label (Join S₁ S₂) BPHere T L M = connect-label M (L ∘ PShift)
sub-from-insertion-label (Join S₁ S₂) (BPExt p) (Join T Sing) L M PHere = M PHere
sub-from-insertion-label (Join S₁ S₂) (BPExt p) (Join T Sing) L M (PExt Z) = sub-from-insertion-label S₁ p T (L ∘ PExt) (M ∘ PExt) Z
sub-from-insertion-label (Join S₁ S₂) (BPExt p) (Join T Sing) L M (PShift Z) = replace-label (L ∘ PShift) (M (PShift PHere)) Z
sub-from-insertion-label (Join S₁ S₂) (BPShift p) T L M PHere = L PHere
sub-from-insertion-label (Join S₁ S₂) (BPShift p) T L M (PExt Z) = L (PExt Z)
sub-from-insertion-label (Join S₁ S₂) (BPShift p) T L M (PShift Z) = sub-from-insertion-label S₂ p T (L ∘ PShift) M Z

sub-from-insertion : (S : Tree n)
                         → (p : BranchingPoint S)
                         → (T : Tree m)
                         → .⦃ lh : has-linear-height (bp-height p) T ⦄
                         → (σ : Sub (suc n) l A)
                         → (τ : Sub (suc m) l A)
                         → Sub (suc (insertion-tree-size S p T)) l A
sub-from-insertion {l = l} {A = A} S P T σ τ
  = label-to-sub (sub-from-insertion-label S P T (to-label S σ) (to-label T τ) ,, A)
