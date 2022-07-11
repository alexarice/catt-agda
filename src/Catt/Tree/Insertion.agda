module Catt.Tree.Insertion where

open import Catt.Prelude
open import Catt.Prelude.Properties
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

data BranchingPoint : Tree n → ℕ → Set where
  BPHere : .⦃ is-linear S ⦄ → BranchingPoint (Join S T) 0
  BPExt : BranchingPoint S n → BranchingPoint (Join S T) (suc n)
  BPShift : BranchingPoint T n → BranchingPoint (Join S T) n

bp-height : BranchingPoint S d → ℕ
bp-height {d = d} p = d

height-of-branching′ : {T : Tree n} → (p : BranchingPoint T d) → ℕ
height-of-branching′ {T = Join S T} (BPHere) = tree-dim S
height-of-branching′ (BPExt P) = suc (height-of-branching′ P)
height-of-branching′ (BPShift P) = height-of-branching′ P

height-of-branching : {T : Tree n} → (p : BranchingPoint T d) → ℕ
height-of-branching p = suc (height-of-branching′ p)

insertion-tree-size :  (S : Tree n) → (p : BranchingPoint S d) → (T : Tree m) → .⦃ has-linear-height d T ⦄ → ℕ
insertion-tree : (S : Tree n) → (p : BranchingPoint S d) → (T : Tree m) → .⦃ _ : has-linear-height d T ⦄ → Tree (insertion-tree-size S p T)

insertion-tree-size {m = m} (Join S₁ S₂) (BPHere) T = connect-tree-length T S₂
insertion-tree-size (Join {m = m} S₁ S₂) (BPExt P) (Join T Sing) = m + suc (suc (insertion-tree-size S₁ P T))
insertion-tree-size (Join {n = n} S₁ S₂) (BPShift P) T = insertion-tree-size S₂ P T + suc (suc n)

insertion-tree (Join S₁ S₂) (BPHere) T = connect-tree T S₂
insertion-tree (Join S₁ S₂) (BPExt P) (Join T Sing) = Join (insertion-tree S₁ P T) S₂
insertion-tree (Join S₁ S₂) (BPShift P) T = Join S₁ (insertion-tree S₂ P T)

interior-sub-label : (S : Tree n)
                  → (p : BranchingPoint S d)
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height d T ⦄
                  → Label (someTree (insertion-tree S p T)) T
interior-sub-label (Join S₁ S₂) BPHere T = ap (connect-tree-inc-left T S₂)
interior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing) PHere = SHere
interior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing) (PExt P) = SExt (interior-sub-label S₁ p T P)
interior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing) (PShift PHere) = SShift SHere
interior-sub-label (Join S₁ S₂) (BPShift p) T P = SShift (interior-sub-label S₂ p T P)

interior-sub : (S : Tree n)
             → (p : BranchingPoint S d)
             → (T : Tree m)
             → .⦃ _ : has-linear-height d T ⦄
             → Sub (suc m) (suc (insertion-tree-size S p T)) ⋆
interior-sub S p T = label-to-sub (interior-sub-label S p T ,, S⋆)

branching-path-to-path : (p : BranchingPoint T d) → Path T
branching-path-to-path {T = Join S T} BPHere = PExt (is-linear-max-path S)
branching-path-to-path {T = Join S T} (BPExt p) = PExt (branching-path-to-path p)
branching-path-to-path {T = Join S T} (BPShift p) = PShift (branching-path-to-path p)

branching-path-to-var : (T : Tree n) → (p : BranchingPoint T d) → Tm (suc n)
branching-path-to-var (Join S T) (BPHere) = 0V [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var (Join S T) (BPExt P) = suspTm (branching-path-to-var S P) [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var (Join S T) (BPShift P) = branching-path-to-var T P [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

branching-path-to-type : (T : Tree n) → (P : BranchingPoint T d) → STy (someTree T)
branching-path-to-type (Join S T) (BPHere) = map-sty-pext (unbiased-type (tree-dim S) S)
branching-path-to-type (Join S T) (BPExt P) = map-sty-pext (branching-path-to-type S P)
branching-path-to-type (Join S T) (BPShift P) = map-sty-pshift (branching-path-to-type T P)

exterior-sub-label : (S : Tree n)
                  → (p : BranchingPoint S d)
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height d T ⦄
                  → Label (someTree (insertion-tree S p T)) S
exterior-sub-label (Join S₁ S₂) BPHere T
  = label-between-connect-trees (label-from-linear-tree-unbiased (suspTree S₁) T 0) SPath
exterior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing)
  = label-between-joins (exterior-sub-label S₁ p T) SPath
exterior-sub-label (Join S₁ S₂) (BPShift p) T
  = label-between-joins SPath (exterior-sub-label S₂ p T)

exterior-sub : (S : Tree n)
             → (p : BranchingPoint S d)
             → (T : Tree m)
             → .⦃ _ : has-linear-height d T ⦄
             → Sub (suc (tree-size S)) (suc (insertion-tree-size S p T)) ⋆
exterior-sub S p T = label-to-sub (exterior-sub-label S p T ,, S⋆)

sub-from-insertion-label : (S : Tree n)
                        → (p : BranchingPoint S d)
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height d T ⦄
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
                   → (p : BranchingPoint S d)
                   → (T : Tree m)
                   → .⦃ lh : has-linear-height d T ⦄
                   → (σ : Sub (suc n) l ⋆)
                   → (τ : Sub (suc m) l ⋆)
                   → Sub (suc (insertion-tree-size S p T)) l ⋆
sub-from-insertion {l = l} S P T σ τ
  = label-to-sub (sub-from-insertion-label S P T (to-label S σ) (to-label T τ) ,, S⋆)

is-linear-has-linear-height : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → d ≤ tree-dim T → has-linear-height d T
is-linear-has-linear-height zero T p = tt
is-linear-has-linear-height (suc d) (Join T Sing) p = is-linear-has-linear-height d T (≤-pred p)

bp-height-<-hob : (p : BranchingPoint S d) → d < height-of-branching p
bp-height-<-hob BPHere = s≤s z≤n
bp-height-<-hob (BPExt p) = s≤s (bp-height-<-hob p)
bp-height-<-hob (BPShift p) = bp-height-<-hob p

prune-tree-lem : (S : Tree n)
               → (p : BranchingPoint S d)
               → has-linear-height d (n-disc (pred (height-of-branching p)))
prune-tree-lem S p = is-linear-has-linear-height (bp-height p) (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-pred (≤-trans (bp-height-<-hob p) (≤-trans (suc-pred-≤ (height-of-branching p)) (s≤s (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))))))

prune-tree : (S : Tree n)
           → (p : BranchingPoint S d)
           → Tree (insertion-tree-size S p (n-disc (pred (height-of-branching p))) ⦃ prune-tree-lem S p ⦄)
prune-tree S p = insertion-tree S p (n-disc (pred (height-of-branching p))) ⦃ prune-tree-lem S p ⦄
