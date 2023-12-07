module Catt.Tree.Insertion where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

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

insertion-tree-size :  (S : Tree n) → (p : BranchingPoint S d) → (T : Tree m) → ℕ
insertion-tree : (S : Tree n) → (p : BranchingPoint S d) → (T : Tree m) → Tree (insertion-tree-size S p T)

insertion-tree-size {m = m} (Join S₁ S₂) (BPHere) T = connect-tree-length T S₂
insertion-tree-size (Join {m = m} S₁ S₂) (BPExt P) T = m + suc (suc (insertion-tree-size S₁ P T))
insertion-tree-size (Join {n = n} S₁ S₂) (BPShift P) T = insertion-tree-size S₂ P T + suc (suc n)

insertion-tree (Join S₁ S₂) (BPHere) T = connect-tree T S₂
insertion-tree (Join S₁ S₂) (BPExt P) T = Join (insertion-tree S₁ P T) S₂
insertion-tree (Join S₁ S₂) (BPShift P) T = Join S₁ (insertion-tree S₂ P T)

interior-label : (S : Tree n)
               → (p : BranchingPoint S d)
               → (T : Tree m)
               → Label (someTree (insertion-tree S p T)) (susp-tree-n d T)
interior-label (Join S₁ S₂) BPHere T = ap (connect-tree-inc-left T S₂)
interior-label (Join S₁ S₂) (BPExt p) T PHere = SHere
interior-label (Join S₁ S₂) (BPExt p) T (PExt P) = SExt (interior-label S₁ p T P)
interior-label (Join S₁ S₂) (BPExt p) T (PShift PHere) = SShift SHere
interior-label (Join S₁ S₂) (BPShift p) T P = SShift (interior-label S₂ p T P)

-- interior-sub : (S : Tree n)
--              → (p : BranchingPoint S d)
--              → (T : Tree m)
--              → Sub (suc (d * 2 + m)) (suc (insertion-tree-size S p T)) ⋆
-- interior-sub S p T = label-to-sub (interior-label S p T ,, S⋆)

branching-path-to-path : (p : BranchingPoint T d) → Path T
branching-path-to-path {T = Join S T} BPHere = PExt (is-linear-max-path S)
branching-path-to-path {T = Join S T} (BPExt p) = PExt (branching-path-to-path p)
branching-path-to-path {T = Join S T} (BPShift p) = PShift (branching-path-to-path p)

branching-path-to-var : (p : BranchingPoint T d) → Tm (suc (tree-size T))
branching-path-to-var {T = Join S T} BPHere = 0V [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var {T = Join S T} (BPExt P) = susp-tm (branching-path-to-var P) [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var {T = Join S T} (BPShift P) = branching-path-to-var P [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

-- branching-path-to-type : (T : Tree n) → (P : BranchingPoint T d) → STy (someTree T)
-- branching-path-to-type (Join S T) (BPHere) = map-sty-ext (unbiased-type (tree-dim S) S)
-- branching-path-to-type (Join S T) (BPExt P) = map-sty-ext (branching-path-to-type S P)
-- branching-path-to-type (Join S T) (BPShift P) = map-sty-shift (branching-path-to-type T P)

exterior-label : (S : Tree n)
               → (p : BranchingPoint S d)
               → (T : Tree m)
               → (A : STy (someTree T))
               → .⦃ height-of-branching p ≃n d + sty-dim A ⦄
               → Label (someTree (insertion-tree S p T)) S
exterior-label (Join S₁ S₂) BPHere T A
  = label-between-connect-trees (term-to-label (SCoh T A (id-label-wt T)) A ∘ cast-to-disc (susp-tree S₁)) SPath
exterior-label (Join S₁ S₂) (BPExt p) T A
  = label-between-joins (exterior-label S₁ p T A) SPath
exterior-label (Join S₁ S₂) (BPShift p) T A
  = label-between-joins SPath (exterior-label S₂ p T A)

-- exterior-sub : (S : Tree n)
--              → (p : BranchingPoint S d)
--              → (T : Tree m)
--              → Sub (suc (tree-size S)) (suc (insertion-tree-size S p T)) ⋆
-- exterior-sub S p T = label-to-sub (exterior-label S p T {!!} ,, S⋆)

label-from-insertion : (S : Tree n)
                     → (p : BranchingPoint S d)
                     → (T : Tree m)
                     → (L : Label X S)
                     → (M : Label X (susp-tree-n d T))
                     → Label X (insertion-tree S p T)
label-from-insertion (Join S₁ S₂) BPHere T L M = connect-label M (L ∘ PShift)
label-from-insertion (Join S₁ S₂) (BPExt p) T L M PHere = L PHere
label-from-insertion (Join S₁ S₂) (BPExt p) T L M (PExt Z) = label-from-insertion S₁ p T (L ∘ PExt) (M ∘ PExt) Z
label-from-insertion (Join S₁ S₂) (BPExt p) T L M (PShift Z) = (L ∘ PShift) Z
label-from-insertion (Join S₁ S₂) (BPShift p) T L M PHere = L PHere
label-from-insertion (Join S₁ S₂) (BPShift p) T L M (PExt Z) = L (PExt Z)
label-from-insertion (Join S₁ S₂) (BPShift p) T L M (PShift Z) = label-from-insertion S₂ p T (L ∘ PShift) M Z

label-from-insertion′ : (S : Tree n)
                        → (p : BranchingPoint S d)
                        → (T : Tree m)
                        → (L : Label X S)
                        → (M : Label X (susp-tree-n d T))
                        → Label X (insertion-tree S p T)
label-from-insertion′ (Join S₁ S₂) BPHere T L M = replace-label (connect-label′ M (L ∘ PShift)) (L PHere)
label-from-insertion′ (Join S₁ S₂) (BPExt p) T L M PHere = L PHere
label-from-insertion′ (Join S₁ S₂) (BPExt p) T L M (PExt Z) = label-from-insertion′ S₁ p T (L ∘ PExt) (M ∘ PExt) Z
label-from-insertion′ (Join S₁ S₂) (BPExt p) T L M (PShift Z) = L (PShift Z)
label-from-insertion′ (Join S₁ S₂) (BPShift p) T L M PHere = L PHere
label-from-insertion′ (Join S₁ S₂) (BPShift p) T L M (PExt Z) = L (PExt Z)
label-from-insertion′ (Join S₁ S₂) (BPShift p) T L M (PShift Z) = label-from-insertion′ S₂ p T (L ∘ PShift) M Z

-- sub-from-insertion : (S : Tree n)
--                    → (p : BranchingPoint S d)
--                    → (T : Tree m)
--                    → .⦃ lh : has-linear-height d T ⦄
--                    → (σ : Sub (suc n) l ⋆)
--                    → (τ : Sub (suc m) l ⋆)
--                    → Sub (suc (insertion-tree-size S p T)) l ⋆
-- sub-from-insertion {l = l} S P T σ τ
--   = label-to-sub (label-from-insertion S P T (to-label S σ) (to-label T τ) ,, S⋆)

-- is-linear-has-linear-height : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → d ≤ tree-dim T → has-linear-height d T
-- is-linear-has-linear-height zero T p = tt
-- is-linear-has-linear-height (suc d) (Join T Sing) p = is-linear-has-linear-height d T (≤-pred p)

-- bp-height-<-hob : (p : BranchingPoint S d) → d < height-of-branching p
-- bp-height-<-hob BPHere = s≤s z≤n
-- bp-height-<-hob (BPExt p) = s≤s (bp-height-<-hob p)
-- bp-height-<-hob (BPShift p) = bp-height-<-hob p

-- prune-tree-lem : (S : Tree n)
--                → (p : BranchingPoint S d)
--                → has-linear-height d (n-disc (pred (height-of-branching p)))
-- prune-tree-lem S p = is-linear-has-linear-height (bp-height p) (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-pred (≤-trans (bp-height-<-hob p) (≤-trans (suc-pred-≤ (height-of-branching p)) (s≤s (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))))))

-- prune-tree : (S : Tree n)
--            → (p : BranchingPoint S d)
--            → Tree (insertion-tree-size S p (n-disc (pred (height-of-branching p))) ⦃ prune-tree-lem S p ⦄)
-- prune-tree S p = insertion-tree S p (n-disc (pred (height-of-branching p))) ⦃ prune-tree-lem S p ⦄
