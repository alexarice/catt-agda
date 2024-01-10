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
open import Catt.Tree.Canonical
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
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

insertion-tree-size :  (S : Tree n) → (p : BranchingPoint S d) → (T : Tree m) → .⦃ has-trunk-height d T ⦄ → ℕ
insertion-tree : (S : Tree n) → (p : BranchingPoint S d) → (T : Tree m) → .⦃ _ : has-trunk-height d T ⦄ → Tree (insertion-tree-size S p T)

insertion-tree-size {m = m} (Join S₁ S₂) (BPHere) T = ++t-length T S₂
insertion-tree-size (Join {m = m} S₁ S₂) (BPExt P) (Susp T) = m + suc (suc (insertion-tree-size S₁ P T))
insertion-tree-size (Join {n = n} S₁ S₂) (BPShift P) T = insertion-tree-size S₂ P T + suc (suc n)

insertion-tree (Join S₁ S₂) (BPHere) T = T ++t S₂
insertion-tree (Join S₁ S₂) (BPExt P) (Susp T) = Join (insertion-tree S₁ P T) S₂
insertion-tree (Join S₁ S₂) (BPShift P) T = Join S₁ (insertion-tree S₂ P T)

interior-label : (S : Tree n)
               → (p : BranchingPoint S d)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height d T ⦄
               → Label (someTree (insertion-tree S p T)) T
interior-label (Join S₁ S₂) BPHere T = ap (++t-inc-left T S₂)
interior-label (Join S₁ S₂) (BPExt p) (Susp T) = unrestrict-label (map-ext (interior-label S₁ p T ,, S⋆))
interior-label (Join S₁ S₂) (BPShift p) T P = SShift (interior-label S₂ p T P)

branching-path-to-path : (p : BranchingPoint T d) → Path T
branching-path-to-path {T = Join S T} BPHere = PExt (is-linear-max-path S)
branching-path-to-path {T = Join S T} (BPExt p) = PExt (branching-path-to-path p)
branching-path-to-path {T = Join S T} (BPShift p) = PShift (branching-path-to-path p)

branching-path-to-var : (p : BranchingPoint T d) → Tm (suc (tree-size T))
branching-path-to-var {T = Join S T} BPHere = 0V [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var {T = Join S T} (BPExt P) = susp-tm (branching-path-to-var P) [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var {T = Join S T} (BPShift P) = branching-path-to-var P [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

branching-path-to-type : (T : Tree n) → (P : BranchingPoint T d) → STy (someTree T)
branching-path-to-type (Join S T) (BPHere) = map-sty-ext (disc-sty S)
branching-path-to-type (Join S T) (BPExt P) = map-sty-ext (branching-path-to-type S P)
branching-path-to-type (Join S T) (BPShift P) = map-sty-shift (branching-path-to-type T P)

exterior-label′ : (S : Tree n)
                → (p : BranchingPoint S d)
                → (T : Tree m)
                → .⦃ _ : has-trunk-height d T ⦄
                → (As : STy (someTree (chop-trunk d T)))
                → .⦃ has-dim (height-of-branching p ∸ d) As ⦄
                → Label (someTree (insertion-tree S p T)) S
exterior-label′ (Join S₁ S₂) BPHere T As
  = label-between-++t (replace-label (stm-to-label (Susp S₁) (sty-to-coh As) As) SHere) SPath
exterior-label′ (Join S₁ S₂) (BPExt p) (Susp T) As
  = label-between-joins (exterior-label′ S₁ p T As) SPath
exterior-label′ (Join S₁ S₂) (BPShift p) T A
  = label-between-joins SPath (exterior-label′ S₂ p T A)

exterior-label : (S : Tree n)
               → (p : BranchingPoint S d)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height d T ⦄
               → Label (someTree (insertion-tree S p T)) S
exterior-label (Join S₁ S₂) BPHere T
  = label-between-++t (replace-label (canonical-label (Susp S₁) T) SHere) SPath
exterior-label (Join S₁ S₂) (BPExt p) (Susp T)
  = label-between-joins (exterior-label S₁ p T) SPath
exterior-label (Join S₁ S₂) (BPShift p) T
  = label-between-joins SPath (exterior-label S₂ p T)

label-from-insertion : (S : Tree n)
                     → (p : BranchingPoint S d)
                     → (T : Tree m)
                     → .⦃ _ : has-trunk-height d T ⦄
                     → (L : Label X S)
                     → (M : Label X T)
                     → Label X (insertion-tree S p T)
label-from-insertion (Join S₁ S₂) BPHere T L M = M ++l (L ∘ PShift)
label-from-insertion (Join S₁ S₂) (BPExt p) (Susp T) L M PHere = M PHere
label-from-insertion (Join S₁ S₂) (BPExt p) (Susp T) L M (PExt Z) = label-from-insertion S₁ p T (L ∘ PExt) (M ∘ PExt) Z
label-from-insertion (Join S₁ S₂) (BPExt p) (Susp T) L M (PShift Z) = replace-label (L ∘ PShift) (M (PShift PHere)) Z
label-from-insertion (Join S₁ S₂) (BPShift p) T L M PHere = L PHere
label-from-insertion (Join S₁ S₂) (BPShift p) T L M (PExt Z) = L (PExt Z)
label-from-insertion (Join S₁ S₂) (BPShift p) T L M (PShift Z) = label-from-insertion S₂ p T (L ∘ PShift) M Z

label-from-insertion′ : (S : Tree n)
                      → (p : BranchingPoint S d)
                      → (T : Tree m)
                      → .⦃ _ : has-trunk-height d T ⦄
                      → (L : Label X S)
                      → (M : Label X T)
                      → Label X (insertion-tree S p T)
label-from-insertion′ (Join S₁ S₂) BPHere T L M = replace-label (M ++l′ (L ∘ PShift)) (L PHere)
label-from-insertion′ (Join S₁ S₂) (BPExt p) (Susp T) L M PHere = L PHere
label-from-insertion′ (Join S₁ S₂) (BPExt p) (Susp T) L M (PExt Z) = label-from-insertion′ S₁ p T (L ∘ PExt) (M ∘ PExt) Z
label-from-insertion′ (Join S₁ S₂) (BPExt p) (Susp T) L M (PShift Z) = L (PShift Z)
label-from-insertion′ (Join S₁ S₂) (BPShift p) T L M PHere = L PHere
label-from-insertion′ (Join S₁ S₂) (BPShift p) T L M (PExt Z) = L (PExt Z)
label-from-insertion′ (Join S₁ S₂) (BPShift p) T L M (PShift Z) = label-from-insertion′ S₂ p T (L ∘ PShift) M Z

bp-height-<-hob : (p : BranchingPoint S d) → d < height-of-branching p
bp-height-<-hob BPHere = s≤s z≤n
bp-height-<-hob (BPExt p) = s≤s (bp-height-<-hob p)
bp-height-<-hob (BPShift p) = bp-height-<-hob p

prune-tree-lem : (S : Tree n)
               → (p : BranchingPoint S d)
               → has-trunk-height d (n-disc (pred (height-of-branching p)))
prune-tree-lem S p = has-trunk-height-n-disc (≤-pred (bp-height-<-hob p))

prune-tree : (S : Tree n)
           → (p : BranchingPoint S d)
           → Tree (insertion-tree-size S p (n-disc (pred (height-of-branching p))) ⦃ prune-tree-lem S p ⦄)
prune-tree S p = insertion-tree S p (n-disc (pred (height-of-branching p))) ⦃ prune-tree-lem S p ⦄

label-from-prune : (S : Tree n)
                 → (p : BranchingPoint S d)
                 → (L : Label X S)
                 → (M : Label X (n-disc (pred (height-of-branching p))))
                 → Label X (prune-tree S p)
label-from-prune S p L M = label-from-insertion S p (n-disc (pred (height-of-branching p))) ⦃ prune-tree-lem S p ⦄ L M

module _ where
  open ≡-Reasoning
  prune-label : (S : Tree n)
              → (p : BranchingPoint S d)
              → Label (someTree (prune-tree S p)) S
  prune-label {d = d} S p = let
    instance _ = prune-tree-lem S p
    in exterior-label S p (n-disc (pred (height-of-branching p)))
