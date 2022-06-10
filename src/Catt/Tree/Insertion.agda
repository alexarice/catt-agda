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

interior-sub : (S : Tree n) → (p : BranchingPoint S) → (T : Tree m) → .⦃ _ : has-linear-height (bp-height p) T ⦄ → Sub (suc m) (suc (insertion-tree-size S p T)) ⋆
interior-sub (Join S₁ S₂) (BPHere) T = idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _
interior-sub (Join S₁ S₂) (BPExt P) (Join T Sing) = connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂) ∘ suspSub (interior-sub S₁ P T)
interior-sub (Join S₁ S₂) (BPShift P) T = connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ∘ interior-sub S₂ P T

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
exterior-sub-label (Join S₁ S₂) (BPHere) T
  = label-between-connect-trees (to-label (suspTree S₁) (sub-from-linear-tree-unbiased (suspTree S₁) T 0) (someTree T))
                                (id-label S₂)
exterior-sub-label (Join S₁ S₂) (BPExt p) (Join T Sing)
  = label-between-joins (exterior-sub-label S₁ p T) (id-label S₂)
exterior-sub-label (Join S₁ S₂) (BPShift p) T
  = label-between-joins (id-label S₁) (exterior-sub-label S₂ p T)

{-
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

exterior-sub-label : (S : Tree n)
                   → (P : Path S)
                   → .⦃ _ : is-branching-path P ⦄
                   → (T : Tree m)
                   → .⦃ _ : has-linear-height (path-length P) T ⦄
                   → Label (suc (insertion-tree-size S P T)) S
exterior-sub-label (Join S₁ S₂) PHere T
  = label-between-connect-trees (to-label (suspTree S₁) (sub-from-linear-tree-unbiased (suspTree S₁) T 0))
                                (id-label S₂)
                                T
                                S₂
exterior-sub-label (Join S₁ S₂) (PExt P) (Join T Sing)
  = label-between-joins (exterior-sub-label S₁ P T) (id-label S₂) (insertion-tree S₁ P T) S₂
exterior-sub-label (Join S₁ S₂) (PShift P) T
  = label-between-joins (id-label S₁) (exterior-sub-label S₂ P T) S₁ (insertion-tree S₂ P T)
-}
-- exterior-path-func : (S : Tree n)
--                    → (P : Path S)
--                    → .⦃ _ : is-branching-path P ⦄
--                    → (T : Tree m)
--                    → .⦃ _ : has-linear-height (path-length P) T ⦄
--                    → path-func (Path (insertion-tree S P T)) S
-- exterior-path-func (Join S₁ S₂) PHere T Q = POther {!!}
-- exterior-path-func (Join S₁ S₂) (PExt P) T Q = {!!}
-- exterior-path-func (Join S₁ S₂) (PShift P) T Q = {!!}


-- exterior-max-func : (S : Tree n)
--                   → (P : Path S)
--                   → .⦃ _ : is-branching-path P ⦄
--                   → (T : Tree m)
--                   → .⦃ _ : has-linear-height (path-length P) T ⦄
--                   → path-func (Path (insertion-tree S P T)) S
-- exterior-max-func (Join S₁ S₂) PHere T (PExt Q) = POther (unbiased-comp (tree-dim T) T [ label-to-sub (connect-tree-inc-left T S₂) ⋆ ]tm)
-- exterior-max-func (Join S₁ S₂) PHere T (PShift Q) = path-inc-right T Q
-- exterior-max-func (Join S₁ S₂) (PExt P) (Join T Sing) (PExt Q) = PExt (exterior-max-func S₁ P T Q)
-- exterior-max-func (Join S₁ S₂) (PExt P) (Join T Sing) (PShift Q) = PShift {S = insertion-tree S₁ P T} Q
-- exterior-max-func (Join S₁ S₂) (PShift P) T (PExt Q) = PExt {T = insertion-tree S₂ P T} Q
-- exterior-max-func (Join S₁ S₂) (PShift P) T (PShift Q) ⦃ mx ⦄ = PShift (exterior-max-func S₂ P T Q ⦃ proj₂ mx ⦄)

-- sub-from-insertion : (S : Tree n)
--                    → (P : Path S)
--                    → .⦃ bp : is-branching-path P ⦄
--                    → (T : Tree m)
--                    → .⦃ lh : has-linear-height (path-length P) T ⦄
--                    → (σ : Sub (suc n) l A)
--                    → (τ : Sub (suc m) l A)
--                    → Sub (suc (insertion-tree-size S P T)) l A
-- sub-from-insertion (Join S₁ S₂) PHere T σ τ
--   = sub-from-connect τ
--                      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ∘ (idSub≃ (connect-tree-to-ctx T S₂))
-- sub-from-insertion (Join S₁ S₂) (PExt P) (Join T Sing) σ τ
--   = sub-from-connect (unrestrict (sub-from-insertion S₁ P T (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (getFst [ τ ]tm) (getSnd [ τ ]tm))
--                                                              (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
--                      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
-- sub-from-insertion (Join S₁ S₂) (PShift P) T σ τ
--   = sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
--                      (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)

sub-from-insertion-label : (S : Tree n)
                                → (p : BranchingPoint S)
                                → (T : Tree m)
                                → .⦃ lh : has-linear-height (bp-height p) T ⦄
                                → (σ : Label X S)
                                → (τ : Label X T)
                                → Label X (insertion-tree S p T)
sub-from-insertion-label (Join S₁ S₂) BPHere T (LJoin x σ σ′) τ = connect-label τ σ′
sub-from-insertion-label (Join S₁ S₂) (BPExt P) (Join T Sing) (LJoin x σ σ′) (LJoin y τ (LSing z))
  = LJoin y (sub-from-insertion-label S₁ P T σ τ) σ′
sub-from-insertion-label (Join S₁ S₂) (BPShift P) T (LJoin x σ σ′) τ
  = LJoin x σ (sub-from-insertion-label S₂ P T σ′ τ)

sub-from-insertion : (S : Tree n)
                         → (p : BranchingPoint S)
                         → (T : Tree m)
                         → .⦃ lh : has-linear-height (bp-height p) T ⦄
                         → (σ : Sub (suc n) l A)
                         → (τ : Sub (suc m) l A)
                         → Sub (suc (insertion-tree-size S p T)) l A
sub-from-insertion {l = l} {A = A} S P T σ τ
  = label-to-sub (sub-from-insertion-label S P T (to-label S σ (Other l)) (to-label T τ (Other l))) A
