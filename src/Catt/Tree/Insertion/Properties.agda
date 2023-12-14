module Catt.Tree.Insertion.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Globular
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Insertion

open import Relation.Binary

-- branching-path-to-var-is-var : (p : BranchingPoint S d) → isVar (branching-path-to-var p)
-- branching-path-to-var-is-var {S = Join S T} BPHere
--   = var-to-var-comp-tm 0V (connect-susp-inc-left (tree-size S) (tree-size T)) ⦃ connect-susp-inc-left-var-to-var (tree-size S) (tree-size T) ⦄
-- branching-path-to-var-is-var {S = Join S T} (BPExt P)
--   = var-to-var-comp-tm (susp-tm (branching-path-to-var P)) ⦃ susp-tm-var (branching-path-to-var P) ⦃ branching-path-to-var-is-var P ⦄ ⦄ (connect-susp-inc-left (tree-size S) (tree-size T)) ⦃ connect-susp-inc-left-var-to-var (tree-size S) (tree-size T) ⦄
-- branching-path-to-var-is-var {S = Join S T} (BPShift P) = var-to-var-comp-tm (branching-path-to-var P) ⦃ branching-path-to-var-is-var P ⦄ (connect-susp-inc-right (tree-size S) (tree-size T)) ⦃ connect-susp-inc-right-var-to-var (tree-size S) (tree-size T) ⦄

instance
  branching-path-to-path-not-here : {P : BranchingPoint S l} → not-here (branching-path-to-path P)
  branching-path-to-path-not-here {P = BPHere} = tt
  branching-path-to-path-not-here {P = BPExt P} = tt
  branching-path-to-path-not-here {P = BPShift P} = tt

  branching-path-to-path-maximal : {P : BranchingPoint S l} → is-maximal (branching-path-to-path P)
  branching-path-to-path-maximal {P = BPHere} = inst
  branching-path-to-path-maximal {P = BPExt P} = inst
  branching-path-to-path-maximal {P = BPShift P} = build

height-of-branching-non-zero : (S : Tree n) → (p : BranchingPoint S d) → NonZero (height-of-branching p)
height-of-branching-non-zero (Join S T) BPHere = it
height-of-branching-non-zero (Join S T) (BPExt P) = it
height-of-branching-non-zero (Join S T) (BPShift P) = height-of-branching-non-zero T P

height-of-branching->-bp-height : (p : BranchingPoint S l) → l < height-of-branching p
height-of-branching->-bp-height BPHere = s≤s z≤n
height-of-branching->-bp-height (BPExt p) = s≤s (height-of-branching->-bp-height p)
height-of-branching->-bp-height (BPShift p) = height-of-branching->-bp-height p

height-of-branching-linear : (S : Tree n) → .⦃ is-linear S ⦄ → (P : BranchingPoint S l) → height-of-branching P ≡ tree-dim S
height-of-branching-linear (Join S Sing) BPHere = refl
height-of-branching-linear (Join S Sing) (BPExt P) = cong suc (height-of-branching-linear S P)

exterior-label-phere : (S : Tree n)
                     → (p : BranchingPoint S d)
                     → (T : Tree m)
                     → .⦃ _ : has-trunk-height d T ⦄
                     → (As : STy (someTree (chop-trunk d T)))
                     → .⦃ _ : height-of-branching p ≃n d + sty-dim As ⦄
                     → ⦃ 1-Full As ⦄
                     → exterior-label S p T As PHere ≃stm SHere {S = insertion-tree S p T}
exterior-label-phere (Join S₁ S₂) BPHere T A = begin
  < term-to-label (susp-tree S₁) (SCoh T A (SPath ,, S⋆)) A PHere >>= connect-tree-inc-left T S₂ >stm
    ≈⟨ >>=-≃ (term-to-label-1-Full-src (susp-tree S₁) (SCoh T A (SPath ,, S⋆)) A) refl≃l refl≃sty ⟩
  < SPath (connect-tree-inc-left′ T S₂ PHere) >stm
    ≈⟨ SPath≃ (connect-tree-inc-left-phere T S₂) ⟩
  < SHere >stm ∎
  where
    open Reasoning stm-setoid
exterior-label-phere (Join S₁ S₂) (BPExt p) (susp T) A = refl≃stm
exterior-label-phere (Join S₁ S₂) (BPShift p) T A = refl≃stm

label-from-replace-lem : (S : Tree n)
                       → (P : BranchingPoint S l)
                       → (T : Tree m)
                       → (L : Label X S)
                       → (a : STm X)
                       → (M : Label X (susp-tree-n l T))
                     → label-from-insertion S P T (replace-label L a) M ≃lm label-from-insertion S P T L M
label-from-replace-lem (Join S₁ S₂) BPHere T L a M = refl≃lm
label-from-replace-lem (Join S₁ S₂) (BPExt P) T L a M .get (PExt Z) = refl≃stm
label-from-replace-lem (Join S₁ S₂) (BPExt P) T L a M .get (PShift Z) = refl≃stm
label-from-replace-lem (Join S₁ S₂) (BPShift P) T L a M .get (PExt Z) = refl≃stm
label-from-replace-lem (Join S₁ S₂) (BPShift P) T L a M .get (PShift Z) = refl≃stm

module _ where
  open Reasoning stm-setoid

  exterior-label-last-path : (S : Tree n)
                           → (p : BranchingPoint S d)
                           → (T : Tree m)
                           → (As : STy (someTree T))
                           → .⦃ _ : height-of-branching p ≃n d + sty-dim As ⦄
                           → ⦃ _ : 1-Full As ⦄
                           → exterior-label S p T As (last-path S) ≃stm SPath (last-path (insertion-tree S p T))
  exterior-label-last-path (Join S₁ S₂) (BPExt p) T As = compute-≃ refl≃stm
  exterior-label-last-path (Join S₁ S₂) (BPShift p) T As = compute-≃ (SShift≃ refl≃ (exterior-label-last-path S₂ p T As))
  exterior-label-last-path (Join S₁ Sing) BPHere T As = begin
    < term-to-label (susp-tree S₁) (SCoh T As (SPath ,, S⋆)) As (PShift PHere) >>= connect-tree-inc-left T Sing >stm
      ≈⟨ >>=-≃ (term-to-label-1-Full-tgt (susp-tree S₁) (SCoh T As (SPath ,, S⋆)) As) refl≃l refl≃sty ⟩
    < SPath (connect-tree-inc-left′ T Sing (last-path T)) >stm
      ≈⟨ SPath≃ (connect-tree-inc-phere T Sing) ⟩
    < SPath (connect-tree-inc-right′ T Sing PHere) >stm
      ≈⟨ SPath≃ (connect-tree-inc-right-last-path T Sing) ⟩
    < SPath (last-path (connect-tree T Sing)) >stm ∎
  exterior-label-last-path (Join S₁ S₂@(Join S₃ S₄)) BPHere T As = SPath≃ (connect-tree-inc-right-last-path T S₂)

  interior-label-comm : (S : Tree n)
                      → (p : BranchingPoint S d)
                      → (T : Tree m)
                      → (L : Label X S)
                      → (M : Label X (susp-tree-n d T))
                      → (As : STy X)
                      → interior-label S p T ●l (label-from-insertion S p T L M ,, As) ≃lm M
  interior-label-comm (Join S₁ S₂) BPHere T L M A .get Z = connect-label-inc-left M (L ∘ PShift) A .get Z
  interior-label-comm (Join S₁ S₂) (BPExt p) T L M A .get (PExt Z)
    = interior-label-comm S₁ p T (L ∘ PExt) (M ∘ PExt) _ .get Z
  interior-label-comm (Join S₁ S₂) (BPExt p) T L M A .get (PShift PHere) = ⊥-elim it
  interior-label-comm (Join S₁ S₂) (BPShift p) T L M = interior-label-comm S₂ p T (L ∘ PShift) M

  exterior-label-comm : (S : Tree n)
                      → (p : BranchingPoint S d)
                      → (T : Tree m)
                      → (L : Label X S)
                      → (M : Label X (susp-tree-n d T))
                      → (As : STy (someTree T))
                      → .⦃ _ : height-of-branching p ≃n d + sty-dim As ⦄
                      → ⦃ 1-Full As ⦄
                      → (Bs : STy X)
                      → L (branching-path-to-path p) ≃stm SCoh (susp-tree-n d T) (map-sty-ext-n d As) (M ,, Bs)
                      → exterior-label S p T As ●l (label-from-insertion S p T L M ,, Bs) ≃lm L
  exterior-label-comm (Join S₁ S₂) BPHere T L M As Bs q .get (PExt Z) = begin
    < term-to-label (susp-tree S₁) (SCoh T As (SPath ,, S⋆)) As (PExt Z)
      >>= connect-tree-inc-left T S₂
      >>= (connect-label M (L ∘ PShift) ,, Bs) >stm
      ≈⟨ >>=-assoc (term-to-label (susp-tree S₁) (SCoh T As (SPath ,, S⋆)) As (PExt Z))
                   (connect-tree-inc-left T S₂)
                   ((connect-label M (L ∘ PShift) ,, Bs)) ⟩
    < term-to-label (susp-tree S₁) (SCoh T As (SPath ,, S⋆)) As (PExt Z)
      >>= connect-tree-inc-left T S₂ ●lt (connect-label M (λ x → L (PShift x)) ,, Bs) >stm
      ≈⟨ >>=-≃ (term-to-label-max (susp-tree S₁) (SCoh T As (id-label-wt T)) As (PExt Z)) (connect-label-inc-left M (L ∘ PShift) Bs) refl≃sty ⟩
    < SCoh T As (M ,, Bs) >stm
      ≈˘⟨ q ⟩
    < L (PExt (is-linear-max-path S₁)) >stm
      ≈⟨ ap-≃ (refl≃l {L = L ∘ PExt}) (max-path-lin-tree S₁ Z refl≃) ⟩
    < L (PExt Z) >stm ∎
  exterior-label-comm (Join S₁ S₂) BPHere T L M As Bs q .get (PShift Z) = begin
    < replace-label (ap (connect-tree-inc-right T S₂))
                    (term-to-label (susp-tree S₁)
                                   (SCoh T As (SPath ,, S⋆))
                                   As
                                   (PShift PHere)
                                   >>= connect-tree-inc-left T S₂)
                    Z
      >>= (connect-label M (L ∘ PShift) ,, Bs) >stm
      ≈⟨ >>=-≃ (replace-not-here (ap (connect-tree-inc-right T S₂)) _ Z) refl≃l refl≃sty ⟩
    < connect-label M (L ∘ PShift) (connect-tree-inc-right′ T S₂ Z) >stm
      ≈⟨ connect-label-inc-right M (L ∘ PShift) Bs Z ⟩
    < L (PShift Z) >stm ∎
  exterior-label-comm (Join S₁ S₂) (BPExt p) T L M As Bs q .get (PExt Z) = exterior-label-comm S₁ p T (L ∘ PExt) (M ∘ PExt) As _ lem .get Z
    where
      lem : L (PExt (branching-path-to-path p))
            ≃stm
            (SCoh (susp-tree-n _ T)
                  (map-sty-ext-n _ As)
                  (M ∘ PExt ,, SArr (M PHere) Bs (M (PShift PHere))))
      lem = begin
        < L (PExt (branching-path-to-path p)) >stm
          ≈⟨ q ⟩
        < SCoh (susp-tree-n (suc _) T) (map-sty-ext-n (suc _) As) (M ,, Bs) >stm
          ≈⟨ SCoh≃ (susp-tree-n (suc _) T)
                   (map-sty-ext-susp-compat (map-sty-ext-n _ As))
                   (unrestrict-label-prop (M ,, Bs))
                   refl≃sty ⟩
        < SCoh (susp-tree-n (suc _) T) (susp-sty (map-sty-ext-n _ As)) _ >stm
          ≈˘⟨ SCoh-unrestrict (susp-tree-n _ T) (map-sty-ext-n _ As) _ ⟩
        < SCoh (susp-tree-n _ T)
               (map-sty-ext-n _ As)
               (M ∘ PExt ,, SArr (label-from-insertion (Join S₁ S₂) (BPExt p) T L M PHere)
                                 Bs
                                 (label-from-insertion (Join S₁ S₂) (BPExt p) T L M (PShift PHere))) >stm ∎
  exterior-label-comm (Join S₁ S₂) (BPExt p) T L M As Bs q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
  exterior-label-comm (Join S₁ S₂) (BPShift p) T L M As Bs q .get (PExt Z) = refl≃stm
  exterior-label-comm (Join S₁ S₂) (BPShift p) T L M As Bs q .get (PShift Z) = exterior-label-comm S₂ p T (L ∘ PShift) M As Bs q .get Z

disc-insertion : (S : Tree n)
               → .⦃ is-linear S ⦄
               → (P : BranchingPoint S l)
               → (T : Tree m)
               → insertion-tree S P T ≃′ susp-tree-n l T
disc-insertion (Join S Sing) BPHere T = connect-tree-right-unit T
disc-insertion (Join S Sing) (BPExt P) T = Join≃′ (disc-insertion S P T) Refl≃′

disc-interior : (S : Tree n)
              → .⦃ is-linear S ⦄
              → (P : BranchingPoint S l)
              → (T : Tree m)
              → interior-label S P T ≃l id-label (susp-tree-n l T)
disc-interior (Join S Sing) BPHere T .get Z = SPath≃ (connect-tree-inc-left-unit T .get Z)
disc-interior (Join S Sing) (BPExt P) T .get PHere = SPath≃ (Here≃ (≃′-to-≃ (Join≃′ (disc-insertion S P T) Refl≃′)))
disc-interior (Join S Sing) (BPExt P) T .get (PExt Z) = compute-≃ (SExt≃ (disc-interior S P T .get Z) refl≃)
disc-interior (Join S Sing) (BPExt P) T .get (PShift PHere) = compute-≃ (SShift≃ (≃′-to-≃ (disc-insertion S P T)) refl≃stm)

disc-label-from : (S : Tree n)
              → .⦃ _ : is-linear S ⦄
              → (P : BranchingPoint S l)
              → (T : Tree m)
              → (L : Label X S)
              → (M : Label X (susp-tree-n l T))
              → label-from-insertion S P T L M ≃l label-≃ (disc-insertion S P T) M
disc-label-from (Join S Sing) BPHere T L M = connect-label-right-unit M (L ∘ PShift)
disc-label-from (Join S Sing) (BPExt P) T L M .get PHere = refl≃stm
disc-label-from (Join S Sing) (BPExt P) T L M .get (PExt Z) = disc-label-from S P T (L ∘ PExt) (M ∘ PExt) .get Z
disc-label-from (Join S Sing) (BPExt P) T L M .get (PShift PHere) = refl≃stm

insertion-disc : (S : Tree n)
               → (p : BranchingPoint S l)
               → insertion-tree S p (n-disc (height-of-branching p ∸ l)) ≃′ S
insertion-disc (Join S₁ S₂) BPHere = Join≃′ (linear-tree-unique (n-disc (tree-dim S₁)) S₁ (≃n-to-≡ (tree-dim-n-disc (tree-dim S₁)))) refl≃′
insertion-disc (Join S₁ S₂) (BPExt p) = Join≃′ (insertion-disc S₁ p) refl≃′
insertion-disc (Join S₁ S₂) (BPShift p) = Join≃′ refl≃′ (insertion-disc S₂ p)

disc-sub-from-2 : (S : Tree n)
                → (p : BranchingPoint S l)
                → (L : Label X S)
                → (M : Label X (susp-tree-n l (n-disc (height-of-branching p ∸ l))))
                → L (branching-path-to-path p) ≃stm M (is-linear-max-path (susp-tree-n l (n-disc (height-of-branching p ∸ l)))
                                                                          ⦃ susp-tree-n-linear l _ ⦄)
                → label-from-insertion S p (n-disc (height-of-branching p ∸ l)) L M ≃lm label-≃ (insertion-disc S p) L
disc-sub-from-2 (Join S T) BPHere L M q .get (PExt Z) = begin
  < M (PExt Z) >stm
    ≈˘⟨ ap-≃ (refl≃l {L = M}) (max-path-lin-tree (n-disc (suc (tree-dim S))) (PExt Z) refl≃) ⟩
  < M (is-linear-max-path (n-disc (suc (tree-dim S)))) >stm
    ≈˘⟨ q ⟩
  < L (PExt (is-linear-max-path S)) >stm
    ≈⟨ ap-≃ (refl≃l {L = L})
            (Ext≃ (trans≃p (max-path-lin-tree S Z (≃′-to-≃ (linear-tree-unique S (n-disc (tree-dim S))
                                                                                 (sym (≃n-to-≡ (tree-dim-n-disc (tree-dim S)))))))
                           (ppath-≃-≃p (linear-tree-unique (n-disc (tree-dim S)) S _) Z)) refl≃) ⟩
  < L (PExt (ppath-≃ (linear-tree-unique (n-disc (tree-dim S)) S _) Z)) >stm ∎
  where
    open Reasoning stm-setoid
disc-sub-from-2 (Join S T) BPHere L M q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
disc-sub-from-2 (Join S T) (BPExt p) L M q .get (PExt Z) = disc-sub-from-2 S p (L ∘ PExt) (M ∘ PExt) q .get Z
disc-sub-from-2 (Join S T) (BPExt p) L M q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
disc-sub-from-2 (Join S T) (BPShift p) L M q .get (PExt Z) = refl≃stm
disc-sub-from-2 (Join S T) (BPShift p) L M q .get (PShift Z) = disc-sub-from-2 T p (L ∘ PShift) M q .get Z

label-from-insertion-map : (f : STm X → STm Y)
                         → (S : Tree n)
                         → (p : BranchingPoint S l)
                         → (T : Tree m)
                         → (L : Label X S)
                         → (M : Label X (susp-tree-n l T))
                         → (f ∘ label-from-insertion S p T L M) ≃l label-from-insertion S p T (f ∘ L) (f ∘ M)
label-from-insertion-map f (Join S₁ S₂) BPHere T L M = connect-label-map f M (L ∘ PShift)
label-from-insertion-map f (Join S₁ S₂) (BPExt p) T L M .get PHere = refl≃stm
label-from-insertion-map f (Join S₁ S₂) (BPExt p) T L M .get (PExt Z) = label-from-insertion-map f S₁ p T (L ∘ PExt) (M ∘ PExt) .get Z
label-from-insertion-map f (Join S₁ S₂) (BPExt p) T L M .get (PShift Z) = replace-label-map f (L ∘ PShift) (M (PShift PHere)) .get Z
label-from-insertion-map f (Join S₁ S₂) (BPShift p) T L M .get PHere = refl≃stm
label-from-insertion-map f (Join S₁ S₂) (BPShift p) T L M .get (PExt Z) = refl≃stm
label-from-insertion-map f (Join S₁ S₂) (BPShift p) T L M .get (PShift Z) = label-from-insertion-map f S₂ p T (L ∘ PShift) M .get Z

-- exterior-interior-prop : (S : Tree n)
--                        → (p : BranchingPoint S l)
--                        → (T : Tree m)
--                        → .⦃ _ : has-linear-height (bp-height p) T ⦄
--                        → label-from-insertion S p T (exterior-label S p T) (interior-label S p T) ≃l id-label (insertion-tree S p T)
-- exterior-interior-prop (Join S₁ S₂) BPHere T = begin
--   < connect-label (ap (connect-tree-inc-left T S₂))
--       (λ x → replace-label (ap (connect-tree-inc-right T S₂))
--                            (SPath (connect-tree-inc-left′ T S₂ (last-path T))) x) >l
--     ≈⟨ connect-label-≃ (refl≃l {L = ap (connect-tree-inc-left T S₂)}) (replace-label-prop (ap (connect-tree-inc-right T S₂)) (SPath (connect-tree-inc-left′ T S₂ (last-path T))) (SPath≃ (connect-tree-inc-phere T S₂))) ⟩
--   < connect-label (ap (connect-tree-inc-left T S₂)) (ap (connect-tree-inc-right T S₂)) >l
--     ≈⟨ connect-label-prop T S₂ ⟩
--   < id-label (connect-tree T S₂) >l ∎
--   where
--     open Reasoning (label-setoid (connect-tree T S₂))
-- exterior-interior-prop (Join S₁ S₂) (BPExt p) (Join T Sing) .get PHere = refl≃stm
-- exterior-interior-prop (Join S₁ S₂) (BPExt p) (Join T Sing) .get (PExt Z) = begin
--   < label-from-insertion S₁ p T
--       (SExt ∘ exterior-label S₁ p T)
--       (SExt ∘ interior-label S₁ p T) Z >stm
--     ≈˘⟨ label-from-insertion-map SExt S₁ p T (exterior-label S₁ p T) (interior-label S₁ p T) .get Z ⟩
--   < (SExt ∘ label-from-insertion S₁ p T (exterior-label S₁ p T) (interior-label S₁ p T)) Z >stm
--     ≈⟨ compute-≃ (SExt≃ (exterior-interior-prop S₁ p T .get Z) refl≃) ⟩
--   < SPath (PExt Z) >stm ∎
--   where
--     open Reasoning stm-setoid
-- exterior-interior-prop (Join S₁ S₂) (BPExt p) (Join T Sing) .get (PShift Z) = compute-≃ (compute-stm-≃ (replace-label-prop (SShift ∘ id-label S₂) (SShift SHere) refl≃stm .get Z))
-- exterior-interior-prop (Join S₁ S₂) (BPShift p) T .get PHere = refl≃stm
-- exterior-interior-prop (Join S₁ S₂) (BPShift p) T .get (PExt Z) = compute-≃ refl≃stm
-- exterior-interior-prop (Join S₁ S₂) (BPShift p) T .get (PShift Z) = begin
--   < label-from-insertion S₂ p T
--       (SShift ∘ exterior-label S₂ p T)
--       (SShift ∘ interior-label S₂ p T) Z >stm
--     ≈˘⟨ label-from-insertion-map SShift S₂ p T (exterior-label S₂ p T) (interior-label S₂ p T) .get Z ⟩
--   < (SShift ∘ label-from-insertion S₂ p T (exterior-label S₂ p T) (interior-label S₂ p T)) Z >stm
--     ≈⟨ compute-≃ (SShift≃ refl≃ (exterior-interior-prop S₂ p T .get Z )) ⟩
--   < SPath (PShift Z) >stm ∎
--   where
--     open Reasoning stm-setoid

exterior-branching-path : (S : Tree n)
                        → (p : BranchingPoint S l)
                        → (T : Tree m)
                        → (Bs : STy (someTree T))
                        → .⦃ _ : height-of-branching p ≃n l + sty-dim Bs ⦄
                        → exterior-label S p T Bs (branching-path-to-path p)
                          ≃stm
                          SCoh (susp-tree-n l T) (map-sty-ext-n l Bs) (interior-label S p T ,, S⋆)
exterior-branching-path (Join S₁ S₂) BPHere T Bs
  = >>=-≃ (term-to-label-max (susp-tree S₁) (SCoh T Bs (id-label-wt T)) Bs (is-linear-max-path (susp-tree S₁)) ⦃ inst ⦄)
          refl≃l
          refl≃sty
exterior-branching-path (Join S₁ S₂) (BPExt p) T Bs = begin
  < SExt (exterior-label S₁ p T Bs (branching-path-to-path p)) >stm
    ≈⟨ SExt≃ (exterior-branching-path S₁ p T Bs) refl≃ ⟩
  < SExt (SCoh (susp-tree-n _ T) (map-sty-ext-n _ Bs) (interior-label S₁ p T ,, S⋆)) >stm
    ≈˘⟨ SCoh-ext (susp-tree-n _ T) (map-sty-ext-n _ Bs) (interior-label S₁ p T ,, S⋆) ⟩
  < SCoh (susp-tree-n _ T) (map-sty-ext-n _ Bs) (map-ext (interior-label S₁ p T ,, S⋆)) >stm
    ≈⟨ SCoh-unrestrict (susp-tree-n _ T) (map-sty-ext-n _ Bs) (map-ext (interior-label S₁ p T ,, S⋆)) ⟩
  < SCoh (susp-tree (susp-tree-n _ T))
         (susp-sty (map-sty-ext-n _ Bs))
         (unrestrict-label (map-ext (interior-label S₁ p T ,, S⋆)) ,, S⋆) >stm
    ≈˘⟨ SCoh≃ (susp-tree (susp-tree-n _ T))
              (map-sty-ext-susp-compat (map-sty-ext-n _ Bs))
              refl≃l
              refl≃sty ⟩
  < SCoh (susp-tree (susp-tree-n _ T)) (map-sty-ext (map-sty-ext-n _ Bs)) (interior-label (Join S₁ S₂) (BPExt p) T ,, S⋆) >stm ∎
  where
    open Reasoning stm-setoid
exterior-branching-path (Join S₁ S₂) (BPShift p) T Bs = begin
  < SShift (exterior-label S₂ p T Bs (branching-path-to-path p)) >stm
    ≈⟨ SShift≃ refl≃ (exterior-branching-path S₂ p T Bs) ⟩
  < SShift (SCoh (susp-tree-n _ T) (map-sty-ext-n _ Bs) (interior-label S₂ p T ,, S⋆)) >stm
    ≈˘⟨ SCoh-shift (susp-tree-n _ T) (map-sty-ext-n _ Bs) (interior-label S₂ p T ,, S⋆) ⟩
  < SCoh (susp-tree-n _ T) (map-sty-ext-n _ Bs) (map-shift (interior-label S₂ p T ,, S⋆)) >stm ∎
  where
    open Reasoning stm-setoid

insertion-parallel : (S : Tree n)
                   → (P : BranchingPoint S l)
                   → (Q : BranchingPoint S l′)
                   → (T : Tree m)
                   → branching-path-to-path P ≃p branching-path-to-path Q
                   → insertion-tree S P T ≃′ insertion-tree S Q T
insertion-parallel (Join S₁ S₂) BPHere BPHere T p = Refl≃′
insertion-parallel (Join S₁ S₂) BPHere (BPExt Q) T p = {!!}
-- Join≃′ (sym≃′ (disc-insertion S₁ Q T)) Refl≃′
insertion-parallel (Join S₁ S₂) (BPExt P) BPHere T p = {!!} -- Join≃′ (disc-insertion S₁ P T) Refl≃′
insertion-parallel (Join S₁ S₂) (BPExt P) (BPExt Q) T p = Join≃′ (insertion-parallel S₁ P Q T (proj-ext p)) Refl≃′
insertion-parallel (Join S₁ S₂) (BPShift P) (BPShift Q) T p = Join≃′ Refl≃′ (insertion-parallel S₂ P Q T (proj-shift p))

-- exterior-parallel : (S : Tree n)
--                   → (P : BranchingPoint S l)
--                   → (Q : BranchingPoint S l′)
--                   → (T : Tree m)
--                   → .⦃ _ : has-linear-height (bp-height P) T ⦄
--                   → .⦃ _ : has-linear-height (bp-height Q) T ⦄
--                   → branching-path-to-path P ≃p branching-path-to-path Q
--                   → exterior-label S P T ≃lm exterior-label S Q T
-- exterior-parallel (Join S₁ S₂) BPHere BPHere T p = refl≃lm
-- exterior-parallel (Join S₁ S₂) BPHere (BPExt Q) (Join T Sing) p .get (PExt Z) = begin
--   < label-from-linear-tree-unbiased S₁ (Join T Sing) 1 Z >>= connect-tree-inc-left (Join T Sing) S₂ >stm
--     ≈⟨ >>=-≃ (lfltu-maximal-path S₁ (Join T Sing) 1 Z) refl≃l refl≃sty ⟩
--   < unbiased-comp′ (tree-dim S₁) T >>=
--         (SPath ∘ PExt ,, SArr (SPath PHere) S⋆ (SPath (PShift PHere))) >stm
--     ≈⟨ >>=-≃ (refl≃stm {a = unbiased-comp′ (tree-dim S₁) T}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
--   < unbiased-comp′ (tree-dim S₁) T >>= map-ext (id-label-wt T) >stm
--     ≈⟨ >>=-ext (unbiased-comp′ (tree-dim S₁) T) (id-label-wt T) ⟩
--   < SExt (unbiased-comp′ (tree-dim S₁) T >>= id-label-wt T) >stm
--     ≈˘⟨ SExt≃ (>>=-≃ (unbiased-comp′-≃ (height-of-branching-linear S₁ Q) refl≃) (disc-interior S₁ Q T) (S⋆-≃ (≃′-to-≃ (disc-insertion S₁ Q T)))) refl≃ ⟩
--   < SExt (unbiased-comp′ (height-of-branching Q) T >>= (interior-label S₁ Q T ,, S⋆)) >stm
--     ≈˘⟨ SExt≃ (exterior-branching-path S₁ Q T) refl≃ ⟩
--   < SExt (exterior-label S₁ Q T (branching-path-to-path Q)) >stm
--     ≈⟨ SExt≃ (ap-≃ (refl≃l {L = exterior-label S₁ Q T}) (max-path-unique S₁ (branching-path-to-path Q) ⦃ branching-path-to-path-maximal Q ⦄ Z )) refl≃ ⟩
--   < SExt (exterior-label S₁ Q T Z) >stm ∎
--   where
--     open Reasoning stm-setoid
-- exterior-parallel (Join S₁ S₂) BPHere (BPExt Q) (Join T Sing) p .get (PShift Z) = trans≃stm (replace-not-here (SPath ∘ PShift) (SPath (PShift PHere)) Z) (trans≃stm (SPath≃ (Shift≃ (sym≃ (≃′-to-≃ (disc-insertion S₁ Q T))) refl≃p)) (compute-≃ refl≃stm))
-- exterior-parallel (Join S₁ S₂) (BPExt P) BPHere (Join T Sing) p .get (PExt Z) = sym≃stm (exterior-parallel (Join S₁ S₂) BPHere (BPExt P) (Join T Sing) (sym≃p p) .get (PExt Z))
-- exterior-parallel (Join S₁ S₂) (BPExt P) BPHere (Join T Sing) p .get (PShift Z) = sym≃stm (exterior-parallel (Join S₁ S₂) BPHere (BPExt P) (Join T Sing) (sym≃p p) .get (PShift Z))
-- exterior-parallel (Join S₁ S₂) (BPExt P) (BPExt Q) (Join T Sing) p .get (PExt Z) = SExt≃ (exterior-parallel S₁ P Q T (proj-ext p) .get Z) refl≃
-- exterior-parallel (Join S₁ S₂) (BPExt P) (BPExt Q) (Join T Sing) p .get (PShift Z) = SShift≃ (≃′-to-≃ (insertion-parallel S₁ P Q T (proj-ext p))) refl≃stm
-- exterior-parallel (Join S₁ S₂) (BPShift P) (BPShift Q) T p .get (PExt Z) = SExt≃ refl≃stm (≃′-to-≃ (insertion-parallel S₂ P Q T (proj-shift p)))
-- exterior-parallel (Join S₁ S₂) (BPShift P) (BPShift Q) T p .get (PShift Z) = SShift≃ refl≃ (exterior-parallel S₂ P Q T (proj-shift p) .get Z)

-- parallel-sub-from : (S : Tree n)
--                   → (P : BranchingPoint S l)
--                   → (Q : BranchingPoint S l′)
--                   → (T : Tree m)
--                   → .⦃ _ : has-linear-height (bp-height P) T ⦄
--                   → .⦃ _ : has-linear-height (bp-height Q) T ⦄
--                   → (p : branching-path-to-path P ≃p branching-path-to-path Q)
--                   → (L : Label X S)
--                   → (M : Label X T)
--                   → label-from-insertion S P T L M ≃lm label-≃ (insertion-parallel S P Q T p) (label-from-insertion S Q T L M)
-- parallel-sub-from (Join S₁ S₂) BPHere BPHere T p L M = refl≃lm
-- parallel-sub-from (Join S₁ S₂) BPHere (BPExt Q) (Join T Sing) p L M .get (PExt Z) = sym≃stm (label-≃-sym (disc-insertion S₁ Q T) (disc-sub-from S₁ Q T (L ∘ PExt) (M ∘ PExt)) .get Z)
-- parallel-sub-from (Join S₁ S₂) BPHere (BPExt Q) (Join T Sing) p L M .get (PShift Z) = refl≃stm
-- parallel-sub-from (Join S₁ S₂) (BPExt P) BPHere (Join T Sing) p L M .get (PExt Z) = disc-sub-from S₁ P T (L ∘ PExt) (M ∘ PExt) .get Z
-- parallel-sub-from (Join S₁ S₂) (BPExt P) BPHere (Join T Sing) p L M .get (PShift Z) = refl≃stm
-- parallel-sub-from (Join S₁ S₂) (BPExt P) (BPExt Q) (Join T Sing) p L M .get (PExt Z) = parallel-sub-from S₁ P Q T (proj-ext p) (L ∘ PExt) (M ∘ PExt) .get Z
-- parallel-sub-from (Join S₁ S₂) (BPExt P) (BPExt Q) (Join T Sing) p L M .get (PShift Z) = refl≃stm
-- parallel-sub-from (Join S₁ S₂) (BPShift P) (BPShift Q) T p L M .get (PExt Z) = refl≃stm
-- parallel-sub-from (Join S₁ S₂) (BPShift P) (BPShift Q) T p L M .get (PShift Z) = parallel-sub-from S₂ P Q T (proj-shift p) (L ∘ PShift) M .get Z

{-
label-from-insertion-≃ : (S : Tree n)
                        → (p : BranchingPoint S d)
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height d T ⦄
                        → {L : Label X S}
                        → {L′ : Label Y S}
                        → {M : Label X T}
                        → {M′ : Label Y T}
                        → L ≃l L′
                        → M ≃l M′
                        → label-from-insertion S p T L M ≃l label-from-insertion S p T L′ M′
label-from-insertion-≃ (Join S₁ S₂) BPHere T p q = connect-label-≃ q [ (λ P → p .get (PShift P)) ]
label-from-insertion-≃ (Join S₁ S₂) (BPExt P) (Join T Sing) p q .get PHere = q .get PHere
label-from-insertion-≃ (Join S₁ S₂) (BPExt P) (Join T Sing) p q .get (PExt Z) = label-from-insertion-≃ S₁ P T [ (λ Z → p .get (PExt Z)) ] [ (λ Z → q .get (PExt Z)) ] .get Z
label-from-insertion-≃ (Join S₁ S₂) (BPExt P) (Join T Sing) p q .get (PShift Z) = replace-label-≃ [ (λ Z → p .get (PShift Z)) ] (q .get (PShift PHere)) .get Z
label-from-insertion-≃ (Join S₁ S₂) (BPShift P) T p q .get PHere = p .get PHere
label-from-insertion-≃ (Join S₁ S₂) (BPShift P) T p q .get (PExt Z) = p .get (PExt Z)
label-from-insertion-≃ (Join S₁ S₂) (BPShift P) T p q .get (PShift Z) = label-from-insertion-≃ S₂ P T [ (λ Z → p .get (PShift Z)) ] q .get Z

connect-bp-left : (S : Tree n)
                → (T : Tree m)
                → (P : BranchingPoint S l)
                → BranchingPoint (connect-tree S T) l
connect-bp-left (Join S₁ S₂) T BPHere = BPHere
connect-bp-left (Join S₁ S₂) T (BPExt P) = BPExt P
connect-bp-left (Join S₁ S₂) T (BPShift P) = BPShift (connect-bp-left S₂ T P)

connect-bp-left-prop : (S : Tree n)
                     → (T : Tree m)
                     → (P : BranchingPoint S l)
                     → SPath (branching-path-to-path (connect-bp-left S T P))
                     ≃stm ap (connect-tree-inc-left S T) (branching-path-to-path P)
connect-bp-left-prop (Join S₁ S₂) T BPHere = refl≃stm
connect-bp-left-prop (Join S₁ S₂) T (BPExt P) = refl≃stm
connect-bp-left-prop (Join S₁ S₂) T (BPShift P) = compute-≃ (SShift≃ refl≃ (connect-bp-left-prop S₂ T P))

insertion-bp-left : (S : Tree n)
                  → (T : Tree m)
                  → (P : BranchingPoint S l)
                  → (U : Tree n′)
                  → .⦃ _ : has-linear-height l U ⦄
                  → insertion-tree (connect-tree S T) (connect-bp-left S T P) U ≃′ connect-tree (insertion-tree S P U) T
insertion-bp-left (Join S₁ S₂) T BPHere U = connect-tree-assoc U S₂ T
insertion-bp-left (Join S₁ S₂) T (BPExt P) (Join U Sing) = refl≃′
insertion-bp-left (Join S₁ S₂) T (BPShift P) U = Join≃′ refl≃′ (insertion-bp-left S₂ T P U)

exterior-bp-left-inc-left : (S : Tree n)
                          → (T : Tree m)
                          → (P : BranchingPoint S l)
                          → (U : Tree n′)
                          → .⦃ _ : has-linear-height l U ⦄
                          → ap (connect-tree-inc-left S T) ●l (exterior-label (connect-tree S T) (connect-bp-left S T P) U ,, S⋆)
                          ≃l exterior-label S P U ●l (connect-tree-inc-left (insertion-tree S P U) T)
exterior-bp-left-inc-left (Join S₁ S₂) T BPHere U .get PHere = SPath≃ (begin
  < connect-tree-inc-left′ U (connect-tree S₂ T) PHere >p
    ≈⟨ connect-tree-inc-left-phere U (connect-tree S₂ T) ⟩
  < PHere >p
    ≈⟨ Here≃ (≃′-to-≃ (connect-tree-assoc U S₂ T)) ⟩
  < PHere >p
    ≈˘⟨ connect-tree-inc-left-phere (connect-tree U S₂) T ⟩
  < connect-tree-inc-left′ (connect-tree U S₂) T PHere >p
    ≈˘⟨ ap′-≃ (connect-tree-inc-left′ (connect-tree U S₂) T) (connect-tree-inc-left-phere U S₂) ⟩
  < connect-tree-inc-left′ (connect-tree U S₂) T
      (connect-tree-inc-left′ U S₂ PHere) >p ∎)
  where
    open Reasoning path-setoid
exterior-bp-left-inc-left (Join S₁ S₂) T BPHere U .get (PExt Z) = begin
  < label-from-linear-tree-unbiased S₁ U 1 Z
    >>= connect-tree-inc-left U (connect-tree S₂ T) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = label-from-linear-tree-unbiased S₁ U 1 Z}) [ (λ P → SPath≃ (connect-tree-inc-left-assoc U S₂ T .get P)) ] (S⋆-≃ (≃′-to-≃ (sym≃′ (connect-tree-assoc U S₂ T)))) ⟩
  < label-from-linear-tree-unbiased S₁ U 1 Z
    >>= connect-tree-inc-left U S₂ ●lt connect-tree-inc-left (connect-tree U S₂) T >stm
    ≈˘⟨ >>=-assoc (label-from-linear-tree-unbiased S₁ U 1 Z) (connect-tree-inc-left U S₂) (connect-tree-inc-left (connect-tree U S₂) T) ⟩
  < label-from-linear-tree-unbiased S₁ U 1 Z
    >>= connect-tree-inc-left U S₂
    >>= connect-tree-inc-left (connect-tree U S₂) T >stm ∎
  where
    open Reasoning stm-setoid
exterior-bp-left-inc-left (Join S₁ S₂) T BPHere U .get (PShift Z) = begin
  < replace-label
       (ap (connect-tree-inc-right U (connect-tree S₂ T)))
       (SPath (connect-tree-inc-left′ U (connect-tree S₂ T) (last-path U)))
       (connect-tree-inc-left′ S₂ T Z) >stm
    ≈⟨ replace-label-prop (ap (connect-tree-inc-right U (connect-tree S₂ T))) _ (SPath≃ (connect-tree-inc-phere U (connect-tree S₂ T))) .get (connect-tree-inc-left′ S₂ T Z) ⟩
  < ap (connect-tree-inc-right U (connect-tree S₂ T)) (connect-tree-inc-left′ S₂ T Z) >stm
    ≈⟨ SPath≃ (connect-tree-inc-assoc U S₂ T .get Z) ⟩
  < SPath (connect-tree-inc-left′ (connect-tree U S₂) T (connect-tree-inc-right′ U S₂ Z)) >stm
    ≈˘⟨ >>=-≃ (replace-label-prop _ _ (SPath≃ (connect-tree-inc-phere U S₂)) .get Z) refl≃l refl≃sty ⟩
  < replace-label (ap (connect-tree-inc-right U S₂))
        (SPath (connect-tree-inc-left′ U S₂ (last-path U))) Z
        >>=
        connect-tree-inc-left (connect-tree U S₂) T >stm ∎
  where
    open Reasoning stm-setoid
exterior-bp-left-inc-left (Join S₁ S₂) T (BPExt P) (Join U Sing) .get PHere = refl≃stm
exterior-bp-left-inc-left (Join S₁ S₂) T (BPExt P) (Join U Sing) .get (PExt Z) = begin
  < SExt (exterior-label S₁ P U Z) >stm
    ≈˘⟨ SExt≃ (>>=-id (exterior-label S₁ P U Z)) refl≃ ⟩
  < SExt (exterior-label S₁ P U Z >>= id-label-wt (insertion-tree S₁ P U)) >stm
    ≈˘⟨ >>=-ext (exterior-label S₁ P U Z) (id-label-wt (insertion-tree S₁ P U)) ⟩
  < exterior-label S₁ P U Z >>= map-ext {T = connect-tree S₂ T} (id-label-wt (insertion-tree S₁ P U)) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = exterior-label S₁ P U Z}) [ (λ Z → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ (SShift≃ refl≃ (SPath≃ (connect-tree-inc-left-phere S₂ T))))) ⟩
  < exterior-label S₁ P U Z >>= (SPath ∘ PExt ,, SArr (SPath PHere) S⋆ (SPath (PShift (connect-tree-inc-left′ S₂ T PHere)))) >stm ∎
  where
    open Reasoning stm-setoid
exterior-bp-left-inc-left (Join S₁ S₂) T (BPExt P) (Join U Sing) .get (PShift Z) = compute-≃ refl≃stm
exterior-bp-left-inc-left (Join S₁ S₂) T (BPShift P) U .get PHere = SPath≃ (Here≃ (≃′-to-≃ (insertion-bp-left (Join S₁ S₂) T (BPShift P) U)))
exterior-bp-left-inc-left (Join S₁ S₂) T (BPShift P) U .get (PExt Z) = compute-≃ (SExt≃ refl≃stm (≃′-to-≃ (insertion-bp-left S₂ T P U)))
exterior-bp-left-inc-left (Join S₁ S₂) T (BPShift P) U .get (PShift Z) = begin
  < SShift (exterior-label (connect-tree S₂ T) (connect-bp-left S₂ T P) U (connect-tree-inc-left′ S₂ T Z)) >stm
    ≈⟨ SShift≃ refl≃ (exterior-bp-left-inc-left S₂ T P U .get Z) ⟩
  < SShift (exterior-label S₂ P U Z >>= connect-tree-inc-left (insertion-tree S₂ P U) T) >stm
    ≈˘⟨ >>=-shift (exterior-label S₂ P U Z) (connect-tree-inc-left (insertion-tree S₂ P U) T) ⟩
  < exterior-label S₂ P U Z >>= map-shift {S = S₁} (connect-tree-inc-left (insertion-tree S₂ P U) T) >stm
    ≈⟨ >>=-≃ (refl≃stm {a = exterior-label S₂ P U Z}) [ (λ Z → compute-≃ refl≃stm) ] refl≃sty ⟩
  < exterior-label S₂ P U Z >>= label₂ (connect-tree-inc-left (Join S₁ (insertion-tree S₂ P U)) T) >stm ∎
  where open Reasoning stm-setoid

exterior-bp-left-inc-right : (S : Tree n)
                           → (T : Tree m)
                           → (P : BranchingPoint S l)
                           → (U : Tree n′)
                           → .⦃ _ : has-linear-height l U ⦄
                           → ap (connect-tree-inc-right S T) ●l (exterior-label (connect-tree S T) (connect-bp-left S T P) U ,, S⋆)
                           ≃l ap (connect-tree-inc-right (insertion-tree S P U) T)
exterior-bp-left-inc-right (Join S₁ S₂) T BPHere U .get Z = begin
  < replace-label (ap (connect-tree-inc-right U (connect-tree S₂ T))) (SPath (connect-tree-inc-left′ U (connect-tree S₂ T) (last-path U))) (connect-tree-inc-right′ S₂ T Z) >stm
    ≈⟨ replace-label-prop (ap (connect-tree-inc-right U (connect-tree S₂ T))) (SPath (connect-tree-inc-left′ U (connect-tree S₂ T) (last-path U))) (SPath≃ (connect-tree-inc-phere U (connect-tree S₂ T))) .get (connect-tree-inc-right′ S₂ T Z) ⟩
  < ap (connect-tree-inc-right U (connect-tree S₂ T)) (connect-tree-inc-right′ S₂ T Z) >stm
    ≈⟨ SPath≃ (connect-tree-inc-right-assoc U S₂ T .get Z) ⟩
  < ap (connect-tree-inc-right (connect-tree U S₂) T) Z >stm ∎
  where
    open Reasoning stm-setoid
exterior-bp-left-inc-right (Join S₁ S₂) T (BPExt P) (Join U Sing) .get Z = compute-≃ refl≃stm
exterior-bp-left-inc-right (Join S₁ S₂) T (BPShift P) U .get Z = compute-≃ (SShift≃ refl≃ (exterior-bp-left-inc-right S₂ T P U .get Z))

sub-from-bp-left : (S : Tree n)
                 → (T : Tree m)
                 → (P : BranchingPoint S l)
                 → (U : Tree n′)
                 → .⦃ _ : has-linear-height l U ⦄
                 → (L : Label X S)
                 → (M : Label X T)
                 → (N : Label X U)
                 → label-from-insertion (connect-tree S T) (connect-bp-left S T P) U (connect-label L M) N
                 ≃lm label-≃ (insertion-bp-left S T P U) (connect-label (label-from-insertion S P U L N) M)
sub-from-bp-left (Join S₁ S₂) T BPHere U L M N .get Z = connect-label-assoc N (L ∘ PShift) M .get Z
sub-from-bp-left (Join S₁ S₂) T (BPExt P) (Join U Sing) L M N .get (PExt Z) = refl≃stm
sub-from-bp-left (Join S₁ S₂) T (BPExt P) (Join U Sing) L M N .get (PShift Z) = replace-connect-label (L ∘ PShift) M (N (PShift PHere)) .get Z
sub-from-bp-left (Join S₁ S₂) T (BPShift P) U L M N .get (PExt Z) = refl≃stm
sub-from-bp-left (Join S₁ S₂) T (BPShift P) U L M N .get (PShift Z) = sub-from-bp-left S₂ T P U (L ∘ PShift) M N .get Z

connect-bp-right : (S : Tree n)
                 → (T : Tree m)
                 → (P : BranchingPoint T l)
                 → BranchingPoint (connect-tree S T) l
connect-bp-right Sing T P = P
connect-bp-right (Join S₁ S₂) T P = BPShift (connect-bp-right S₂ T P)

connect-bp-right-prop : (S : Tree n)
                      → (T : Tree m)
                      → (P : BranchingPoint T l)
                      → SPath (branching-path-to-path (connect-bp-right S T P))
                      ≃stm ap (connect-tree-inc-right S T) (branching-path-to-path P)
connect-bp-right-prop Sing T P = refl≃stm
connect-bp-right-prop (Join S₁ S₂) T P = compute-≃ (SShift≃ refl≃ (connect-bp-right-prop S₂ T P))

insertion-bp-right : (S : Tree n)
                   → (T : Tree m)
                   → (P : BranchingPoint T l)
                   → (U : Tree n′)
                   → .⦃ _ : has-linear-height l U ⦄
                   → insertion-tree (connect-tree S T) (connect-bp-right S T P) U ≃′ connect-tree S (insertion-tree T P U)
insertion-bp-right Sing T P U = refl≃′
insertion-bp-right (Join S₁ S₂) T P U = Join≃′ refl≃′ (insertion-bp-right S₂ T P U)

exterior-bp-right-inc-left : (S : Tree n)
                           → (T : Tree m)
                           → (P : BranchingPoint T l)
                           → (U : Tree n′)
                           → .⦃ _ : has-linear-height l U ⦄
                           → ap (connect-tree-inc-left S T) ●l (exterior-label (connect-tree S T) (connect-bp-right S T P) U ,, S⋆)
                           ≃l ap (connect-tree-inc-left S (insertion-tree T P U))
exterior-bp-right-inc-left Sing T P U .get PHere = exterior-label-phere T P U
exterior-bp-right-inc-left (Join S₁ S₂) T P U .get PHere = SPath≃ (Here≃ (≃′-to-≃ (insertion-bp-right (Join S₁ S₂) T P U)))
exterior-bp-right-inc-left (Join S₁ S₂) T P U .get (PExt Z) = compute-≃ (SExt≃ refl≃stm (≃′-to-≃ (insertion-bp-right S₂ T P U)))
exterior-bp-right-inc-left (Join S₁ S₂) T P U .get (PShift Z) = compute-≃ (SShift≃ refl≃ (exterior-bp-right-inc-left S₂ T P U .get Z))

exterior-bp-right-inc-right : (S : Tree n)
                            → (T : Tree m)
                            → (P : BranchingPoint T l)
                            → (U : Tree n′)
                            → .⦃ _ : has-linear-height l U ⦄
                            → ap (connect-tree-inc-right S T) ●l (exterior-label (connect-tree S T) (connect-bp-right S T P) U ,, S⋆)
                            ≃l exterior-label T P U ●l (connect-tree-inc-right S (insertion-tree T P U))
exterior-bp-right-inc-right Sing T P U = sym≃l (comp-right-unit (exterior-label T P U))
exterior-bp-right-inc-right (Join S₁ S₂) T P U = begin
  < SShift ∘ (ap (connect-tree-inc-right S₂ T) ●l (exterior-label (connect-tree S₂ T) (connect-bp-right S₂ T P) U ,, S⋆)) >l
    ≈⟨ [ (λ Z → SShift≃ refl≃ (exterior-bp-right-inc-right S₂ T P U .get Z)) ] ⟩
  < SShift ∘ exterior-label T P U ●l connect-tree-inc-right S₂ (insertion-tree T P U) >l
    ≈˘⟨ comp-shift (exterior-label T P U) (connect-tree-inc-right S₂ (insertion-tree T P U)) ⟩
  < exterior-label T P U ●l map-shift {S = S₁} (connect-tree-inc-right S₂ (insertion-tree T P U)) >l
    ≈⟨ label-comp-≃ (refl≃l {L = exterior-label T P U}) [ (λ Z → compute-≃ refl≃stm) ] refl≃sty ⟩
  < exterior-label T P U ●l connect-tree-inc-right (Join S₁ S₂) (insertion-tree T P U) >l  ∎
  where
    open Reasoning (label-setoid T)

sub-from-bp-right : (S : Tree n)
                  → (T : Tree m)
                  → (P : BranchingPoint T l)
                  → (U : Tree n′)
                  → .⦃ _ : has-linear-height l U ⦄
                  → (L : Label X S)
                  → (M : Label X T)
                  → (N : Label X U)
                  → label-from-insertion′ (connect-tree S T) (connect-bp-right S T P) U (connect-label′ L M) N
                  ≃lm label-≃ (insertion-bp-right S T P U) (connect-label′ L (label-from-insertion′ T P U M N))
sub-from-bp-right Sing T P U L M N = refl≃lm
sub-from-bp-right (Join S₁ S₂) T P U L M N .get (PExt Z) = refl≃stm
sub-from-bp-right (Join S₁ S₂) T P U L M N .get (PShift Z) = sub-from-bp-right S₂ T P U (λ x → L (PShift x)) M N .get Z


Orthogonal : (P : BranchingPoint S l) → (Q : BranchingPoint S l′) → Set
Orthogonal BPHere BPHere = ⊥
Orthogonal BPHere (BPExt Q) = ⊥
Orthogonal BPHere (BPShift Q) = ⊤
Orthogonal (BPExt P) BPHere = ⊥
Orthogonal (BPExt P) (BPExt Q) = Orthogonal P Q
Orthogonal (BPExt P) (BPShift Q) = ⊤
Orthogonal (BPShift P) BPHere = ⊤
Orthogonal (BPShift P) (BPExt Q) = ⊤
Orthogonal (BPShift P) (BPShift Q) = Orthogonal P Q

Orthogonal-sym : (P : BranchingPoint S l) → (Q : BranchingPoint S l′) → .⦃ Orthogonal P Q ⦄ → Orthogonal Q P
Orthogonal-sym BPHere (BPShift Q) = tt
Orthogonal-sym (BPExt P) (BPExt Q) = Orthogonal-sym P Q
Orthogonal-sym (BPExt P) (BPShift Q) = tt
Orthogonal-sym (BPShift P) BPHere = tt
Orthogonal-sym (BPShift P) (BPExt Q) = tt
Orthogonal-sym (BPShift P) (BPShift Q) = Orthogonal-sym P Q

module Def39 where
  orthog-bp : (P : BranchingPoint S l)
            → (Q : BranchingPoint S l′)
            → .⦃ Orthogonal P Q ⦄
            → (T : Tree m)
            → .⦃ _ : has-linear-height (bp-height P) T ⦄
            → BranchingPoint (insertion-tree S P T) l′
  orthog-bp BPHere (BPShift Q) T = connect-bp-right T _ Q
  orthog-bp (BPExt P) (BPExt Q) (Join T Sing) = BPExt (orthog-bp P Q T)
  orthog-bp (BPExt P) (BPShift Q) (Join T Sing) = BPShift Q
  orthog-bp (BPShift P) BPHere T = BPHere
  orthog-bp (BPShift P) (BPExt Q) T = BPExt Q
  orthog-bp (BPShift P) (BPShift Q) T = BPShift (orthog-bp P Q T)

  orthog-bp-prop : (S : Tree n)
                 → (P : BranchingPoint S l)
                 → (Q : BranchingPoint S l′)
                 → .⦃ _ : Orthogonal P Q ⦄
                 → (T : Tree m)
                 → .⦃ _ : has-linear-height (bp-height P) T ⦄
                 → SPath (branching-path-to-path (orthog-bp P Q T))
                 ≃stm exterior-label S P T (branching-path-to-path Q)
  orthog-bp-prop (Join S₁ S₂) BPHere (BPShift Q) T = begin
    < SPath (branching-path-to-path (connect-bp-right T S₂ Q)) >stm
      ≈⟨ connect-bp-right-prop T S₂ Q ⟩
    < ap (connect-tree-inc-right T S₂) (branching-path-to-path Q) >stm
      ≈˘⟨ replace-not-here (ap (connect-tree-inc-right T S₂)) (SPath (connect-tree-inc-left′ T S₂ (last-path T))) (branching-path-to-path Q) ⦃ branching-path-to-path-not-here Q ⦄ ⟩
    < replace-label (ap (connect-tree-inc-right T S₂))
         (SPath (connect-tree-inc-left′ T S₂ (last-path T)))
         (branching-path-to-path Q) >stm ∎
    where
      open Reasoning stm-setoid
  orthog-bp-prop (Join S₁ S₂) (BPExt P) (BPExt Q) (Join T Sing) = compute-≃ (SExt≃ (orthog-bp-prop S₁ P Q T) refl≃)
  orthog-bp-prop (Join S₁ S₂) (BPExt P) (BPShift Q) (Join T Sing) = compute-≃ refl≃stm
  orthog-bp-prop (Join S₁ S₂) (BPShift P) BPHere T = compute-≃ refl≃stm
  orthog-bp-prop (Join S₁ S₂) (BPShift P) (BPExt Q) T = compute-≃ refl≃stm
  orthog-bp-prop (Join S₁ S₂) (BPShift P) (BPShift Q) T = compute-≃ (SShift≃ refl≃ (orthog-bp-prop S₂ P Q T))
open Def39 public

module Lemma42 where
  insertion-orthog : (S : Tree n)
                   → (P : BranchingPoint S l)
                   → (T : Tree m)
                   → .⦃ _ : has-linear-height (bp-height P) T ⦄
                   → (Q : BranchingPoint S l′)
                   → .⦃ _ : Orthogonal P Q ⦄
                   → (U : Tree m′)
                   → .⦃ _ : has-linear-height (bp-height Q) U ⦄
                   → insertion-tree (insertion-tree S P T) (orthog-bp P Q T) U ≃′ insertion-tree (insertion-tree S Q U) (orthog-bp Q P ⦃ Orthogonal-sym P Q ⦄ U) T
  insertion-orthog (Join S₁ S₂) BPHere T (BPShift Q) U = insertion-bp-right T S₂ Q U
  insertion-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) = Join≃′ (insertion-orthog S₁ P T Q U) Refl≃′
  insertion-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPShift Q) U = Refl≃′
  insertion-orthog (Join S₁ S₂) (BPShift P) T BPHere U = sym≃′ (insertion-bp-right U S₂ P T)
  insertion-orthog (Join S₁ S₂) (BPShift P) T (BPExt Q) (Join U Sing) = Refl≃′
  insertion-orthog (Join S₁ S₂) (BPShift P) T (BPShift Q) U = Join≃′ Refl≃′ (insertion-orthog S₂ P T Q U)

  module _ where
    open Reasoning stm-setoid
    exterior-orthog : (S : Tree n)
                    → (P : BranchingPoint S l)
                    → (T : Tree m)
                    → .⦃ _ : has-linear-height (bp-height P) T ⦄
                    → (Q : BranchingPoint S l′)
                    → .⦃ _ : Orthogonal P Q ⦄
                    → (U : Tree m′)
                    → .⦃ _ : has-linear-height (bp-height Q) U ⦄
                    → exterior-label S P T ●l (exterior-label (insertion-tree S P T) (orthog-bp P Q T) U ,, S⋆)
                    ≃lm exterior-label S Q U ●l (exterior-label (insertion-tree S Q U) (orthog-bp Q P ⦃ Orthogonal-sym P Q ⦄ U) T ,, S⋆)
    exterior-orthog (Join S₁ S₂) BPHere T (BPShift Q) U .get (PExt Z) = begin
      < label-from-linear-tree-unbiased S₁ T 1 Z
        >>= connect-tree-inc-left T S₂
        >>= (exterior-label (connect-tree T S₂) (connect-bp-right T S₂ Q) U ,, S⋆) >stm
        ≈⟨ >>=-assoc (label-from-linear-tree-unbiased S₁ T 1 Z) (connect-tree-inc-left T S₂) _ ⟩
      < label-from-linear-tree-unbiased S₁ T 1 Z
        >>= connect-tree-inc-left T S₂ ●lt (exterior-label (connect-tree T S₂) (connect-bp-right T S₂ Q) U ,, S⋆) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = label-from-linear-tree-unbiased S₁ T 1 Z}) (exterior-bp-right-inc-left T S₂ Q U) (S⋆-≃ (≃′-to-≃ (insertion-bp-right T S₂ Q U))) ⟩
      < label-from-linear-tree-unbiased S₁ T 1 Z
        >>= connect-tree-inc-left T (insertion-tree S₂ Q U) >stm ∎
    exterior-orthog (Join S₁ S₂) BPHere T (BPShift Q) U .get (PShift Z) = begin
      < replace-label (ap (connect-tree-inc-right T S₂)) (SPath (connect-tree-inc-left′ T S₂ (last-path T))) Z
          >>= (exterior-label (connect-tree T S₂) (connect-bp-right T S₂ Q) U ,, S⋆) >stm
        ≈⟨ >>=-≃ (replace-label-prop _ _ (SPath≃ (connect-tree-inc-phere T S₂)) .get Z) refl≃l refl≃sty ⟩
      < exterior-label (connect-tree T S₂) (connect-bp-right T S₂ Q) U (connect-tree-inc-right′ T S₂ Z) >stm
        ≈⟨ exterior-bp-right-inc-right T S₂ Q U .get Z ⟩
      < exterior-label S₂ Q U Z >>= connect-tree-inc-right T (insertion-tree S₂ Q U) >stm
        ≈˘⟨ >>=-≃ (refl≃stm {a = exterior-label S₂ Q U Z}) (replace-label-prop _ _ (SPath≃ (connect-tree-inc-phere T (insertion-tree S₂ Q U)))) refl≃sty ⟩
      < exterior-label S₂ Q U Z
        >>= (replace-label (ap (connect-tree-inc-right T (insertion-tree S₂ Q U)))
                          (SPath (connect-tree-inc-left′ T (insertion-tree S₂ Q U) (last-path T))) ,, S⋆) >stm ∎
    exterior-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) .get (PExt Z) = let
      instance _ = Orthogonal-sym P Q
      in begin
      < exterior-label S₁ P T Z >>= map-ext (exterior-label (insertion-tree S₁ P T) (orthog-bp P Q T) U ,, S⋆) >stm
        ≈⟨ >>=-ext (exterior-label S₁ P T Z) (exterior-label (insertion-tree S₁ P T) (orthog-bp P Q T) U ,, S⋆) ⟩
      < SExt (exterior-label S₁ P T Z >>= (exterior-label (insertion-tree S₁ P T) (orthog-bp P Q T) U ,, S⋆)) >stm
        ≈⟨ SExt≃ (exterior-orthog S₁ P T Q U .get Z) refl≃ ⟩
      < SExt (exterior-label S₁ Q U Z >>= (exterior-label (insertion-tree S₁ Q U) (orthog-bp Q P U) T ,, S⋆)) >stm
        ≈˘⟨ >>=-ext (exterior-label S₁ Q U Z) (exterior-label (insertion-tree S₁ Q U) (orthog-bp Q P U) T ,, S⋆) ⟩
      < exterior-label S₁ Q U Z >>= map-ext (exterior-label (insertion-tree S₁ Q U) (orthog-bp Q P U) T ,, S⋆) >stm ∎
    exterior-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) .get (PShift Z) = SShift≃ (≃′-to-≃ (insertion-orthog S₁ P T Q U)) refl≃stm
    exterior-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPShift Q) U .get (PExt Z) = begin
      < exterior-label S₁ P T Z >>= ((SExt ∘ SPath) ,, SArr (SPath PHere) S⋆ (SShift (exterior-label S₂ Q U PHere))) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = exterior-label S₁ P T Z}) refl≃l (SArr≃ refl≃stm refl≃sty (SShift≃ refl≃ (exterior-label-phere S₂ Q U))) ⟩
      < exterior-label S₁ P T Z >>= map-ext (id-label-wt (insertion-tree S₁ P T)) >stm
        ≈⟨ >>=-ext (exterior-label S₁ P T Z) (id-label-wt (insertion-tree S₁ P T)) ⟩
      < SExt (exterior-label S₁ P T Z >>= id-label-wt (insertion-tree S₁ P T)) >stm
        ≈⟨ SExt≃ (>>=-id (exterior-label S₁ P T Z)) refl≃ ⟩
      < SExt (exterior-label S₁ P T Z) >stm ∎
    exterior-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPShift Q) U .get (PShift Z) = begin
      < SShift (exterior-label S₂ Q U Z) >stm
        ≈˘⟨ SShift≃ refl≃ (>>=-id (exterior-label S₂ Q U Z)) ⟩
      < SShift (exterior-label S₂ Q U Z >>= id-label-wt (insertion-tree S₂ Q U)) >stm
        ≈˘⟨ >>=-shift (exterior-label S₂ Q U Z) (id-label-wt (insertion-tree S₂ Q U)) ⟩
      < exterior-label S₂ Q U Z >>= map-shift (id-label-wt (insertion-tree S₂ Q U)) >stm ∎
    exterior-orthog (Join S₁ S₂) (BPShift P) T BPHere U .get (PExt Z) = sym≃stm (exterior-orthog (Join S₁ S₂) BPHere U (BPShift P) T .get (PExt Z))
    exterior-orthog (Join S₁ S₂) (BPShift P) T BPHere U .get (PShift Z) = sym≃stm (exterior-orthog (Join S₁ S₂) BPHere U (BPShift P) T .get (PShift Z))
    exterior-orthog (Join S₁ S₂) (BPShift P) T (BPExt Q) (Join U Sing) .get (PExt Z) = begin
      < SExt (exterior-label S₁ Q U Z) >stm
        ≈˘⟨ SExt≃ (>>=-id (exterior-label S₁ Q U Z)) refl≃ ⟩
      < SExt (exterior-label S₁ Q U Z >>= id-label-wt (insertion-tree S₁ Q U)) >stm
        ≈˘⟨ >>=-ext (exterior-label S₁ Q U Z) (id-label-wt (insertion-tree S₁ Q U)) ⟩
      < exterior-label S₁ Q U Z >>= map-ext (id-label-wt (insertion-tree S₁ Q U)) >stm
        ≈˘⟨ >>=-≃ (refl≃stm {a = exterior-label S₁ Q U Z}) refl≃l (SArr≃ refl≃stm refl≃sty (SShift≃ refl≃ (exterior-label-phere S₂ P T))) ⟩
      < exterior-label S₁ Q U Z >>= (SExt ∘ SPath ,, SArr (SPath PHere) S⋆ (SShift (exterior-label S₂ P T PHere))) >stm ∎
    exterior-orthog (Join S₁ S₂) (BPShift P) T (BPExt Q) (Join U Sing) .get (PShift Z) = begin
      < exterior-label S₂ P T Z >>= map-shift (id-label-wt (insertion-tree S₂ P T)) >stm
        ≈⟨ >>=-shift (exterior-label S₂ P T Z) (id-label-wt (insertion-tree S₂ P T)) ⟩
      < SShift (exterior-label S₂ P T Z >>= id-label-wt (insertion-tree S₂ P T)) >stm
        ≈⟨ SShift≃ refl≃ (>>=-id (exterior-label S₂ P T Z)) ⟩
      < SShift (exterior-label S₂ P T Z) >stm ∎
    exterior-orthog (Join S₁ S₂) (BPShift P) T (BPShift Q) U .get (PExt Z) = SExt≃ refl≃stm (≃′-to-≃ (insertion-orthog S₂ P T Q U))
    exterior-orthog (Join S₁ S₂) (BPShift P) T (BPShift Q) U .get (PShift Z) = let
      instance _ = Orthogonal-sym P Q
      in begin
      < exterior-label S₂ P T Z >>= map-shift (exterior-label (insertion-tree S₂ P T) (orthog-bp P Q T) U ,, S⋆) >stm
        ≈⟨ >>=-shift (exterior-label S₂ P T Z) (exterior-label (insertion-tree S₂ P T) (orthog-bp P Q T) U ,, S⋆) ⟩
      < SShift (exterior-label S₂ P T Z >>= (exterior-label (insertion-tree S₂ P T) (orthog-bp P Q T) U ,, S⋆)) >stm
        ≈⟨ SShift≃ refl≃ (exterior-orthog S₂ P T Q U .get Z) ⟩
      < SShift (exterior-label S₂ Q U Z >>= (exterior-label (insertion-tree S₂ Q U) (orthog-bp Q P U) T ,, S⋆)) >stm
        ≈˘⟨ >>=-shift (exterior-label S₂ Q U Z) (exterior-label (insertion-tree S₂ Q U) (orthog-bp Q P U) T ,, S⋆) ⟩
      < exterior-label S₂ Q U Z >>= map-shift (exterior-label (insertion-tree S₂ Q U) (orthog-bp Q P U) T ,, S⋆) >stm ∎

    sub-from-orthog : (S : Tree n)
                    → (P : BranchingPoint S l)
                    → (T : Tree m)
                    → .⦃ _ : has-linear-height (bp-height P) T ⦄
                    → (Q : BranchingPoint S l′)
                    → .⦃ _ : Orthogonal P Q ⦄
                    → (U : Tree m′)
                    → .⦃ _ : has-linear-height (bp-height Q) U ⦄
                    → (L : Label X S)
                    → (M : Label X T)
                    → (N : Label X U)
                    → label-from-insertion′ (insertion-tree S P T) (orthog-bp P Q T) U (label-from-insertion′ S P T L M) N
                    ≃lm label-≃ (insertion-orthog S P T Q U) (label-from-insertion′ (insertion-tree S Q U) (orthog-bp Q P ⦃ Orthogonal-sym P Q ⦄ U) T (label-from-insertion′ S Q U L N) M)
    sub-from-orthog (Join S₁ S₂) BPHere T (BPShift Q) U L M N = sub-from-bp-right T S₂ Q U M (λ x → L (PShift x)) N
    sub-from-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) L M N .get (PExt Z) = sub-from-orthog S₁ P T Q U (L ∘ PExt) (M ∘ PExt) (N ∘ PExt) .get Z
    sub-from-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) L M N .get (PShift Z) = refl≃stm
    sub-from-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPShift Q) U L M N .get (PExt Z) = refl≃stm
    sub-from-orthog (Join S₁ S₂) (BPExt P) (Join T Sing) (BPShift Q) U L M N .get (PShift Z) = refl≃stm
    sub-from-orthog (Join S₁ S₂) (BPShift P) T BPHere U L M N .get Z = sym≃stm (label-≃-sym-max (insertion-bp-right U S₂ P T) (sub-from-bp-right U S₂ P T N (λ x → L (PShift x)) M) .get Z)
    sub-from-orthog (Join S₁ S₂) (BPShift P) T (BPExt Q) (Join U Sing) L M N .get (PExt Z) = refl≃stm
    sub-from-orthog (Join S₁ S₂) (BPShift P) T (BPExt Q) (Join U Sing) L M N .get (PShift Z) = refl≃stm
    sub-from-orthog (Join S₁ S₂) (BPShift P) T (BPShift Q) U L M N .get (PExt Z) = refl≃stm
    sub-from-orthog (Join S₁ S₂) (BPShift P) T (BPShift Q) U L M N .get (PShift Z) = sub-from-orthog S₂ P T Q U (L ∘ PShift) M N .get Z
open Lemma42 public

module Lemma46 where
  insertion-bd-1 : (S : Tree n)
                 → (p : BranchingPoint S l)
                 → (T : Tree m)
                 → .⦃ _ : has-linear-height (bp-height p) T ⦄
                 → (d : ℕ)
                 → .(d ≤ linear-height T)
                 → .(height-of-branching p ≥ tree-dim T)
                 → tree-bd d S ≃′ tree-bd d (insertion-tree S p T)
  insertion-bd-1 (Join S₁ S₂) p T zero q r = refl≃′
  insertion-bd-1 (Join S₁ S₂) BPHere (Join T Sing) (suc d) q r = let
    .lem : d ≤ tree-dim S₁
    lem = ≤-pred (≤-trans q (≤-trans (s≤s (linear-height-dim T)) r))
    in Join≃′ (linear-tree-unique (tree-bd d S₁)
                                ⦃ bd-linear-height d S₁ (≤-trans lem (≤-reflexive (sym (linear-linear-height S₁)))) ⦄
                                (tree-bd d T)
                                ⦃ bd-linear-height d T (≤-pred q) ⦄
                                (trans (tree-dim-bd′ d S₁ lem) (sym (tree-dim-bd′ d T (≤-trans (≤-pred q) (linear-height-dim T))))))
            refl≃′
  insertion-bd-1 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) q r = Join≃′ (insertion-bd-1 S₁ p T d (≤-pred q) (≤-pred r)) refl≃′
  insertion-bd-1 (Join S₁ S₂) (BPShift p) T (suc d) q r = Join≃′ refl≃′ (insertion-bd-1 S₂ p T (suc d) q r)

  unbiased-exterior-comm-1 : (S : Tree n)
                           → (p : BranchingPoint S l)
                           → (T : Tree m)
                           → .⦃ _ : has-linear-height (bp-height p) T ⦄
                           → (d : ℕ)
                           → (d < height-of-branching p)
                           → (q : d ≤ linear-height T)
                           → (r : height-of-branching p ≥ tree-dim T)
                           → (b : Bool)
                           → ap (tree-inc-label d S b) ●l (exterior-label S p T ,, S⋆) ≃lm label-≃ (insertion-bd-1 S p T d q r) (ap (tree-inc-label d (insertion-tree S p T) b))
  unbiased-exterior-comm-1 S P T zero p q r false .get Z = exterior-label-phere S P T
  unbiased-exterior-comm-1 S P T zero p q r true .get Z = exterior-label-last-path S P T
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPHere ⦃ l ⦄) (Join T Sing) (suc d) p q r b .get (PExt Z) = begin
    < label-from-linear-tree-unbiased S₁ (Join T Sing) 1 (tree-inc-label′ d S₁ b Z)
          >>= connect-tree-inc-left (Join T Sing) S₂ >stm
      ≈⟨ >>=-≃ (lfltu-≤-linear-height S₁ (susp-tree T) 1 d q (≤-pred p) r b Z) refl≃l refl≃sty ⟩
    < SPath (PExt (tree-inc-label′ d T b (is-linear-max-path (tree-bd d T)))) >stm
      ≈⟨ SPath≃ (Ext≃ (ap′-≃ (tree-inc-label′ d T b) lem) refl≃) ⟩
    < SPath (PExt (tree-inc-label′ d T b (ppath-≃ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z))) >stm ∎
    where
      instance _ = bd-linear-height (1 + d) (susp-tree T) q
      instance _ = bd-linear-height d S₁ (≤-trans (≤-pred (≤-pred (≤-step p))) (≤-reflexive (sym (linear-linear-height S₁ ⦃ l ⦄))))
      lem : is-linear-max-path (tree-bd d T) ≃p
              ppath-≃ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z
      lem = begin
        < is-linear-max-path (tree-bd d T) >p
          ≈⟨ max-path-lin-tree (tree-bd d T) Z (≃′-to-≃ (sym≃′ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) (trans (tree-dim-bd′ d S₁ (≤-pred (≤-pred (≤-step p)))) (sym (tree-dim-bd′ d T (≤-trans (≤-pred q) (linear-height-dim T)))))))) ⟩
        < Z >p
          ≈⟨ ppath-≃-≃p (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z ⟩
        < ppath-≃ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z >p ∎
        where
          open Reasoning path-setoid
      open Reasoning stm-setoid
  unbiased-exterior-comm-1 (Join S₁ S₂) BPHere (Join T Sing) (suc d) p q r b .get (PShift Z) = begin
    < replace-label (λ P → SPath (PShift P)) (SPath (PShift PHere))
                    (tree-inc-label′ (suc d) S₂ b Z) >stm
      ≈⟨ replace-not-here (λ P → SPath (PShift P)) (SPath (PShift PHere)) (tree-inc-label′ (suc d) S₂ b Z) ⦃ tree-inc-not-here (suc d) S₂ b Z ⦄ ⟩
    < SPath (PShift (tree-inc-label′ (suc d) S₂ b Z)) >stm ∎
    where
      open Reasoning stm-setoid
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPExt P) (Join T Sing) (suc d) p q r b .get (PExt Z)
    = compute-≃ (SExt≃ (unbiased-exterior-comm-1 S₁ P T d (≤-pred p) (≤-pred q) (≤-pred r) b .get Z) refl≃)
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPExt P) (Join T Sing) (suc d) p q r b .get (PShift Z)
    = compute-≃ refl≃stm
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPShift P) T (suc d) p q r b .get (PExt Z)
    = compute-≃ refl≃stm
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPShift P) T (suc d) p q r b .get (PShift Z)
    = compute-≃ (SShift≃ refl≃ (unbiased-exterior-comm-1 S₂ P T (suc d) p q r b .get Z))
open Lemma46 public

data Condition (d : ℕ) (T : Tree n) (m : ℕ) : Set where
  Cond1 : d > (linear-height T) → d ≤ m → Condition d T m
  Cond2 : d ≥ m → Condition d T m

cond-pred : Condition (suc d) (susp-tree T) (suc m) → Condition d T m
cond-pred (Cond1 x y) = Cond1 (≤-pred x) (≤-pred y)
cond-pred (Cond2 x) = Cond2 (≤-pred x)

bd-bp-lem : (p : BranchingPoint S l)
          → {T : Tree n}
          → .⦃ has-linear-height (bp-height p) T ⦄
          → Condition d T (height-of-branching p)
          → d > bp-height p
bd-bp-lem p {T} (Cond1 x y) = <-transʳ (has-linear-height-prop _ T) x
bd-bp-lem p (Cond2 q) = <-transˡ (height-of-branching->-bp-height p) q

module Def47 where
  bd-branching-point : (S : Tree n)
                     → (p : BranchingPoint S l)
                     → (d : ℕ)
                     → .(q : d > bp-height p)
                     → BranchingPoint (tree-bd d S) l
  bd-branching-point (Join S₁ S₂) BPHere (suc d) q = BPHere ⦃ is-linear-bd d S₁ ⦄
  bd-branching-point (Join S₁ S₂) (BPExt p) (suc d) q = BPExt (bd-branching-point S₁ p d (≤-pred q))
  bd-branching-point (Join S₁ S₂) (BPShift p) (suc d) q = BPShift (bd-branching-point S₂ p (suc d) q)
open Def47 public

bd-branching-point-height : (S : Tree n)
                          → (p : BranchingPoint S l)
                          → (d : ℕ)
                          → .(q : d > bp-height p)
                          → height-of-branching (bd-branching-point S p d q) ≡ d ⊓ height-of-branching p
bd-branching-point-height (Join S₁ S₂) BPHere (suc d) q = cong suc (tree-dim-bd d S₁)
bd-branching-point-height (Join S₁ S₂) (BPExt p) (suc d) q = cong suc (bd-branching-point-height S₁ p d (≤-pred q))
bd-branching-point-height (Join S₁ S₂) (BPShift p) (suc d) q = bd-branching-point-height S₂ p (suc d) q

bd-has-linear-height : (d : ℕ) → (m : ℕ)
                     → (T : Tree n) → .⦃ has-linear-height m T ⦄
                     → .(d > m)
                     → has-linear-height m (tree-bd d T)
bd-has-linear-height d zero T q = tt
bd-has-linear-height (suc d) (suc m) (Join T Sing) q = bd-has-linear-height d m T (≤-pred q)

module Lemma48 where
  open Reasoning stm-setoid

  insertion-bd-2 : (S : Tree n)
                 → (p : BranchingPoint S l)
                 → (T : Tree m)
                 → .⦃ _ : has-linear-height (bp-height p) T ⦄
                 → (d : ℕ)
                 → .(q : d > bp-height p)
                 → insertion-tree (tree-bd d S)
                                  (bd-branching-point S p d q)
                                  (tree-bd d T)
                                  ⦃ bd-has-linear-height d l T q ⦄
                   ≃′ tree-bd d (insertion-tree S p T)
  insertion-bd-2 (Join S₁ S₂) BPHere T (suc d) q = connect-tree-bd d T S₂
  insertion-bd-2 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) q
    = Join≃′ (insertion-bd-2 S₁ p T d (≤-pred q)) refl≃′
  insertion-bd-2 (Join S₁ S₂) (BPShift p) T (suc d) q
    = Join≃′ refl≃′ (insertion-bd-2 S₂ p T (suc d) q)

  unbiased-exterior-comm-2 : (S : Tree n)
                           → (p : BranchingPoint S l)
                           → (T : Tree m)
                           → .⦃ _ : has-linear-height (bp-height p) T ⦄
                           → (d : ℕ)
                           → (b : Bool)
                           → height-of-branching p ≥ tree-dim T
                           → (c : Condition d T (height-of-branching p))
                           → ap (tree-inc-label d S b) ●l (exterior-label S p T ,, S⋆)
                           ≃lm exterior-label (tree-bd d S)
                                                  (bd-branching-point S p d (bd-bp-lem p c))
                                                  (tree-bd d T)
                                                  ⦃ bd-has-linear-height d l T (bd-bp-lem p c) ⦄
                               ●l (label-wt-≃ (insertion-bd-2 S p T d (bd-bp-lem p c)) (tree-inc-label d (insertion-tree S p T) b))
  unbiased-exterior-comm-2 S p T zero b r (Cond1 () x)
  unbiased-exterior-comm-2 S p T zero b r (Cond2 ())
  unbiased-exterior-comm-2 (Join S₁ S₂) BPHere T (suc d) b r c .get (PShift Z) = begin
    < replace-label (ap (connect-tree-inc-right T S₂))
                    (ap (connect-tree-inc-left T S₂) (last-path T))
                    (tree-inc-label′ (suc d) S₂ b Z) >stm
      ≈⟨ replace-not-here (ap (connect-tree-inc-right T S₂)) (ap (connect-tree-inc-left T S₂) (last-path T)) (tree-inc-label′ (suc d) S₂ b Z) ⦃ tree-inc-not-here (suc d) S₂ b Z ⦄ ⟩
    < SPath (connect-tree-inc-right′ T S₂ (tree-inc-label′ (suc d) S₂ b Z)) >stm
      ≈⟨ SPath≃ (tree-inc-inc-right d T S₂ b Z) ⟩
    < SPath (tree-inc-label′ (suc d) (connect-tree T S₂) b (ppath-≃ (connect-tree-bd d T S₂) (connect-tree-inc-right′ (tree-bd (suc d) T) (tree-bd (suc d) S₂) Z))) >stm
      ≈˘⟨ >>=-≃ (replace-not-here (ap (connect-tree-inc-right (tree-bd (suc d) T) (tree-bd (suc d) S₂)))
                                     (ap (connect-tree-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)) (last-path (tree-bd (suc d) T))) Z)
                                     (refl≃l {L = label-≃ (connect-tree-bd d T S₂) (ap (tree-inc-label (suc d) (connect-tree T S₂) b))})
                                     refl≃sty ⟩
    < (replace-label (ap (connect-tree-inc-right (tree-bd (suc d) T) (tree-bd (suc d) S₂)))
                     (ap (connect-tree-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)) (last-path (tree-bd (suc d) T)))
                     Z
        >>= label-wt-≃ (connect-tree-bd d T S₂) (tree-inc-label (suc d) (connect-tree T S₂) b)) >stm ∎
  unbiased-exterior-comm-2 (Join S₁ S₂) BPHere T (suc d) b r (Cond1 q r′) .get (PExt Z) = let
    instance _ = is-linear-bd d S₁
    in begin
    < label-from-linear-tree-unbiased S₁ T 1 (tree-inc-label′ d S₁ b Z)
        >>= connect-tree-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (lfltu->-linear-height S₁ T 1 d r q (≤-pred r′) b Z) (refl≃l {L = ap (connect-tree-inc-left T S₂)}) refl≃sty ⟩
    < unbiased-comp′ (d + 1) (tree-bd (d + 1) T) >>= tree-inc-label (d + 1) T b >>= connect-tree-inc-left T S₂ >stm
      ≈⟨ reflexive≃stm (cong (λ - → unbiased-comp′ - (tree-bd - T) >>= tree-inc-label - T b >>= connect-tree-inc-left T S₂) (+-comm d 1)) ⟩
    < unbiased-comp′ (1 + d) (tree-bd (1 + d) T) >>= tree-inc-label (1 + d) T b >>= connect-tree-inc-left T S₂ >stm
      ≈˘⟨ reflexive≃stm (cong (λ - → unbiased-comp′ (1 + -) (tree-bd (1 + d) T) >>= tree-inc-label (1 + d) T b >>= connect-tree-inc-left T S₂) (trans (tree-dim-bd d S₁) (m≤n⇒m⊓n≡m (≤-pred r′)))) ⟩
    < unbiased-comp′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T) >>= tree-inc-label (suc d) T b >>= connect-tree-inc-left T S₂ >stm
      ≈⟨ >>=-assoc (unbiased-comp′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)) (tree-inc-label (suc d) T b) (connect-tree-inc-left T S₂) ⟩
    < unbiased-comp′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)
      >>= tree-inc-label (suc d) T b ●lt connect-tree-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (sym≃stm (lfltu-maximal-path (tree-bd d S₁) (tree-bd (suc d) T) 1 Z)) [ (λ P → SPath≃ (tree-inc-inc-left d T S₂ b P)) ] refl≃sty ⟩
    < label-from-linear-tree-unbiased (tree-bd d S₁) (tree-bd (suc d) T) 1 Z
      >>= connect-tree-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
          ●lt (label-wt-≃ (connect-tree-bd d T S₂) (tree-inc-label (suc d) (connect-tree T S₂) b)) >stm
      ≈˘⟨ >>=-assoc (label-from-linear-tree-unbiased (tree-bd d S₁) (tree-bd (suc d) T) 1 Z) _ _ ⟩
    < label-from-linear-tree-unbiased (tree-bd d S₁) (tree-bd (suc d) T) 1 Z
        >>=
        connect-tree-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
        >>=
        label-wt-≃ (connect-tree-bd d T S₂) (tree-inc-label (suc d) (connect-tree T S₂) b) >stm ∎
  unbiased-exterior-comm-2 (Join S₁ S₂) BPHere T (suc d) b r (Cond2 q) .get (PExt Z) = let
    instance _ = is-linear-bd d S₁
    in begin
    < label-from-linear-tree-unbiased S₁ T 1 (tree-inc-label′ d S₁ b Z)
        >>= connect-tree-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (lfltu-maximal-path S₁ T 1 (tree-inc-label′ d S₁ b Z) ⦃ tree-inc-full-preserve-max d S₁ b (≤-pred q) Z ⦄) (refl≃l {L = ap (connect-tree-inc-left T S₂)}) refl≃sty ⟩
    < unbiased-comp′ (1 + tree-dim S₁) T >>= connect-tree-inc-left T S₂ >stm
      ≈˘⟨ >>=-≃′ (unbiased-comp′-≃ (cong suc (tree-dim-≃ (≃′-to-≃ (tree-bd-full d S₁ (≤-pred q))))) (≃′-to-≃ (tree-bd-full (suc d) T (≤-trans r q)))) ((tree-bd-full (suc d) T (≤-trans r q)) ,, [ (λ P → SPath≃ (ap′-≃ (connect-tree-inc-left′ T S₂) (tree-inc-label-full (suc d) T b (≤-trans r q) .get P))) ]) refl≃sty ⟩
    < unbiased-comp′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)
      >>= tree-inc-label (suc d) T b ●lt connect-tree-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (sym≃stm (lfltu-maximal-path (tree-bd d S₁) (tree-bd (suc d) T) 1 Z)) [ (λ P → SPath≃ (tree-inc-inc-left d T S₂ b P)) ] refl≃sty ⟩
    < label-from-linear-tree-unbiased (tree-bd d S₁) (tree-bd (suc d) T) 1 Z
      >>= connect-tree-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
          ●lt (label-wt-≃ (connect-tree-bd d T S₂) (tree-inc-label (suc d) (connect-tree T S₂) b)) >stm
      ≈˘⟨ >>=-assoc (label-from-linear-tree-unbiased (tree-bd d S₁) (tree-bd (suc d) T) 1 Z) _ _ ⟩
    < label-from-linear-tree-unbiased (tree-bd d S₁) (tree-bd (suc d) T) 1 Z
        >>=
        connect-tree-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
        >>=
        label-wt-≃ (connect-tree-bd d T S₂) (tree-inc-label (suc d) (connect-tree T S₂) b) >stm ∎

  unbiased-exterior-comm-2 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) b r c .get (PExt Z) = let
    instance _ = bd-has-linear-height d (bp-height p) T (bd-bp-lem p (cond-pred c))
    in begin
    < SExt (exterior-label S₁ p T (tree-inc-label′ d S₁ b Z)) >stm
      ≈⟨ SExt≃ (unbiased-exterior-comm-2 S₁ p T d b (≤-pred r) (cond-pred c) .get Z) refl≃ ⟩
    < SExt ((exterior-label (tree-bd d S₁)
                               (bd-branching-point S₁ p d (bd-bp-lem p (cond-pred c)))
                               (tree-bd d T)
            ●l label-wt-≃ (insertion-bd-2 S₁ p T d (bd-bp-lem p (cond-pred c)))
                            (tree-inc-label d (insertion-tree S₁ p T) b)) Z) >stm
      ≈˘⟨ >>=-ext (exterior-label (tree-bd d S₁) (bd-branching-point S₁ p d (bd-bp-lem p (cond-pred c))) (tree-bd d T) Z) (label-wt-≃ (insertion-bd-2 S₁ p T d (bd-bp-lem p (cond-pred c))) (tree-inc-label d (insertion-tree S₁ p T) b)) ⟩
    < exterior-label (tree-bd d S₁) (bd-branching-point S₁ p d (bd-bp-lem p (cond-pred c))) (tree-bd d T) Z
       >>= map-ext {T = S₂} (label-wt-≃ (insertion-bd-2 S₁ p T d (bd-bp-lem p (cond-pred c))) (tree-inc-label d (insertion-tree S₁ p T) b)) >stm
       ≈˘⟨ >>=-≃ (refl≃stm {a = exterior-label (tree-bd d S₁) (bd-branching-point S₁ p d (bd-bp-lem p (cond-pred c))) (tree-bd d T) Z}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ (SShift≃ refl≃ (SPath≃ (tree-inc-label-phere d S₂ b))))) ⟩
    < exterior-label (tree-bd d S₁) (bd-branching-point S₁ p d (bd-bp-lem p (cond-pred c))) (tree-bd d T) Z
       >>= label₁ (label-wt-≃ (Join≃′ (insertion-bd-2 S₁ p T d (bd-bp-lem p (cond-pred c))) refl≃′) (tree-inc-label (suc d) (Join (insertion-tree S₁ p T) S₂) b)) >stm ∎
  unbiased-exterior-comm-2 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) b r c .get (PShift Z)
    = compute-≃ refl≃stm
  unbiased-exterior-comm-2 (Join S₁ S₂) (BPShift p) T (suc d) b r c .get (PExt Z)
    = compute-≃ refl≃stm
  unbiased-exterior-comm-2 (Join S₁ S₂) (BPShift p) T (suc d) b r c .get (PShift Z) = let
    instance _ = bd-has-linear-height (suc d) (bp-height p) T (bd-bp-lem p c)
    in begin
    < SShift (exterior-label S₂ p T (tree-inc-label′ (suc d) S₂ b Z)) >stm
      ≈⟨ SShift≃ refl≃ (unbiased-exterior-comm-2 S₂ p T (suc d) b r c .get Z) ⟩
    < SShift (exterior-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z
        >>= label-wt-≃ (insertion-bd-2 S₂ p T (suc d) (bd-bp-lem p c)) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) >stm
      ≈˘⟨ >>=-shift (exterior-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z) (label-wt-≃ (insertion-bd-2 S₂ p T (suc d) (bd-bp-lem p c)) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) ⟩
    < exterior-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z
       >>= map-shift (label-wt-≃ (insertion-bd-2 S₂ p T (suc d) (bd-bp-lem p c)) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) >stm
      ≈⟨ >>=-≃ (refl≃stm {a = exterior-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z}) [ (λ P → compute-≃ refl≃stm) ] refl≃sty ⟩
    < exterior-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z
       >>= label₂ (label-wt-≃ (Join≃′ refl≃′ (insertion-bd-2 S₂ p T (suc d) (bd-bp-lem p c)))
                           (tree-inc-label (suc d) (Join S₁ (insertion-tree S₂ p T)) b)) >stm ∎
open Lemma48 public

data Bd-Conditions (d : ℕ) {S : Tree n} (P : BranchingPoint S l) (T : Tree m) : Set where
  Bd-Cond1 : d < height-of-branching P → d ≤ linear-height T → Bd-Conditions d P T
  Bd-Cond2 : Condition d T (height-of-branching P) → Bd-Conditions d P T

Bd-Conditions-one-of : (d : ℕ) → (P : BranchingPoint S l) → (T : Tree m) → Bd-Conditions d P T
Bd-Conditions-one-of d P T with <-cmp d (height-of-branching P)
... | tri≈ ¬a b ¬c = Bd-Cond2 (Cond2 (≤-reflexive (sym b)))
... | tri> ¬a ¬b c = Bd-Cond2 (Cond2 (<⇒≤ c))
... | tri< a ¬b ¬c with <-cmp d (linear-height T)
... | tri< a₁ ¬b₁ ¬c₁ = Bd-Cond1 a (<⇒≤ a₁)
... | tri≈ ¬a b ¬c₁ = Bd-Cond1 a (≤-reflexive b)
... | tri> ¬a ¬b₁ c = Bd-Cond2 (Cond1 c (<⇒≤ a))

module Def57 where
  pruned-bp : (S : Tree n)
            → (p : BranchingPoint S l)
            → .(bp-height p < pred (height-of-branching p))
            → BranchingPoint (prune-tree S p) l
  pruned-bp (Join S T) (BPExt p) q = BPExt (pruned-bp S p (≤-pred q))
  pruned-bp (Join S T) (BPShift p) q = BPShift (pruned-bp T p q)
  pruned-bp (Join (Join S Sing) T) BPHere q = BPHere ⦃ n-disc-is-linear (tree-dim S) ⦄
open Def57 public

module Lemma58Part1 where
  insertion-tree-pruned-bp : (S : Tree n)
                           → (p : BranchingPoint S l)
                           → (T : Tree m)
                           → .⦃ _ : has-linear-height (bp-height p) T ⦄
                           → .(q : bp-height p < pred (height-of-branching p))
                           → insertion-tree (prune-tree S p) (pruned-bp S p q) T ≃′ insertion-tree S p T
  insertion-tree-pruned-bp (Join S₁ S₂) (BPExt p) (Join T Sing) q = Join≃′ (insertion-tree-pruned-bp S₁ p T (≤-pred q)) refl≃′
  insertion-tree-pruned-bp (Join S₁ S₂) (BPShift p) T q = Join≃′ refl≃′ (insertion-tree-pruned-bp S₂ p T q)
  insertion-tree-pruned-bp (Join (Join S₁ Sing) S₂) BPHere T q = refl≃′


  pruned-bp-prop-2 : (S : Tree n)
                 → (p : BranchingPoint S l)
                 → .(q : bp-height p < pred (height-of-branching p))
                 → SPath (branching-path-to-path (pruned-bp S p q))
                 ≃stm interior-label S p (n-disc (pred (height-of-branching p))) ⦃ is-linear-has-linear-height l (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))) ⦄ (is-linear-max-path (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄)
  pruned-bp-prop-2 (Join S T) (BPExt p) q = compute-≃ (SExt≃ (pruned-bp-prop-2 S p (≤-pred q)) refl≃)
  pruned-bp-prop-2 (Join S T) (BPShift p) q = compute-≃ (SShift≃ refl≃ (pruned-bp-prop-2 T p q))
  pruned-bp-prop-2 (Join (Join S Sing) T) BPHere q = refl≃stm


  pruned-bp-prop : (S : Tree n)
                 → (p : BranchingPoint S l)
                 → (T : Tree m)
                 → .⦃ _ : has-linear-height l T ⦄
                 → .(q : bp-height p < pred (height-of-branching p))
                 → (L : Label X S)
                 → (M : Label-WT X T)
                 → (label-from-insertion S
                                             p
                                             (n-disc (pred (height-of-branching p)))
                                             ⦃ is-linear-has-linear-height l (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))) ⦄
                                             L
                                             (label-from-linear-tree-unbiased (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ T 0 ●l M)
                                             (branching-path-to-path (pruned-bp S p q)))
                 ≃stm (unbiased-comp′ (pred (height-of-branching p)) T >>= M)
  pruned-bp-prop (Join S₁ S₂) (BPExt p) (Join T Sing) q L M = let
    instance .x : has-linear-height (bp-height p) (n-disc (height-of-branching′ p))
    x = is-linear-has-linear-height (bp-height p) (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ (≤-pred q)) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p))))))
    instance _ = n-disc-is-linear (height-of-branching′ p)
    in begin
    < label-from-insertion S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄
         (L ∘ PExt)
         (label-from-linear-tree-unbiased (n-disc (height-of-branching′ p)) (Join T Sing) 1 ●l M)
         (branching-path-to-path (pruned-bp S₁ p _)) >stm
      ≈⟨ label-from-insertion-≃ S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄ refl≃l (label-comp-≃ (lfltu-susp (n-disc (height-of-branching′ p)) T 0) (refl≃l {L = ap M}) refl≃sty) .get (branching-path-to-path (pruned-bp S₁ p _)) ⟩
    < label-from-insertion S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄
         (L ∘ PExt)
         (label-from-linear-tree-unbiased (n-disc (height-of-branching′ p)) T 0 ●l (label₁ M))
         (branching-path-to-path (pruned-bp S₁ p _)) >stm
      ≈⟨ pruned-bp-prop S₁ p T (≤-pred q) (L ∘ PExt) (label₁ M) ⟩
    < unbiased-comp′ (pred (height-of-branching p)) T >>= label₁ M >stm ∎
    where
      open Reasoning stm-setoid
  pruned-bp-prop (Join S₁ S₂) (BPShift p) T q L M = pruned-bp-prop S₂ p T q (L ∘ PShift) M
  pruned-bp-prop (Join (Join S₁ Sing) S₂) BPHere T q L M = let
    instance _ = n-disc-is-linear (suc (tree-dim S₁))
    in begin
    < label-from-linear-tree-unbiased (n-disc (suc (tree-dim S₁))) T 0
         (is-linear-max-path (n-disc (suc (tree-dim S₁)))) >>= M >stm
      ≈⟨ >>=-≃ (lfltu-maximal-path (n-disc (suc (tree-dim S₁))) T 0 (is-linear-max-path (n-disc (suc (tree-dim S₁)))) ⦃ is-linear-max-path-max (n-disc (suc (tree-dim S₁))) ⦄) refl≃l refl≃sty ⟩
    < unbiased-comp′ (suc (tree-dim (n-disc (tree-dim S₁)))) T >>= M >stm
      ≈⟨ >>=-≃ (unbiased-comp′-≃ {d = suc (tree-dim (n-disc (tree-dim S₁)))} {d′ = suc (tree-dim S₁)} (cong suc (tree-dim-n-disc (tree-dim S₁))) (refl≃ {T = T})) (refl≃l {L = ap M}) refl≃sty ⟩
    < unbiased-comp′ (suc (tree-dim S₁)) T >>= M >stm ∎
    where
      open Reasoning stm-setoid

  pruned-bp-sub-from : (S : Tree n)
                     → (p : BranchingPoint S l)
                     → (T : Tree m)
                     → .⦃ _ : has-linear-height l T ⦄
                     → .(q : bp-height p < pred (height-of-branching p))
                     → (L : Label X S)
                     → (M : Label-WT X T)
                     → label-from-insertion (prune-tree S p) (pruned-bp S p q) T (label-from-insertion S
                                             p
                                             (n-disc (pred (height-of-branching p)))
                                             ⦃ is-linear-has-linear-height l (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))) ⦄
                                             L
                                             (label-from-linear-tree-unbiased (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ T 0 ●l M)) (ap M)
                     ≃lm label-≃ (insertion-tree-pruned-bp S p T q) (label-from-insertion S p T L (ap M))
  pruned-bp-sub-from (Join S₁ S₂) (BPExt p) (Join T Sing) q L M .get (PExt Z) = let
    instance .x : has-linear-height (bp-height p) (n-disc (height-of-branching′ p))
    x = is-linear-has-linear-height (bp-height p) (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ (≤-pred q)) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p))))))
    instance _ = n-disc-is-linear (height-of-branching′ p)
    in begin
    < label-from-insertion
         (prune-tree S₁ p)
         (pruned-bp S₁ p _) T
         (label-from-insertion S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄
            (L ∘ PExt)
            (label-from-linear-tree-unbiased (n-disc (height-of-branching′ p)) (Join T Sing) 1 ●l M))
         (ap M ∘ PExt) Z >stm
      ≈⟨ label-from-insertion-≃ (prune-tree S₁ p) (pruned-bp S₁ p _) T (label-from-insertion-≃ S₁ p (n-disc (pred (height-of-branching p))) ⦃ x ⦄ refl≃l (label-comp-≃ (lfltu-susp (n-disc (height-of-branching′ p)) T 0) refl≃l refl≃sty)) refl≃l .get Z ⟩
    < label-from-insertion
        (prune-tree S₁ p)
        (pruned-bp S₁ p _) T
        (label-from-insertion S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄
          (L ∘ PExt)
          (label-from-linear-tree-unbiased (n-disc (pred (height-of-branching p))) T 0 ●l label₁ M))
        (ap M ∘ PExt) Z >stm
      ≈⟨ pruned-bp-sub-from S₁ p T (≤-pred q) (L ∘ PExt) (label₁ M) .get Z ⟩
    < label-≃ (insertion-tree-pruned-bp S₁ p T _) (label-from-insertion S₁ p T (L ∘ PExt) (ap M ∘ PExt)) Z >stm ∎
    where
      open Reasoning stm-setoid
  pruned-bp-sub-from (Join S₁ S₂) (BPExt p) (Join T Sing) q L M .get (PShift Z) = replace-not-here (replace-label (L ∘ PShift) (ap M (PShift PHere))) (ap M (PShift PHere)) Z
  pruned-bp-sub-from (Join S₁ S₂) (BPShift p) T q L M .get (PExt Z) = refl≃stm
  pruned-bp-sub-from (Join S₁ S₂) (BPShift p) T q L M .get (PShift Z) = pruned-bp-sub-from S₂ p T q (L ∘ PShift) M .get Z
  pruned-bp-sub-from (Join (Join S₁ Sing) Sing) BPHere T q L M = ≃l-to-≃lm (connect-label-sing (ap M) _ _)
  pruned-bp-sub-from (Join (Join S₁ Sing) (Join S₂ S₃)) BPHere T q L M
    = connect-label-≃m (refl≃lm {L = ap M}) (replace-join-≃lm (L ∘ PShift) _)
open Lemma58Part1 public

module Lemma53 where
  insertion-linear-height : (S : Tree n)
                          → .⦃ non-linear S ⦄
                          → (P : BranchingPoint S l)
                          → (T : Tree m)
                          → .⦃ _ : has-linear-height l T ⦄
                          → (d : ℕ)
                          → .⦃ has-linear-height d S ⦄
                          → has-linear-height d (insertion-tree S P T)
  insertion-linear-height S P T zero = tt
  insertion-linear-height (Join S Sing) BPHere T (suc d) = ⊥-elim (linear-non-linear S)
  insertion-linear-height (Join S Sing) (BPExt P) (Join T Sing) (suc d) = insertion-linear-height S P T d
open Lemma53 public

module Def54 where
  inserted-bp : (S : Tree n)
              → (P : BranchingPoint S l)
              → (T : Tree m)
              → .⦃ _ : has-linear-height l T ⦄
              → .⦃ _ : non-linear T ⦄
              → (Q : BranchingPoint T l′)
              → BranchingPoint (insertion-tree S P T) l′
  inserted-bp (Join S₁ S₂) BPHere T Q = connect-bp-left T S₂ Q
  inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) BPHere = ⊥-elim (linear-non-linear T)
  inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) = BPExt (inserted-bp S₁ P T Q)
  inserted-bp (Join S₁ S₂) (BPShift P) T Q = BPShift (inserted-bp S₂ P T Q)
open Def54 public

module Lemma55Part1 where
  inserted-bp-prop : (S : Tree n)
                   → (P : BranchingPoint S l)
                   → (T : Tree m)
                   → .⦃ _ : has-linear-height l T ⦄
                   → .⦃ _ : non-linear T ⦄
                   → (Q : BranchingPoint T l′)
                   → SPath (branching-path-to-path (inserted-bp S P T Q))
                   ≃stm interior-label S P T (branching-path-to-path Q)
  inserted-bp-prop (Join S₁ S₂) BPHere T Q = connect-bp-left-prop T S₂ Q
  inserted-bp-prop (Join S₁ S₂) (BPExt P) (Join T Sing) BPHere = ⊥-elim (linear-non-linear T)
  inserted-bp-prop (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) = compute-≃ (SExt≃ (inserted-bp-prop S₁ P T Q) refl≃)
  inserted-bp-prop (Join S₁ S₂) (BPShift P) T Q = compute-≃ (SShift≃ refl≃ (inserted-bp-prop S₂ P T Q))

  insertion-tree-inserted-bp : (S : Tree n)
                             → (P : BranchingPoint S l)
                             → (T : Tree m)
                             → .⦃ _ : has-linear-height l T ⦄
                             → .⦃ _ : non-linear T ⦄
                             → (Q : BranchingPoint T l′)
                             → (U : Tree m′)
                             → .⦃ _ : has-linear-height l′ U ⦄
                             → insertion-tree (insertion-tree S P T) (inserted-bp S P T Q) U
                             ≃′ insertion-tree S P (insertion-tree T Q U) ⦃ insertion-linear-height T Q U l ⦄
  insertion-tree-inserted-bp (Join S₁ S₂) BPHere T Q U = insertion-bp-left T S₂ Q U
  insertion-tree-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) BPHere U = ⊥-elim (linear-non-linear T)
  insertion-tree-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) = Join≃′ (insertion-tree-inserted-bp S₁ P T Q U) refl≃′
  insertion-tree-inserted-bp (Join S₁ S₂) (BPShift P) T Q U = Join≃′ refl≃′ (insertion-tree-inserted-bp S₂ P T Q U)

  module _ where
    open Reasoning stm-setoid

    sub-from-inserted-bp : (S : Tree n)
                         → (P : BranchingPoint S l)
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height l T ⦄
                         → .⦃ _ : non-linear T ⦄
                         → (Q : BranchingPoint T l′)
                         → (U : Tree m′)
                         → .⦃ _ : has-linear-height l′ U ⦄
                         → (L : Label X S)
                         → (M : Label X T)
                         → (N : Label X U)
                         → label-from-insertion (insertion-tree S P T) (inserted-bp S P T Q) U (label-from-insertion S P T L M) N
                         ≃lm label-≃ (insertion-tree-inserted-bp S P T Q U) (label-from-insertion S P (insertion-tree T Q U) ⦃ insertion-linear-height T Q U l ⦄ L (label-from-insertion T Q U M N))
    sub-from-inserted-bp (Join S₁ S₂) BPHere T Q U L M N = sub-from-bp-left T S₂ Q U M (L ∘ PShift) N
    sub-from-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) BPHere U L M N = ⊥-elim (linear-non-linear T)
    sub-from-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) L M N .get (PExt Z) = sub-from-inserted-bp S₁ P T Q U (L ∘ PExt) (M ∘ PExt) (N ∘ PExt) .get Z
    sub-from-inserted-bp (Join S₁ .(Join _ _)) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) L M N .get (PShift (PExt Z)) = refl≃stm
    sub-from-inserted-bp (Join S₁ .(Join _ _)) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) L M N .get (PShift (PShift Z)) = refl≃stm
    sub-from-inserted-bp (Join S₁ S₂) (BPShift P) T Q U L M N .get (PExt Z) = refl≃stm
    sub-from-inserted-bp (Join S₁ S₂) (BPShift P) T Q U L M N .get (PShift Z) = sub-from-inserted-bp S₂ P T Q U (L ∘ PShift) M N .get Z
open Lemma55Part1 public
-}
