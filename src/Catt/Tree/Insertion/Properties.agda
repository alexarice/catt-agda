module Catt.Tree.Insertion.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Globular

branching-path-to-var-is-var : (S : Tree n) → (p : BranchingPoint S) → isVar (branching-path-to-var S p)
branching-path-to-var-is-var (Join S T) BPHere = var-to-var-comp-tm 0V (connect-susp-inc-left (tree-size S) (tree-size T)) ⦃ connect-susp-inc-left-var-to-var (tree-size S) (tree-size T) ⦄
branching-path-to-var-is-var (Join S T) (BPExt P) = var-to-var-comp-tm (suspTm (branching-path-to-var S P)) ⦃ suspTm-var (branching-path-to-var S P) ⦃ branching-path-to-var-is-var S P ⦄ ⦄ (connect-susp-inc-left (tree-size S) (tree-size T)) ⦃ connect-susp-inc-left-var-to-var (tree-size S) (tree-size T) ⦄
branching-path-to-var-is-var (Join S T) (BPShift P) = var-to-var-comp-tm (branching-path-to-var T P) ⦃ branching-path-to-var-is-var T P ⦄ (connect-susp-inc-right (tree-size S) (tree-size T)) ⦃ connect-susp-inc-right-var-to-var (tree-size S) (tree-size T) ⦄

height-of-branching-non-zero : (S : Tree n) → (p : BranchingPoint S) → NonZero (height-of-branching p)
height-of-branching-non-zero (Join S T) BPHere = it
height-of-branching-non-zero (Join S T) (BPExt P) = it
height-of-branching-non-zero (Join S T) (BPShift P) = height-of-branching-non-zero T P

exterior-sub-label-phere : (S : Tree n)
                         → (p : BranchingPoint S)
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height (bp-height p) T ⦄
                         → ap (exterior-sub-label S p T) PHere ≃stm SHere {S = insertion-tree S p T}
exterior-sub-label-phere (Join S₁ S₂) BPHere T = connect-tree-inc-left-phere T S₂
exterior-sub-label-phere (Join S₁ S₂) (BPExt p) (Join T Sing) = refl≃stm
exterior-sub-label-phere (Join S₁ S₂) (BPShift p) T = refl≃stm

module _ where
  open Reasoning stm-setoid

  exterior-sub-label-last-path : (S : Tree n)
                               → (p : BranchingPoint S)
                               → (T : Tree m)
                               → .⦃ _ : has-linear-height (bp-height p) T ⦄
                               → ap (exterior-sub-label S p T) (last-path S) ≃stm path-to-stm (last-path (insertion-tree S p T))
  exterior-sub-label-last-path (Join S₁ S₂) (BPExt p) (Join T Sing) = refl≃stm
  exterior-sub-label-last-path (Join S₁ S₂) (BPShift p) T = ≃SShift refl≃ (exterior-sub-label-last-path S₂ p T)
  exterior-sub-label-last-path (Join S₁ Sing) BPHere T = begin
    < path-to-stm (last-path T) >>= connect-tree-inc-left T Sing >stm
      ≈⟨ extend-path-to-stm (last-path T) (connect-tree-inc-left T Sing) ⟩
    < ap (connect-tree-inc-left T Sing) (last-path T) >stm
      ≈⟨ connect-tree-inc-phere T Sing ⟩
    < ap (connect-tree-inc-right T Sing) PHere >stm
      ≈⟨ connect-tree-inc-right-last-path T Sing ⟩
    < path-to-stm (last-path (connect-tree T Sing)) >stm ∎
  exterior-sub-label-last-path (Join S₁ S₂@(Join S₃ S₄)) BPHere T = begin
    < path-to-stm (last-path S₂) >>= connect-tree-inc-right T S₂ >stm
      ≈⟨ extend-path-to-stm (last-path S₂) (connect-tree-inc-right T S₂) ⟩
    < ap (connect-tree-inc-right T S₂) (last-path S₂) >stm
      ≈⟨ connect-tree-inc-right-last-path T S₂ ⟩
    < path-to-stm (last-path (connect-tree T (Join S₃ S₄))) >stm ∎

  interior-sub-label-comm : (S : Tree n)
                          → (p : BranchingPoint S)
                          → (T : Tree m)
                          → .⦃ _ : has-linear-height (bp-height p) T ⦄
                          → (L : Label X S A)
                          → (M : Label X T A)
                          → label-comp (interior-sub-label S p T) (sub-from-insertion-label S p T L M) ≃lm M
  interior-sub-label-comm (Join S₁ S₂) BPHere T L M .get Z = connect-label-inc-left M (label₂ L) .get Z
  interior-sub-label-comm (Join S₁ S₂) (BPExt p) (Join T Sing) L M .get (PExt Z)
    = interior-sub-label-comm S₁ p T (convert-type (label₁ L) (apt M PHere ─⟨ _ ⟩⟶ apt M (PShift PHere))) (label₁ M) .get Z
  interior-sub-label-comm (Join S₁ S₂) (BPExt p) (Join T Sing) L M .get (PShift PHere) = ⊥-elim (proj₁ it)
  interior-sub-label-comm (Join S₁ S₂) (BPShift p) T L M = interior-sub-label-comm S₂ p T (label₂ L) M

  exterior-sub-label-comm : (S : Tree n)
                          → (p : BranchingPoint S)
                          → (T : Tree m)
                          → .⦃ _ : has-linear-height (bp-height p) T ⦄
                          → (L : Label X S A)
                          → (M : Label X T A)
                          → ap L (branching-path-to-path S p) ≃stm (unbiased-comp′ (height-of-branching p) T >>= M)
                          → label-comp (exterior-sub-label S p T) (sub-from-insertion-label S p T L M) ≃lm L
  exterior-sub-label-comm (Join S₁ S₂) BPHere T L M q .get (PExt Z) = begin
    < label-from-linear-tree-unbiased S₁ T 1 .ap Z >>= connect-tree-inc-left T S₂ >>= connect-label M (label₂ L) >stm
      ≈⟨ extend-assoc (label-from-linear-tree-unbiased S₁ T 1 .ap Z) (connect-tree-inc-left T S₂) (connect-label M (label₂ L)) ⟩
    < label-from-linear-tree-unbiased S₁ T 1 .ap Z >>= label-comp (connect-tree-inc-left T S₂) (connect-label M (label₂ L)) >stm
      ≈⟨ extend-≃ (label-from-linear-tree-unbiased-maximal-path S₁ T 1 Z) (connect-label-inc-left M (label₂ L)) refl≃ty ⟩
    < unbiased-comp′ (1 + tree-dim S₁) T >>= M >stm
      ≈˘⟨ q ⟩
    < ap L (branching-path-to-path (Join S₁ S₂) BPHere) >stm
      ≈⟨ reflexive≃stm (cong (λ P → (ap L (PExt P))) (max-path-lin-tree S₁ Z)) ⟩
    < ap L (PExt Z) >stm ∎
  exterior-sub-label-comm (Join S₁ S₂) BPHere T L M q .get (PShift Z) = begin
    < replace-label (label-comp (id-label S₂) (connect-tree-inc-right T S₂)) (path-to-stm (last-path T) >>= connect-tree-inc-left T S₂) .ap Z >>= connect-label M (label₂ L) >stm
      ≈⟨ extend-≃ (replace-not-here (label-comp (id-label S₂) (connect-tree-inc-right T S₂)) (path-to-stm (last-path T) >>= connect-tree-inc-left T S₂) Z ⦃ proj₁ it ⦄) refl≃l refl≃ty ⟩
    < ap (label-comp (id-label S₂) (connect-tree-inc-right T S₂)) Z >>= connect-label M (label₂ L) >stm
      ≈⟨ extend-≃ (extend-path-to-stm Z (connect-tree-inc-right T S₂)) refl≃l refl≃ty ⟩
    < ap (connect-tree-inc-right T S₂) Z >>= connect-label M (label₂ L) >stm
      ≈⟨ connect-label-inc-right M (label₂ L) Z ⦃ proj₁ it ⦄ ⦃ proj₂ it ⦄ ⟩
    < ap (label₂ L) Z >stm ∎
  exterior-sub-label-comm (Join S₁ S₂) (BPExt p) (Join T Sing) L M q .get (PExt Z) = exterior-sub-label-comm S₁ p T (convert-type (label₁ L) (apt M PHere ─⟨ _ ⟩⟶ apt M (PShift PHere))) (label₁ M) q .get Z
  exterior-sub-label-comm (Join S₁ S₂) (BPExt p) (Join T Sing) L M q .get (PShift Z) = trans≃stm (extend-path-to-stm Z (label₂ (sub-from-insertion-label (Join S₁ S₂) (BPExt p) (Join T Sing) L M))) (replace-not-here (label₂ L) (ap M (PShift PHere)) Z ⦃ proj₁ it ⦄)
  exterior-sub-label-comm (Join S₁ S₂) (BPShift p) T L M q .get (PExt Z) = extend-path-to-stm Z (label₁ (sub-from-insertion-label (Join S₁ S₂) (BPShift p) T L M))
  exterior-sub-label-comm (Join S₁ S₂) (BPShift p) T L M q .get (PShift Z) = exterior-sub-label-comm S₂ p T (label₂ L) M q .get Z ⦃ proj₂ it ⦄

  insertion-bd-1 : (S : Tree n)
               → (p : BranchingPoint S)
               → (T : Tree m)
               → .⦃ _ : has-linear-height (bp-height p) T ⦄
               → (d : ℕ)
               → (d ≤ bp-height p)
               → tree-bd d S ≃ tree-bd d (insertion-tree S p T)
  insertion-bd-1 S p T zero q = refl≃
  insertion-bd-1 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) q = Join≃ (insertion-bd-1 S₁ p T d (≤-pred q)) refl≃
  insertion-bd-1 (Join S₁ S₂) (BPShift p) T (suc d) q = Join≃ refl≃ (insertion-bd-1 S₂ p T (suc d) q)

  unbiased-exterior-comm-1 : (S : Tree n)
                         → (p : BranchingPoint S)
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height (bp-height p) T ⦄
                         → (d : ℕ)
                         → (q : d ≤ bp-height p)
                         → (b : Bool)
                         → prepend (tree-inc-label′ d S b) (exterior-sub-label S p T) ≃lm label-≃ (insertion-bd-1 S p T d q) (tree-inc-label d (insertion-tree S p T) b)
  unbiased-exterior-comm-1 S p T zero q false .get Z = exterior-sub-label-phere S p T
  unbiased-exterior-comm-1 S p T zero q true .get Z = exterior-sub-label-last-path S p T
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) q b .get (PExt Z)
    = ≃SExt (unbiased-exterior-comm-1 S₁ p T d (≤-pred q) b .get Z) refl≃
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) q b .get (PShift Z)
    = reflexive≃stm (cong (λ - → SShift (path-to-stm (tree-inc-label′ (suc d) S₂ b -))) (sym (ppath-refl Z)))
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPShift p) T (suc d) q b .get (PExt Z)
    = reflexive≃stm (cong (λ - → SExt (path-to-stm (tree-inc-label′ d S₁ b -))) (sym (ppath-refl Z)))
  unbiased-exterior-comm-1 (Join S₁ S₂) (BPShift p) T (suc d) q b .get (PShift Z)
    = ≃SShift refl≃ (unbiased-exterior-comm-1 S₂ p T (suc d) q b .get Z ⦃ proj₂ it ⦄)

  bd-branching-point : (S : Tree n)
                     → (p : BranchingPoint S)
                     → (d : ℕ)
                     → (q : d > bp-height p)
                     → BranchingPoint (tree-bd d S)
  bd-branching-point (Join S₁ S₂) BPHere (suc d) q = BPHere ⦃ is-linear-bd d S₁ ⦄
  bd-branching-point (Join S₁ S₂) (BPExt p) (suc d) q = BPExt (bd-branching-point S₁ p d (≤-pred q))
  bd-branching-point (Join S₁ S₂) (BPShift p) (suc d) q = BPShift (bd-branching-point S₂ p (suc d) q)

  bd-branching-point-height : (S : Tree n)
                            → (p : BranchingPoint S)
                            → (d : ℕ)
                            → (q : d > bp-height p)
                            → bp-height (bd-branching-point S p d q) ≡ bp-height p
  bd-branching-point-height (Join S₁ S₂) BPHere (suc d) q = refl
  bd-branching-point-height (Join S₁ S₂) (BPExt p) (suc d) q = cong suc (bd-branching-point-height S₁ p d (≤-pred q))
  bd-branching-point-height (Join S₁ S₂) (BPShift p) (suc d) q = bd-branching-point-height S₂ p (suc d) q

  bd-has-linear-height : (d : ℕ) → (m : ℕ)
                       → (T : Tree n) → .⦃ has-linear-height m T ⦄
                       → d > m
                       → has-linear-height m (tree-bd d T)
  bd-has-linear-height d zero T q = tt
  bd-has-linear-height (suc d) (suc m) (Join T Sing) q = bd-has-linear-height d m T (≤-pred q)

  bd-bp-height : (S : Tree n)
               → (p : BranchingPoint S)
               → (T : Tree m)
               → .⦃ _ : has-linear-height (bp-height p) T ⦄
               → (d : ℕ)
               → (q : d > bp-height p)
               → has-linear-height (bp-height (bd-branching-point S p d q)) (tree-bd d T)
  bd-bp-height S p T d q = subst (λ - → has-linear-height - (tree-bd d T))
                                 (sym (bd-branching-point-height S p d q))
                                 (bd-has-linear-height d (bp-height p) T q)

  insertion-bd-2 : (S : Tree n)
                 → (p : BranchingPoint S)
                 → (T : Tree m)
                 → .⦃ _ : has-linear-height (bp-height p) T ⦄
                 → (d : ℕ)
                 → (q : d > bp-height p)
                 → insertion-tree (tree-bd d S)
                                  (bd-branching-point S p d q)
                                  (tree-bd d T)
                                  ⦃ bd-bp-height S p T d q ⦄
                   ≃ tree-bd d (insertion-tree S p T)
  insertion-bd-2 (Join S₁ S₂) BPHere T (suc d) q = connect-tree-bd d T S₂
  insertion-bd-2 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) q
    = Join≃ (insertion-bd-2 S₁ p T d (≤-pred q)) refl≃
  insertion-bd-2 (Join S₁ S₂) (BPShift p) T (suc d) q
    = Join≃ refl≃ (insertion-bd-2 S₂ p T (suc d) q)

  unbiased-exterior-comm-2 : (S : Tree n)
                           → (p : BranchingPoint S)
                           → (T : Tree m)
                           → .⦃ _ : has-linear-height (bp-height p) T ⦄
                           → (d : ℕ)
                           → (q : d > bp-height p)
                           → (b : Bool)
                           → prepend (tree-inc-label′ d S b) (exterior-sub-label S p T)
                           ≃lm label-comp (exterior-sub-label (tree-bd d S)
                                                              (bd-branching-point S p d q)
                                                              (tree-bd d T)
                                                              ⦃ bd-bp-height S p T d q ⦄)
                                          (label-≃ (insertion-bd-2 S p T d q) (tree-inc-label d (insertion-tree S p T) b))
  unbiased-exterior-comm-2 (Join S₁ S₂) BPHere T (suc d) q b .get (PExt Z) = ?
  unbiased-exterior-comm-2 (Join S₁ S₂) BPHere T (suc d) q b .get (PShift Z) = ?
  unbiased-exterior-comm-2 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) q b .get (PExt Z) = let
    instance _ = bd-bp-height S₁ p T d (≤-pred q)
    in begin
    < SExt (ap (exterior-sub-label S₁ p T) (tree-inc-label′ d S₁ b Z)) >stm
      ≈⟨ ≃SExt (unbiased-exterior-comm-2 S₁ p T d (≤-pred q) b .get Z) refl≃ ⟩
    < SExt (ap (label-comp (exterior-sub-label (tree-bd d S₁)
                                               (bd-branching-point S₁ p d (≤-pred q))
                                               (tree-bd d T))
               (label-≃ (insertion-bd-2 S₁ p T d (≤-pred q))
                        (tree-inc-label d (insertion-tree S₁ p T) b))) Z) >stm
      ≈˘⟨ extend-map-pext (ap (exterior-sub-label (tree-bd d S₁) (bd-branching-point S₁ p d (≤-pred q)) (tree-bd d T)) Z) (label-≃ (insertion-bd-2 S₁ p T d (≤-pred q)) (tree-inc-label d (insertion-tree S₁ p T) b)) ⟩
    < ap (exterior-sub-label (tree-bd d S₁) (bd-branching-point S₁ p d (≤-pred q)) (tree-bd d T)) Z
       >>= map-pext {T = S₂} (label-≃ (insertion-bd-2 S₁ p T d (≤-pred q)) (tree-inc-label d (insertion-tree S₁ p T) b)) >stm
      ≈⟨ extend-≃ (refl≃stm {a = ap (exterior-sub-label (tree-bd d S₁) (bd-branching-point S₁ p d (≤-pred q)) (tree-bd d T)) Z}) [ (λ P → refl≃stm) ] (Arr≃ (connect-inc-left-fst-var getSnd _) refl≃ty (trans≃tm (connect-inc-fst-var getSnd (tree-size S₂)) (sub-action-≃-tm (sym≃tm (tree-inc-label-phere d S₂ b .get)) refl≃s))) ⟩
    < ap (exterior-sub-label (tree-bd d S₁) (bd-branching-point S₁ p d (≤-pred q)) (tree-bd d T)) Z
       >>= label₁ (label-≃ (Join≃ (insertion-bd-2 S₁ p T d (≤-pred q)) refl≃) (tree-inc-label (suc d) (Join (insertion-tree S₁ p T) S₂) b)) >stm ∎
  unbiased-exterior-comm-2 (Join S₁ S₂) (BPExt p) (Join T Sing) (suc d) q b .get (PShift Z) = begin
    < SShift (path-to-stm (tree-inc-label′ (suc d) S₂ b Z)) >stm
      ≈˘⟨ reflexive≃stm (cong (λ - → SShift (path-to-stm (tree-inc-label′ (suc d) S₂ b -))) (ppath-refl Z)) ⟩
    < SShift (path-to-stm (tree-inc-label′ (suc d) S₂ b (ppath-≃ refl≃ Z))) >stm
      ≈˘⟨ extend-path-to-stm Z _ ⟩
    < path-to-stm Z >>=
       label₂ (label-≃ (Join≃ (insertion-bd-2 S₁ p T d (≤-pred q)) refl≃) (tree-inc-label (suc d) (Join (insertion-tree S₁ p T) S₂) b)) >stm ∎
  unbiased-exterior-comm-2 (Join S₁ S₂) (BPShift p) T (suc d) q b .get (PExt Z) = begin
    < SExt (path-to-stm (tree-inc-label′ d S₁ b Z)) >stm
      ≈˘⟨ reflexive≃stm (cong (λ - → SExt (path-to-stm (tree-inc-label′ d S₁ b -))) (ppath-refl Z)) ⟩
    < SExt (path-to-stm (tree-inc-label′ d S₁ b (ppath-≃ refl≃ Z))) >stm
      ≈˘⟨ extend-path-to-stm Z (label₁
                                 (label-≃ (Join≃ refl≃ (insertion-bd-2 S₂ p T (suc d) q))
                                  (tree-inc-label (suc d) (Join S₁ (insertion-tree S₂ p T)) b))) ⟩
    < path-to-stm Z >>= label₁ (label-≃ (Join≃ refl≃ (insertion-bd-2 S₂ p T (suc d) q)) (tree-inc-label (suc d) (Join S₁ (insertion-tree S₂ p T)) b)) >stm ∎
  unbiased-exterior-comm-2 (Join S₁ S₂) (BPShift p) T (suc d) q b .get (PShift Z) = let
    instance _ = bd-bp-height S₂ p T (suc d) q
    in begin
    < SShift (ap (exterior-sub-label S₂ p T) (tree-inc-label′ (suc d) S₂ b Z)) >stm
      ≈⟨ ≃SShift refl≃ (unbiased-exterior-comm-2 S₂ p T (suc d) q b .get Z ⦃ proj₂ it ⦄) ⟩
    < SShift (ap (exterior-sub-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) q) (tree-bd (suc d) T)) Z
        >>= label-≃ (insertion-bd-2 S₂ p T (suc d) q) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) >stm
      ≈˘⟨ extend-map-pshift (ap (exterior-sub-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) q) (tree-bd (suc d) T)) Z) (label-≃ (insertion-bd-2 S₂ p T (suc d) q) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) ⟩
    < ap (exterior-sub-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) q) (tree-bd (suc d) T)) Z
       >>= map-pshift (label-≃ (insertion-bd-2 S₂ p T (suc d) q) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) >stm
      ≡⟨⟩
    < ap (exterior-sub-label (tree-bd (suc d) S₂) (bd-branching-point S₂ p (suc d) q) (tree-bd (suc d) T)) Z
       >>= label₂ (label-≃ (Join≃ refl≃ (insertion-bd-2 S₂ p T (suc d) q))
                           (tree-inc-label (suc d) (Join S₁ (insertion-tree S₂ p T)) b)) >stm ∎

{-
exterior-sub-fst-var : (S : Tree n)
                     → (P : Path S)
                     → .⦃ bp : is-branching-path  ⦄
                     → (T : Tree m)
                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                     → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                     → Var {suc (insertion-tree-size S P T)} (fromℕ _) ≃tm Var (fromℕ _) [ exterior-sub S P T ]tm
exterior-sub-fst-var (Join S₁ S₂) PHere T = begin
  < Var (fromℕ (insertion-tree-size (Join S₁ S₂) PHere T)) >tm
    ≈˘⟨ idSub≃-fst-var (sym≃c (connect-tree-to-ctx T S₂)) ⟩
  < Var (fromℕ _) [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (sub-between-connects-fst-var (sub-from-linear-tree-unbiased (suspTree S₁) T 0) idSub (tree-last-var T) (unrestrict-fst (sub-from-linear-tree-unbiased S₁ T 1))) (refl≃s {σ = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))}) ⟩
  < Var (fromℕ _)
    [ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T) ]tm
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ]tm
    >tm
    ≈˘⟨ assoc-tm (idSub≃ (sym≃c (connect-tree-to-ctx T S₂))) (sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)) (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T) ]tm >tm ≡⟨⟩
  < Var (fromℕ _) [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm ∎
  where
    open Reasoning tm-setoid

exterior-sub-fst-var (Join S₁ S₂) (PExt P) (Join T Sing) = sym≃tm (sub-between-connect-susps-fst-var (exterior-sub S₁ P T) idSub)

exterior-sub-fst-var (Join S₁ S₂) (PShift P) T = sym≃tm (sub-between-connect-susps-fst-var idSub (exterior-sub S₂ P T))

exterior-sub-last-var : (S : Tree n)
                     → (P : Path S)
                     → .⦃ bp : is-branching-path P ⦄
                     → (T : Tree m)
                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                     → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                     → tree-last-var (insertion-tree S P T) ≃tm tree-last-var S [ exterior-sub S P T ]tm
exterior-sub-last-var (Join S₁ S₂) PHere T = begin
  < tree-last-var (connect-tree T S₂) >tm
    ≈⟨ connect-tree-last-var T S₂ ⟩
  < tree-last-var S₂
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ connect-inc-right (tree-last-var T) (tree-size S₂) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-action-≃-sub (id-right-unit (connect-inc-right (tree-last-var T) (tree-size S₂))) refl≃s) ⟩
  < tree-last-var S₂
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ (connect-inc-right (tree-last-var T) (tree-size S₂) ∘ idSub) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-action-≃-sub (sub-between-connects-inc-right (sub-from-linear-tree-unbiased (suspTree S₁) T 0) getSnd idSub (tree-last-var T) (unrestrict-snd (sub-from-linear-tree-unbiased S₁ T 1)) (id-on-tm (Var (fromℕ _)))) refl≃s) ⟩
  < tree-last-var S₂
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ (sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)
      ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (∘-assoc _ _ _) ⟩
  < tree-last-var S₂
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
  < tree-last-var S₂
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T) ]tm >tm ∎
  where
    open Reasoning tm-setoid

exterior-sub-last-var (Join S₁ S₂) (PExt P) (Join T Sing) = begin
  < tree-last-var S₂
    [ connect-susp-inc-right (tree-size (insertion-tree S₁ P T)) (tree-size S₂) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (id-right-unit (connect-susp-inc-right (insertion-tree-size S₁ P T) _)) ⟩
  < tree-last-var S₂ [ connect-susp-inc-right (insertion-tree-size S₁ P T) _
                     ∘ idSub ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-between-connect-susps-inc-right (exterior-sub S₁ P T) idSub (id-on-tm (Var (fromℕ _)))) ⟩
  < tree-last-var S₂
    [ sub-between-connect-susps (exterior-sub S₁ P T) idSub
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
  < tree-last-var S₂
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps (exterior-sub S₁ P T) idSub ]tm >tm ∎
  where
    open Reasoning tm-setoid
exterior-sub-last-var (Join S₁ S₂) (PShift P) T = begin
  < tree-last-var (insertion-tree S₂ P T)
    [ connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (exterior-sub-last-var S₂ P T) refl≃s ⟩
  < tree-last-var S₂ [ exterior-sub S₂ P T ]tm
                     [ connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
  < tree-last-var S₂
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T)
    ∘ exterior-sub S₂ P T ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var S₂}) (sub-between-connect-susps-inc-right idSub (exterior-sub S₂ P T) (sym≃tm (exterior-sub-fst-var S₂ P T))) ⟩
  < tree-last-var S₂
    [ sub-between-connect-susps idSub (exterior-sub S₂ P T)
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var S₂) ⟩
  < tree-last-var S₂
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps idSub (exterior-sub S₂ P T) ]tm >tm ∎
  where
    open Reasoning tm-setoid


insertion-eq : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
             → branching-path-to-var S P [ exterior-sub S P T ]tm ≃tm Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub S P T)
insertion-eq (Join S₁ S₂) PHere T = begin
  < 0V [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
       [ exterior-sub (Join S₁ S₂) PHere T ]tm >tm
    ≈˘⟨ assoc-tm _ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) 0V ⟩
  < 0V [ exterior-sub (Join S₁ S₂) PHere T
       ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (∘-assoc _ _ (connect-susp-inc-left (tree-size S₁) (tree-size S₂))) ⟩
  < 0V [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
       ∘ (sub-between-connects (sub-from-linear-tree-unbiased (suspTree S₁) T 0)
                           idSub
                           (tree-last-var T)
         ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (sub-action-≃-sub (sub-between-connects-inc-left (sub-from-linear-tree-unbiased (suspTree S₁) T 0) getSnd idSub (tree-last-var T)) (refl≃s {σ = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))})) ⟩
  < 0V [ idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
       ∘ (connect-inc-left (tree-last-var T) _
       ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (idSub≃-on-sub (sym≃c (connect-tree-to-ctx T S₂)) (connect-inc-left (tree-last-var T) _
       ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0)) ⟩
  < 0V [ connect-inc-left (tree-last-var T) _
       ∘ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm >tm
    ≈⟨ assoc-tm (connect-inc-left (tree-last-var T) _) (sub-from-linear-tree-unbiased (suspTree S₁) T 0) 0V ⟩
  < 0V [ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm
       [ connect-inc-left (tree-last-var T) _ ]tm >tm
    ≈⟨ sub-action-≃-tm (sub-from-linear-tree-unbiased-0V (suspTree S₁) T 0) refl≃s ⟩
  < unbiased-comp (tree-dim (suspTree S₁)) T [ connect-inc-left (tree-last-var T) _ ]tm >tm
    ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim (suspTree S₁)) T) (connect-inc-left (tree-last-var T) _ ∘ idSub) >tm
    ≈⟨ Coh≃ refl≃c (unbiased-type-≃ (recompute ((suc (tree-dim S₁)) ≟ (tree-dim T)) it) refl≃) lem ⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T)
      (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
       connect-inc-left (tree-last-var T) _) >tm
    ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub (Join S₁ S₂) PHere T) >tm ∎
  where
    lem : connect-inc-left (tree-last-var T) _ ∘ idSub
          ≃s idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _
    lem = begin
      < connect-inc-left (tree-last-var T) _ ∘ idSub >s
        ≈⟨ id-right-unit (connect-inc-left (tree-last-var T) _) ⟩
      < connect-inc-left (tree-last-var T) _ >s
        ≈˘⟨ idSub≃-on-sub (sym≃c (connect-tree-to-ctx T S₂)) (connect-inc-left (tree-last-var T) _) ⟩
      < idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _ >s ∎
      where
        open Reasoning sub-setoid
    open Reasoning tm-setoid

insertion-eq (Join S₁ S₂) (PExt P) (Join T Sing) ⦃ p = p ⦄ = let
  instance .x : _
           x = cong pred p
  in begin
  < suspTm (branching-path-to-var S₁ P)
    [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps (exterior-sub S₁ P T) idSub ]tm >tm
    ≈˘⟨ assoc-tm _ _ (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
    [ sub-between-connect-susps (exterior-sub S₁ P T) idSub
    ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (branching-path-to-var S₁ P)}) (sub-between-connect-susps-inc-left (exterior-sub S₁ P T) idSub) ⟩
  < suspTm (branching-path-to-var S₁ P)
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _
    ∘ suspSub (exterior-sub S₁ P T) ]tm
    >tm
    ≈⟨ assoc-tm _ _ (suspTm (branching-path-to-var S₁ P)) ⟩
  < suspTm (branching-path-to-var S₁ P)
    [ suspSub (exterior-sub S₁ P T) ]tm
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈˘⟨ sub-action-≃-tm (susp-functorial-tm (exterior-sub S₁ P T) (branching-path-to-var S₁ P)) refl≃s ⟩
  < suspTm (branching-path-to-var S₁ P [ exterior-sub S₁ P T ]tm)
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ sub-action-≃-tm (susp-tm-≃ (insertion-eq S₁ P T)) refl≃s ⟩
  < suspTm (Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub S₁ P T))
    [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]tm >tm
    ≈⟨ Coh≃ refl≃c (unbiased-type-susp-lem (tree-dim T) T) refl≃s ⟩
  < Coh (suspCtx (tree-to-ctx T)) (unbiased-type (tree-dim (Join T Sing)) (Join T Sing)) (interior-sub (Join S₁ S₂) (PExt P) (Join T Sing)) >tm ∎
  where
    open Reasoning tm-setoid

insertion-eq (Join S₁ S₂) (PShift P) T = begin
  < branching-path-to-var S₂ P
    [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
    [ sub-between-connect-susps idSub (exterior-sub S₂ P T) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P
    [ sub-between-connect-susps idSub (exterior-sub S₂ P T)
    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = branching-path-to-var S₂ P}) (sub-between-connect-susps-inc-right idSub (exterior-sub S₂ P T) (sym≃tm (exterior-sub-fst-var S₂ P T))) ⟩
  < branching-path-to-var S₂ P
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T)
    ∘ exterior-sub S₂ P T ]tm >tm
    ≈⟨ assoc-tm _ _ (branching-path-to-var S₂ P) ⟩
  < branching-path-to-var S₂ P [ exterior-sub S₂ P T ]tm
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]tm >tm
    ≈⟨ sub-action-≃-tm (insertion-eq S₂ P T) refl≃s ⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub S₂ P T)
    [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]tm >tm
    ≡⟨⟩
  < Coh (tree-to-ctx T) (unbiased-type (tree-dim T) T) (interior-sub (Join S₁ S₂) (PShift P) T) >tm ∎
  where
    open Reasoning tm-setoid

exterior-sub-susp : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → exterior-sub (suspTree S) (PExt P) (suspTree T) ≃s suspSub (exterior-sub S P T)
exterior-sub-susp S P T = begin
  < exterior-sub (suspTree S) (PExt P) (suspTree T) >s ≡⟨⟩
  < idSub ∘ suspSub (exterior-sub S P T) >s
    ≈⟨ id-left-unit (suspSub (exterior-sub S P T)) ⟩
  < suspSub (exterior-sub S P T) >s ∎
    where
      open Reasoning sub-setoid

sub-from-insertion-≃ : (S : Tree n)
                     → (P : Path S)
                     → .⦃ bp : is-branching-path P ⦄
                     → (T : Tree m)
                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                     → σ ≃s σ′ → τ ≃s τ′
                     → sub-from-insertion S P T σ τ ≃s sub-from-insertion S P T σ′ τ′
sub-from-insertion-≃ (Join S₁ S₂) PHere T p q = sub-action-≃-sub refl≃s (sub-from-connect-≃ q (sub-action-≃-sub refl≃s p))
sub-from-insertion-≃ (Join S₁ S₂) (PExt P) (Join T Sing) p q = sub-from-connect-≃ (unrestrict-≃ (sub-from-insertion-≃ S₁ P T (restrict-≃ (sub-action-≃-sub refl≃s p) (sub-action-≃-tm (refl≃tm {s = getFst}) q) (sub-action-≃-tm (refl≃tm {s = getSnd}) q)) (restrict-≃ q (sub-action-≃-tm (refl≃tm {s = getFst}) q) (sub-action-≃-tm (refl≃tm {s = getSnd}) q)))) (sub-action-≃-sub refl≃s p)
sub-from-insertion-≃ (Join S₁ S₂) (PShift P) T p q = sub-from-connect-≃ (sub-action-≃-sub refl≃s p) (sub-from-insertion-≃ S₂ P T (sub-action-≃-sub refl≃s p) q)

lift-sub-from-insertion : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l A)
                        → (τ : Sub (suc m) l A)
                        → liftSub (sub-from-insertion S P T σ τ) ≃s sub-from-insertion S P T (liftSub σ) (liftSub τ)
lift-sub-from-insertion (Join S₁ S₂) PHere T σ τ = begin
  < liftSub (sub-from-connect τ
                              (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
            ∘ idSub≃ (connect-tree-to-ctx T S₂)) >s
    ≈˘⟨ apply-lifted-sub-sub-≃ _ _ ⟩
  < liftSub (sub-from-connect τ
                              (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-connect-lift τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  < sub-from-connect (liftSub τ)
                     (liftSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ sub-action-≃-sub refl≃s (sub-from-connect-≃ refl≃s (apply-lifted-sub-sub-≃ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) σ)) ⟩
  < sub-from-connect (liftSub τ)
                     (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s ∎
  where
    open Reasoning sub-setoid

lift-sub-from-insertion (Join S₁ S₂) (PExt P) (Join T Sing) σ τ = begin
  < liftSub (sub-from-connect
      (unrestrict (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s
    ≈⟨ sub-from-connect-lift _ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ⟩
  < sub-from-connect
      (liftSub (unrestrict
        (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))))
      (liftSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s
    ≈˘⟨ sub-from-connect-≃ lem (apply-lifted-sub-sub-≃ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) σ) ⟩
  < sub-from-connect
      (unrestrict
        (sub-from-insertion S₁ P T
          (restrict (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ liftSub τ ]tm)
                    (getSnd [ liftSub τ ]tm))
          (restrict (liftSub τ) (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm))))
      (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s ∎
  where
    open Reasoning sub-setoid

    l1 : restrict (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ liftSub τ ]tm)
                  (getSnd [ liftSub τ ]tm)
         ≃s
         liftSub (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                           (getFst [ τ ]tm)
                           (getSnd [ τ ]tm))
    l1 = begin
      < restrict (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                 (getFst [ liftSub τ ]tm)
                 (getSnd [ liftSub τ ]tm) >s
        ≈⟨ restrict-≃ (apply-lifted-sub-sub-≃ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) σ) (apply-lifted-sub-tm-≃ getFst τ) (apply-lifted-sub-tm-≃ getSnd τ) ⟩
      < restrict (liftSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
                 (liftTerm (getFst [ τ ]tm))
                 (liftTerm (getSnd [ τ ]tm)) >s
        ≈⟨ restrict-lift _ _ _ ⟩
      < liftSub (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                          (getFst [ τ ]tm)
                          (getSnd [ τ ]tm)) >s ∎

    l2 : restrict (liftSub τ) (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm)
         ≃s liftSub (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l2 = begin
      < restrict (liftSub τ) (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm) >s
        ≈⟨ restrict-≃ refl≃s (apply-lifted-sub-tm-≃ getFst τ) (apply-lifted-sub-tm-≃ getSnd τ) ⟩
      < restrict (liftSub τ) (liftTerm (getFst [ τ ]tm)) (liftTerm (getSnd [ τ ]tm)) >s
        ≈⟨ restrict-lift τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ⟩
      < liftSub (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)) >s ∎

    lem : unrestrict (sub-from-insertion S₁ P T
            (restrict
              (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm))
            (restrict (liftSub τ) (getFst [ liftSub τ ]tm)
              (getSnd [ liftSub τ ]tm)))
          ≃s
          liftSub (unrestrict (sub-from-insertion S₁ P T
            (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                      (getFst [ τ ]tm)
                      (getSnd [ τ ]tm))
            (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
    lem = begin
      < unrestrict (sub-from-insertion S₁ P T
        (restrict
          (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (getFst [ liftSub τ ]tm) (getSnd [ liftSub τ ]tm))
        (restrict (liftSub τ) (getFst [ liftSub τ ]tm)
          (getSnd [ liftSub τ ]tm))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-≃ S₁ P T l1 l2) ⟩
      < unrestrict (sub-from-insertion S₁ P T
         (liftSub (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                            (getFst [ τ ]tm)
                            (getSnd [ τ ]tm)))
         (liftSub (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s
        ≈˘⟨ unrestrict-≃ (lift-sub-from-insertion S₁ P T _ _) ⟩
      < unrestrict (liftSub (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s
        ≈⟨ unrestrict-lift _ ⟩
      < liftSub (unrestrict (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s ∎

lift-sub-from-insertion (Join S₁ S₂) (PShift P) T σ τ = begin
  < liftSub (sub-from-connect
       (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
       (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)) >s
    ≈⟨ sub-from-connect-lift (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) ⟩
  < sub-from-connect
      (liftSub (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
      (liftSub (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)) >s
    ≈˘⟨ sub-from-connect-≃ (apply-lifted-sub-sub-≃ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) σ) lem ⟩
  < sub-from-connect
      (liftSub σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T
                          (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                          (liftSub τ)) >s ∎
  where
    open Reasoning sub-setoid

    lem : sub-from-insertion S₂ P T
            (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
            (liftSub τ)
          ≃s
          liftSub (sub-from-insertion S₂ P T
                  (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
    lem = begin
      < sub-from-insertion S₂ P T
          (liftSub σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
          (liftSub τ) >s
        ≈⟨ sub-from-insertion-≃ S₂ P T (apply-lifted-sub-sub-≃ (connect-susp-inc-right _ _) σ) refl≃s ⟩
      < sub-from-insertion S₂ P T
          (liftSub (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
          (liftSub τ) >s
        ≈˘⟨ lift-sub-from-insertion S₂ P T _ _ ⟩
      < liftSub (sub-from-insertion S₂ P T
                (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) >s ∎

sub-from-insertion-susp-res : (S : Tree n)
                            → (P : Path S)
                            → .⦃ bp : is-branching-path P ⦄
                            → (T : Tree m)
                            → .⦃ lh : has-linear-height (path-length P) T ⦄
                            → (σ : Sub (suc n) l A)
                            → (τ : Sub (suc m) l A)
                            → sub-from-insertion S P T (suspSubRes σ) (suspSubRes τ) ≃s suspSubRes (sub-from-insertion S P T σ τ)
sub-from-insertion-susp-res (Join S₁ S₂) PHere T σ τ = begin
  < sub-from-connect (suspSubRes τ) (suspSubRes σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ sub-action-≃-sub refl≃s (sub-from-connect-≃ refl≃s (susp-res-comp-sub σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < sub-from-connect (suspSubRes τ) (suspSubRes (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ sub-action-≃-sub refl≃s (sub-from-connect-susp-res τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  < suspSubRes (sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ susp-res-comp-sub _ _ ⟩
  < suspSubRes (sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂)) >s ∎
  where
    open Reasoning sub-setoid

sub-from-insertion-susp-res (Join S₁ S₂) (PExt P) (Join T Sing) σ τ = begin
  < sub-from-connect
      (unrestrict (sub-from-insertion S₁ P T
        (restrict (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ suspSubRes τ ]tm)
                  (getSnd [ suspSubRes τ ]tm))
        (restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm))))
      (suspSubRes σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect
      (suspSubRes (unrestrict (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))))
      (suspSubRes (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s
    ≈˘⟨ sub-from-connect-susp-res _ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ⟩
  < suspSubRes (sub-from-connect
      (unrestrict
        (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (getFst [ τ ]tm) (getSnd [ τ ]tm))
         (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s ∎
  where
    open Reasoning sub-setoid

    l3 : restrict
           (suspSubRes σ ∘
            connect-susp-inc-left (tree-size S₁) (tree-size S₂))
           (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm)
           ≃s
           suspSubRes
           (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
            (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l3 = begin
      < restrict (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                 (getFst [ suspSubRes τ ]tm)
                 (getSnd [ suspSubRes τ ]tm) >s
        ≈˘⟨ restrict-≃ (susp-res-comp-sub σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
                       (susp-res-comp-tm getFst τ)
                       (susp-res-comp-tm getSnd τ) ⟩
      < restrict (suspSubRes (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
                 (suspTm (getFst [ τ ]tm))
                 (suspTm (getSnd [ τ ]tm)) >s
        ≈˘⟨ susp-res-restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                              (getFst [ τ ]tm)
                              (getSnd [ τ ]tm) ⟩
      < suspSubRes (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                             (getFst [ τ ]tm)
                             (getSnd [ τ ]tm)) >s ∎

    l4 : restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm)
                                 (getSnd [ suspSubRes τ ]tm)
         ≃s suspSubRes (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l4 = begin
      < restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm) >s
        ≈˘⟨ restrict-≃ refl≃s (susp-res-comp-tm getFst τ) (susp-res-comp-tm getSnd τ) ⟩
      < restrict (suspSubRes τ) (suspTm (getFst [ τ ]tm)) (suspTm (getSnd [ τ ]tm)) >s
        ≈˘⟨ susp-res-restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ⟩
      < suspSubRes (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)) >s ∎

    l1 : unrestrict (sub-from-insertion S₁ P T
           (restrict (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (getFst [ suspSubRes τ ]tm)
                     (getSnd [ suspSubRes τ ]tm))
           (restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm)))
      ≃s suspSubRes (unrestrict (sub-from-insertion S₁ P T
           (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (getFst [ τ ]tm)
                     (getSnd [ τ ]tm))
           (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
    l1 = begin
      < unrestrict (sub-from-insertion S₁ P T
          (restrict (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ suspSubRes τ ]tm)
                    (getSnd [ suspSubRes τ ]tm))
          (restrict (suspSubRes τ) (getFst [ suspSubRes τ ]tm) (getSnd [ suspSubRes τ ]tm))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-≃ S₁ P T l3 l4) ⟩
      < unrestrict (sub-from-insertion S₁ P T
          (suspSubRes (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                                (getFst [ τ ]tm)
                                (getSnd [ τ ]tm)))
          (suspSubRes (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-susp-res S₁ P T _ _) ⟩
      < unrestrict (suspSubRes (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s
        ≈˘⟨ sub-res-unrestrict-comm _ ⟩
      < suspSubRes (unrestrict (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)))) >s ∎

    l2 : suspSubRes σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)
      ≃s suspSubRes (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    l2 = sym≃s (susp-res-comp-sub σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)))

sub-from-insertion-susp-res (Join S₁ S₂) (PShift P) T σ τ = begin
  < sub-from-connect
      (suspSubRes σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T (suspSubRes σ
                                 ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                                 (suspSubRes τ)) >s
    ≈˘⟨ sub-from-connect-≃ (susp-res-comp-sub σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
                           lem ⟩
  < sub-from-connect
      (suspSubRes (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)))
      (suspSubRes (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)) >s
    ≈˘⟨ sub-from-connect-susp-res (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) _ ⟩
  < suspSubRes (sub-from-connect
      (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)) >s ∎
  where
    open Reasoning sub-setoid

    lem : suspSubRes (sub-from-insertion S₂ P T
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
       ≃s sub-from-insertion S₂ P T (suspSubRes σ
                                    ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                                    (suspSubRes τ)
    lem = begin
      < suspSubRes (sub-from-insertion S₂ P T
                   (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) >s
        ≈˘⟨ sub-from-insertion-susp-res S₂ P T _ _ ⟩
      < sub-from-insertion S₂ P T (suspSubRes (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
                                  (suspSubRes τ) >s
        ≈⟨ sub-from-insertion-≃ S₂ P T (susp-res-comp-sub σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂))) refl≃s ⟩
      < sub-from-insertion S₂ P T (suspSubRes σ
                                  ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                                  (suspSubRes τ) >s ∎

sub-from-insertion-susp : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l ⋆)
                        → (τ : Sub (suc m) l ⋆)
                        → sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) ≃s suspSub (sub-from-insertion S P T σ τ)
sub-from-insertion-susp S P T σ τ = begin
  < sub-from-insertion (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) >s ≡⟨⟩
  < (unrestrict (sub-from-insertion S P T
                (restrict (suspSub σ ∘ idSub)
                          (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm))
                (restrict (suspSub τ) (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm)))) >s
    ≈⟨ unrestrict-≃ (sub-from-insertion-≃ S P T l1 l2) ⟩
  < unrestrict (sub-from-insertion S P T (suspSubRes σ) (suspSubRes τ)) >s
    ≈⟨ unrestrict-≃ (sub-from-insertion-susp-res S P T σ τ) ⟩
  < unrestrict (suspSubRes (sub-from-insertion S P T σ τ)) >s ≡⟨⟩
  < suspSub (sub-from-insertion S P T σ τ) >s ∎
  where
    open Reasoning sub-setoid

    l1 : restrict (suspSub σ ∘ idSub) (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm)
         ≃s suspSubRes σ
    l1 = begin
      < restrict (suspSub σ ∘ idSub) (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm) >s
        ≈⟨ restrict-≃ (id-right-unit (suspSub σ)) (sym≃tm (susp-sub-preserve-getFst τ)) (sym≃tm (susp-sub-preserve-getSnd τ)) ⟩
      < restrict (suspSub σ) getFst getSnd >s
        ≈⟨ restrict-unrestrict (suspSubRes σ) ⟩
      < suspSubRes σ >s ∎

    l2 : restrict (suspSub τ) (getFst [ suspSub τ ]tm)
           (getSnd [ suspSub τ ]tm)
           ≃s suspSubRes τ
    l2 = begin
      < restrict (suspSub τ) (getFst [ suspSub τ ]tm) (getSnd [ suspSub τ ]tm) >s
        ≈˘⟨ restrict-≃ refl≃s (susp-sub-preserve-getFst τ) (susp-sub-preserve-getSnd τ) ⟩
      < restrict (suspSub τ) getFst getSnd >s
        ≈⟨ restrict-unrestrict (suspSubRes τ) ⟩
      < suspSubRes τ >s ∎

sub-from-insertion-sub : (S : Tree n)
                       → (P : Path S)
                       → .⦃ bp : is-branching-path P ⦄
                       → (T : Tree m)
                       → .⦃ lh : has-linear-height (path-length P) T ⦄
                       → (σ : Sub (suc n) l A)
                       → (τ : Sub (suc m) l A)
                       → (μ : Sub l l′ B)
                       → sub-from-insertion S P T (μ ∘ σ) (μ ∘ τ) ≃s μ ∘ sub-from-insertion S P T σ τ
sub-from-insertion-sub (Join S₁ S₂) PHere T σ τ μ = begin
  < sub-from-connect (μ ∘ τ) (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-connect-≃ refl≃s (∘-assoc μ σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < sub-from-connect (μ ∘ τ) (μ ∘ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈˘⟨ sub-action-≃-sub refl≃s (sub-from-connect-sub τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) μ) ⟩
  < μ
    ∘ sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂) >s
    ≈⟨ ∘-assoc μ _ _ ⟩
  < μ
    ∘ (sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂)) >s ∎
  where
    open Reasoning sub-setoid

sub-from-insertion-sub (Join S₁ S₂) (PExt P) (Join T Sing) σ τ μ = begin
  < sub-from-connect
      (unrestrict (sub-from-insertion S₁ P T
        (restrict (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ μ ∘ τ ]tm)
                  (getSnd [ μ ∘ τ ]tm))
        (restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm))))
      (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s
    ≈⟨ sub-from-connect-≃ lem (∘-assoc μ σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  < sub-from-connect
      (μ ∘ unrestrict (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (getFst [ τ ]tm)
                  (getSnd [ τ ]tm))
        (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
      (μ ∘ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) >s
    ≈˘⟨ sub-from-connect-sub _ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) μ ⟩
  < μ ∘ sub-from-connect
       (unrestrict (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                   (getFst [ τ ]tm)
                   (getSnd [ τ ]tm))
         (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s ∎
  where
    open Reasoning sub-setoid

    l1 : restrict
           (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
           (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm)
           ≃s
           (μ ∘
            restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
            (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l1 = begin
      < restrict (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                 (getFst [ μ ∘ τ ]tm)
                 (getSnd [ μ ∘ τ ]tm) >s
        ≈⟨ restrict-≃ (∘-assoc μ σ _) (assoc-tm μ τ getFst) (assoc-tm μ τ getSnd) ⟩
      < restrict (μ ∘ (σ ∘ connect-susp-inc-left _ _))
                 (getFst [ τ ]tm [ μ ]tm)
                 (getSnd [ τ ]tm [ μ ]tm)
        >s
        ≈˘⟨ restrict-comp-sub μ (σ ∘ connect-susp-inc-left _ _) (getFst [ τ ]tm) (getSnd [ τ ]tm) ⟩
      < μ ∘ restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (getFst [ τ ]tm)
                     (getSnd [ τ ]tm) >s ∎

    l2 : restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm)
      ≃s (μ ∘ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))
    l2 = begin
      < restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm) >s
        ≈⟨ restrict-≃ refl≃s (assoc-tm μ τ getFst) (assoc-tm μ τ getSnd) ⟩
      < restrict (μ ∘ τ) (getFst [ τ ]tm [ μ ]tm) (getSnd [ τ ]tm [ μ ]tm) >s
        ≈˘⟨ restrict-comp-sub μ τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ⟩
      < μ ∘ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) >s ∎

    lem : unrestrict (sub-from-insertion S₁ P T
            (restrict (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                      (getFst [ μ ∘ τ ]tm)
                      (getSnd [ μ ∘ τ ]tm))
            (restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm)))
          ≃s
          (μ ∘ unrestrict (sub-from-insertion S₁ P T
              (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                        (getFst [ τ ]tm)
                        (getSnd [ τ ]tm))
              (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
    lem = begin
      < unrestrict (sub-from-insertion S₁ P T
          (restrict (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ μ ∘ τ ]tm)
                    (getSnd [ μ ∘ τ ]tm))
          (restrict (μ ∘ τ) (getFst [ μ ∘ τ ]tm) (getSnd [ μ ∘ τ ]tm))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-≃ S₁ P T l1 l2) ⟩
      < unrestrict (sub-from-insertion S₁ P T
          (μ ∘ restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                        (getFst [ τ ]tm)
                        (getSnd [ τ ]tm))
          (μ ∘ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))) >s
        ≈⟨ unrestrict-≃ (sub-from-insertion-sub S₁ P T _ _ μ) ⟩
      < unrestrict (μ ∘ sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))) >s
        ≈⟨ unrestrict-comp-higher μ _ ⟩
      < μ ∘ unrestrict (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (getFst [ τ ]tm)
                    (getSnd [ τ ]tm))
          (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))) >s ∎

sub-from-insertion-sub (Join S₁ S₂) (PShift P) T σ τ μ = begin
  < sub-from-connect
      (μ ∘ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T
        (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
        (μ ∘ τ)) >s
    ≈⟨ sub-from-connect-≃ (∘-assoc μ σ (connect-susp-inc-left _ _)) lem ⟩
  < sub-from-connect
      (μ ∘ (σ ∘ connect-susp-inc-left _ _))
      (μ ∘ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) >s
    ≈˘⟨ sub-from-connect-sub (σ ∘ connect-susp-inc-left _ _) (sub-from-insertion S₂ P T _ τ) μ ⟩
  < μ ∘ sub-from-connect
      (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) >s ∎
  where
    open Reasoning sub-setoid

    lem : sub-from-insertion S₂ P T
            (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
            (μ ∘ τ)
       ≃s μ ∘ sub-from-insertion S₂ P T
            (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ
    lem = begin
      < sub-from-insertion S₂ P T
          (μ ∘ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
          (μ ∘ τ) >s
        ≈⟨ sub-from-insertion-≃ S₂ P T (∘-assoc μ σ (connect-susp-inc-right _ _)) refl≃s ⟩
      < sub-from-insertion S₂ P T
          (μ ∘ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))
          (μ ∘ τ) >s
        ≈⟨ sub-from-insertion-sub S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ μ ⟩
      < μ ∘ sub-from-insertion S₂ P T
          (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ >s ∎

sub-from-insertion-label-helper-≃ : (S : Tree n)
                                  → (P : Path S)
                                  → .⦃ bp : is-branching-path P ⦄
                                  → (T : Tree m)
                                  → .⦃ lh : has-linear-height (path-length P) T ⦄
                                  → ∀ {σ : Label l S} {σ′ : Label l′ S}
                                  → σ ≃l σ′
                                  → ∀ {τ} {τ′}
                                  → τ ≃l τ′
                                  → sub-from-insertion-label-helper S P T σ τ ≃l sub-from-insertion-label-helper S P T σ′ τ′
sub-from-insertion-label-helper-≃ (Join S₁ S₂) PHere T (LJoin≃ x p p′) q = connect-label-≃ q p′
sub-from-insertion-label-helper-≃ (Join S₁ S₂) (PExt P) (Join T Sing) (LJoin≃ x p p′) (LJoin≃ y q (LSing≃ z)) = LJoin≃ y (sub-from-insertion-label-helper-≃ S₁ P T p q) p′
sub-from-insertion-label-helper-≃ (Join S₁ S₂) (PShift P) T (LJoin≃ x p p′) q = LJoin≃ x p (sub-from-insertion-label-helper-≃ S₂ P T p′ q)

lift-sub-from-insertion-label-helper : (S : Tree n)
                                     → (P : Path S)
                                     → .⦃ bp : is-branching-path P ⦄
                                     → (T : Tree m)
                                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                                     → (σ : Label l S)
                                     → (τ : Label l T)
                                     → liftLabel (sub-from-insertion-label-helper S P T σ τ) ≃l sub-from-insertion-label-helper S P T (liftLabel σ) (liftLabel τ)
lift-sub-from-insertion-label-helper (Join S₁ S₂) PHere T (LJoin x σ σ′) τ = lift-connect-label τ σ′
lift-sub-from-insertion-label-helper (Join S₁ S₂) (PExt P) (Join T Sing) (LJoin x σ σ′) (LJoin y τ (LSing z)) = LJoin≃ refl≃tm (lift-sub-from-insertion-label-helper S₁ P T σ τ) refl≃l
lift-sub-from-insertion-label-helper (Join S₁ S₂) (PShift P) T (LJoin x σ σ′) τ = LJoin≃ refl≃tm refl≃l (lift-sub-from-insertion-label-helper S₂ P T σ′ τ)

lift-sub-from-insertion-label : (S : Tree n)
                              → (P : Path S)
                              → .⦃ bp : is-branching-path P ⦄
                              → (T : Tree m)
                              → .⦃ lh : has-linear-height (path-length P) T ⦄
                              → (σ : Sub (suc n) l A)
                              → (τ : Sub (suc m) l A)
                              → liftSub (sub-from-insertion-label S P T σ τ) ≃s sub-from-insertion-label S P T (liftSub σ) (liftSub τ)
lift-sub-from-insertion-label {A = A} S P T σ τ = begin
  < liftSub (sub-from-insertion-label S P T σ τ) >s
    ≈˘⟨ lift-label-to-sub (sub-from-insertion-label-helper S P T (to-label S σ) (to-label T τ)) A ⟩
  < label-to-sub (liftLabel (sub-from-insertion-label-helper S P T (to-label S σ) (to-label T τ))) (liftType A) >s
    ≈⟨ label-to-sub-≃ (lift-sub-from-insertion-label-helper S P T (to-label S σ) (to-label T τ)) refl≃ty ⟩
  < label-to-sub (sub-from-insertion-label-helper S P T (liftLabel (to-label S σ)) (liftLabel (to-label T τ))) (liftType A) >s
    ≈⟨ label-to-sub-≃ (sub-from-insertion-label-helper-≃ S P T (lift-to-label S σ) (lift-to-label T τ)) refl≃ty ⟩
  < sub-from-insertion-label S P T (liftSub σ) (liftSub τ) >s ∎
  where
    open Reasoning sub-setoid

susp-sub-from-insertion-label-helper : (S : Tree n)
                                     → (P : Path S)
                                     → .⦃ bp : is-branching-path P ⦄
                                     → (T : Tree m)
                                     → .⦃ lh : has-linear-height (path-length P) T ⦄
                                     → (σ : Label l S)
                                     → (τ : Label l T)
                                     → suspLabel (sub-from-insertion-label-helper S P T σ τ) ≃l sub-from-insertion-label-helper S P T (suspLabel σ) (suspLabel τ)
susp-sub-from-insertion-label-helper (Join S₁ S₂) PHere T (LJoin x σ σ′) τ = susp-connect-label τ σ′
susp-sub-from-insertion-label-helper (Join S₁ S₂) (PExt P) (Join T Sing) (LJoin x σ σ′) (LJoin y τ (LSing z)) = LJoin≃ refl≃tm (susp-sub-from-insertion-label-helper S₁ P T σ τ) refl≃l
susp-sub-from-insertion-label-helper (Join S₁ S₂) (PShift P) T (LJoin x σ σ′) τ = LJoin≃ refl≃tm refl≃l (susp-sub-from-insertion-label-helper S₂ P T σ′ τ)

susp-sub-from-insertion-label : (S : Tree n)
                              → (P : Path S)
                              → .⦃ bp : is-branching-path P ⦄
                              → (T : Tree m)
                              → .⦃ lh : has-linear-height (path-length P) T ⦄
                              → (σ : Sub (suc n) l ⋆)
                              → (τ : Sub (suc m) l ⋆)
                              → sub-from-insertion-label (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) ≃s suspSub (sub-from-insertion-label S P T σ τ)
susp-sub-from-insertion-label S P T σ τ = begin
  < sub-from-insertion-label (suspTree S) (PExt P) (suspTree T) (suspSub σ) (suspSub τ) >s ≡⟨⟩
  < label-to-sub (sub-from-insertion-label-helper (suspTree S) (PExt P) (suspTree T) (to-label (suspTree S) (suspSub σ)) (to-label (suspTree T) (suspSub τ))) ⋆ >s
    ≈⟨ label-to-sub-≃ (sub-from-insertion-label-helper-≃ (suspTree S) (PExt P) (suspTree T) (susp-to-label S σ) (susp-to-label T τ)) refl≃ty ⟩
  < label-to-sub (sub-from-insertion-label-helper (suspTree S) (PExt P) (suspTree T)
                 (LJoin getFst (suspLabel (to-label S σ)) (LSing getSnd))
                 (LJoin getFst (suspLabel (to-label T τ)) (LSing getSnd)))
                 ⋆ >s
    ≡⟨⟩
  < unrestrict (label-to-sub (sub-from-insertion-label-helper S P T (suspLabel (to-label S σ))
                                                                    (suspLabel (to-label T τ)))
                             (getFst ─⟨ ⋆ ⟩⟶ getSnd)) >s
    ≈˘⟨ unrestrict-≃ (label-to-sub-≃ (susp-sub-from-insertion-label-helper S P T (to-label S σ) (to-label T τ)) refl≃ty) ⟩
  < unrestrict (label-to-sub (suspLabel (sub-from-insertion-label-helper S P T (to-label S σ) (to-label T τ))) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) >s
    ≈⟨ unrestrict-≃ (label-to-sub-susp (sub-from-insertion-label-helper S P T (to-label S σ) (to-label T τ)) ⋆) ⟩
  < suspSub (sub-from-insertion-label S P T σ τ) >s ∎
  where
    open Reasoning sub-setoid

sub-from-insertion-label-helper-sub : (S : Tree n)
                                    → (P : Path S)
                                    → .⦃ bp : is-branching-path P ⦄
                                    → (T : Tree m)
                                    → .⦃ lh : has-linear-height (path-length P) T ⦄
                                    → (σ : Label l S)
                                    → (τ : Label l T)
                                    → (μ : Sub l l′ A)
                                    → sub-from-insertion-label-helper S P T (σ [ μ ]l) (τ [ μ ]l) ≃l sub-from-insertion-label-helper S P T σ τ [ μ ]l
sub-from-insertion-label-helper-sub (Join S₁ S₂) PHere T (LJoin x σ σ′) τ μ = connect-label-comp τ σ′ μ
sub-from-insertion-label-helper-sub (Join S₁ S₂) (PExt P) (Join T Sing) (LJoin x σ σ′) (LJoin y τ (LSing z)) μ = LJoin≃ refl≃tm (sub-from-insertion-label-helper-sub S₁ P T σ τ μ) refl≃l
sub-from-insertion-label-helper-sub (Join S₁ S₂) (PShift P) T (LJoin x σ σ′) τ μ = LJoin≃ refl≃tm refl≃l (sub-from-insertion-label-helper-sub S₂ P T σ′ τ μ)

sub-from-insertion-label-sub : (S : Tree n)
                             → (P : Path S)
                             → .⦃ bp : is-branching-path P ⦄
                             → (T : Tree m)
                             → .⦃ lh : has-linear-height (path-length P) T ⦄
                             → (σ : Sub (suc n) l A)
                             → (τ : Sub (suc m) l A)
                             → (μ : Sub l l′ B)
                             → sub-from-insertion-label S P T (μ ∘ σ) (μ ∘ τ) ≃s μ ∘ sub-from-insertion-label S P T σ τ
sub-from-insertion-label-sub {A = A} S P T σ τ μ = begin
  < label-to-sub (sub-from-insertion-label-helper S P T (to-label S (μ ∘ σ)) (to-label T (μ ∘ τ))) (A [ μ ]ty) >s
    ≈⟨ label-to-sub-≃ (sub-from-insertion-label-helper-≃ S P T (to-label-comp S σ μ) (to-label-comp T τ μ)) refl≃ty ⟩
  < label-to-sub (sub-from-insertion-label-helper S P T (to-label S σ [ μ ]l) (to-label T τ [ μ ]l)) (A [ μ ]ty) >s
    ≈⟨ label-to-sub-≃ (sub-from-insertion-label-helper-sub S P T (to-label S σ) (to-label T τ) μ) refl≃ty ⟩
  < label-to-sub (sub-from-insertion-label-helper S P T (to-label S σ) (to-label T τ) [ μ ]l) (A [ μ ]ty) >s
    ≈⟨ label-comp-to-sub-comp (sub-from-insertion-label-helper S P T (to-label S σ) (to-label T τ)) μ A ⟩
  < μ ∘ sub-from-insertion-label S P T σ τ >s ∎
  where
    open Reasoning sub-setoid

exterior-sub-first-label : (S : Tree n)
                         → (P : Path S)
                         → .⦃ _ : is-branching-path P ⦄
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height (path-length P) T ⦄
                         → first-label (exterior-sub-label S P T) ≃tm (Var (fromℕ (insertion-tree-size S P T)))
exterior-sub-first-label (Join S₁ S₂) PHere T = begin
  < first-label (exterior-sub-label (Join S₁ S₂) PHere T) >tm
    ≈⟨ label-between-connect-trees-first-label (to-label (suspTree S₁) (sub-from-linear-tree-unbiased (suspTree S₁) T 0)) (id-label S₂) T S₂ ⟩
  < first-label (to-label (suspTree S₁) (sub-from-linear-tree-unbiased (suspTree S₁) T 0)) [ label-to-sub (connect-tree-inc-left T S₂) ⋆ ]tm >tm
    ≈⟨ sub-action-≃-tm (‼l-prop-2 {S = suspTree S₁} (sub-from-linear-tree-unbiased (suspTree S₁) T 0) PHere) refl≃s ⟩
  < Var (fromℕ _)
    [ sub-from-linear-tree-unbiased (suspTree S₁) T 0 ]tm
    [ label-to-sub (connect-tree-inc-left T S₂) ⋆ ]tm >tm
    ≈⟨ sub-action-≃-tm (unrestrict-fst (sub-from-linear-tree-unbiased S₁ T 1)) refl≃s ⟩
  < Var (fromℕ _) [ label-to-sub (connect-tree-inc-left T S₂) ⋆ ]tm >tm
    ≈˘⟨ ‼l-prop (connect-tree-inc-left T S₂) PHere ⋆ ⟩
  < first-label (connect-tree-inc-left T S₂) >tm
    ≈⟨ connect-tree-inc-left-first-label T S₂ ⟩
  < Var (fromℕ (connect-tree-length T S₂)) >tm ∎
  where
    open Reasoning tm-setoid
exterior-sub-first-label (Join S₁ S₂) (PExt P) (Join T Sing)
  = label-between-joins-first-label (exterior-sub-label S₁ P T) (id-label S₂) (insertion-tree S₁ P T) S₂
exterior-sub-first-label (Join S₁ S₂) (PShift P) T
  = label-between-joins-first-label (id-label S₁) (exterior-sub-label S₂ P T) S₁ (insertion-tree S₂ P T)
-}
