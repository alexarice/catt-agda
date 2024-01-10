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
open import Catt.Tree.Canonical
open import Catt.Tree.Canonical.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Insertion

open import Relation.Binary

instance
  ⌊⌋p-not-here : {P : Branch S l} → not-here ⌊ P ⌋p
  ⌊⌋p-not-here {P = BHere} = tt
  ⌊⌋p-not-here {P = BExt P} = tt
  ⌊⌋p-not-here {P = BShift P} = tt

  ⌊⌋p-maximal : {P : Branch S l} → is-maximal ⌊ P ⌋p
  ⌊⌋p-maximal {P = BHere} = inst
  ⌊⌋p-maximal {P = BExt P} = inst
  ⌊⌋p-maximal {P = BShift P} = build

ih-non-zero : (S : Tree n) → (p : Branch S d) → NonZero (ih p)
ih-non-zero (Join S T) BHere = it
ih-non-zero (Join S T) (BExt P) = it
ih-non-zero (Join S T) (BShift P) = ih-non-zero T P

ih-linear : (S : Tree n) → .⦃ is-linear S ⦄ → (P : Branch S l) → ih P ≡ tree-dim S
ih-linear (Susp S) BHere = refl
ih-linear (Susp S) (BExt P) = cong suc (ih-linear S P)

κ-phere : (S : Tree n)
                     → (p : Branch S d)
                     → (T : Tree m)
                     → .⦃ _ : has-trunk-height d T ⦄
                     → κ S p T PHere ≃stm SHere {S = insertion-tree S p T}
κ-phere (Join S₁ S₂) BHere T = SPath≃ (++t-inc-left-phere T S₂)
κ-phere (Join S₁ S₂) (BExt p) (Susp T) = refl≃stm
κ-phere (Join S₁ S₂) (BShift p) T = refl≃stm

label-from-replace-lem : (S : Tree n)
                       → (P : Branch S l)
                       → (T : Tree m)
                       → .⦃ _ : has-trunk-height l T ⦄
                       → (L : Label X S)
                       → (a : STm X)
                       → (M : Label X T)
                     → label-from-insertion S P T (replace-label L a) M ≃lm label-from-insertion S P T L M
label-from-replace-lem (Join S₁ S₂) BHere T L a M = refl≃lm
label-from-replace-lem (Join S₁ S₂) (BExt P) (Susp T) L a M .get (PExt Z) = refl≃stm
label-from-replace-lem (Join S₁ S₂) (BExt P) (Susp T) L a M .get (PShift Z) = refl≃stm
label-from-replace-lem (Join S₁ S₂) (BShift P) T L a M .get (PExt Z) = refl≃stm
label-from-replace-lem (Join S₁ S₂) (BShift P) T L a M .get (PShift Z) = refl≃stm

module _ where
  open Reasoning stm-setoid

  κ-last-path : (S : Tree n)
                           → (p : Branch S d)
                           → (T : Tree m)
                           → .⦃ _ : has-trunk-height d T ⦄
                           → κ S p T (last-path S) ≃stm SPath (last-path (insertion-tree S p T))
  κ-last-path (Join S₁ S₂) (BExt p) (Susp T) = compute-≃ refl≃stm
  κ-last-path (Join S₁ S₂) (BShift p) T = compute-≃ (SShift≃ refl≃ (κ-last-path S₂ p T))
  κ-last-path (Join S₁ Sing) BHere T = SPath≃ (++t-inc-right-last-path T Sing)
  κ-last-path (Join S₁ S₂@(Join S₃ S₄)) BHere T = SPath≃ (++t-inc-right-last-path T S₂)

  ι-comm : (S : Tree n)
                      → (p : Branch S d)
                      → (T : Tree m)
                      → .⦃ _ : has-trunk-height d T ⦄
                      → (L : Label X S)
                      → (M : Label X T)
                      → (As : STy X)
                      → ι S p T ●l (label-from-insertion S p T L M ,, As) ≃lm M
  ι-comm (Join S₁ S₂) BHere T L M A .get Z = ++l-inc-left M (L ∘ PShift) A .get Z
  ι-comm (Join S₁ S₂) (BExt p) (Susp T) L M A .get (PExt Z)
    = ι-comm S₁ p T (L ∘ PExt) (M ∘ PExt) _ .get Z
  ι-comm (Join S₁ S₂) (BExt p) (Susp T) L M A .get (PShift PHere) = ⊥-elim it
  ι-comm (Join S₁ S₂) (BShift p) T L M = ι-comm S₂ p T (L ∘ PShift) M

  κ-comm : (S : Tree n)
                      → (p : Branch S d)
                      → (T : Tree m)
                      → .⦃ _ : has-trunk-height d T ⦄
                      → (L : Label X S)
                      → (M : Label X T)
                      → (Bs : STy X)
                      → L ⌊ p ⌋p ≃stm canonical-comp′ (ih p) T >>= (M ,, Bs)
                      → κ S p T ●l (label-from-insertion S p T L M ,, Bs) ≃lm L
  κ-comm (Join S₁ S₂) BHere T L M Bs q .get (PExt Z) = begin
    < canonical-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂
      >>= (M ++l (L ∘ PShift) ,, Bs) >stm
      ≈⟨ >>=-assoc (canonical-label (Susp S₁) T (PExt Z))
                   (++t-inc-left T S₂)
                   ((M ++l L ∘ PShift ,, Bs)) ⟩
    < canonical-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂ ●lt (M ++l L ∘ PShift ,, Bs) >stm
      ≈⟨ >>=-≃ (canonical-label-max (Susp S₁) T (PExt Z))
               (++l-inc-left M (L ∘ PShift) Bs) refl≃sty ⟩
    < canonical-comp′ (suc (tree-dim S₁)) T >>= (M ,, Bs) >stm
      ≈˘⟨ q ⟩
    < L (PExt (is-linear-max-path S₁)) >stm
      ≈⟨ ap-≃ (refl≃l {L = L ∘ PExt}) (max-path-lin-tree S₁ Z refl≃) ⟩
    < L (PExt Z) >stm ∎
  κ-comm (Join S₁ S₂) BHere T L M Bs q .get (PShift Z) = ++l-inc-right M (L ∘ PShift) Bs Z
  κ-comm (Join S₁ S₂) (BExt {n = n} p) (Susp T) L M Bs q .get (PExt Z) = κ-comm S₁ p T (L ∘ PExt) (M ∘ PExt) _ q .get Z
  κ-comm (Join S₁ S₂) (BExt p) (Susp T) L M Bs q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
  κ-comm (Join S₁ S₂) (BShift p) T L M Bs q .get (PExt Z) = refl≃stm
  κ-comm (Join S₁ S₂) (BShift p) T L M Bs q .get (PShift Z) = κ-comm S₂ p T (L ∘ PShift) M Bs q .get Z

disc-insertion : (S : Tree n)
               → .⦃ is-linear S ⦄
               → (P : Branch S l)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height l T ⦄
               → insertion-tree S P T ≃′ T
disc-insertion (Susp S) BHere T = ++t-right-unit T
disc-insertion (Susp S) (BExt P) (Susp T) = Join≃′ (disc-insertion S P T) Refl≃′

disc-ι : (S : Tree n)
              → .⦃ is-linear S ⦄
              → (P : Branch S l)
              → (T : Tree m)
              → .⦃ _ : has-trunk-height l T ⦄
              → ι S P T ≃l id-label T
disc-ι (Susp S) BHere T .get Z = SPath≃ (++t-inc-left-unit T .get Z)
disc-ι (Susp S) (BExt P) (Susp T) .get PHere = SPath≃ (Here≃ (≃′-to-≃ (Join≃′ (disc-insertion S P T) Refl≃′)))
disc-ι (Susp S) (BExt P) (Susp T) .get (PExt Z) = compute-≃ (SExt≃ (disc-ι S P T .get Z) refl≃)
disc-ι (Susp S) (BExt P) (Susp T) .get (PShift PHere) = compute-≃ (SShift≃ (≃′-to-≃ (disc-insertion S P T)) refl≃stm)

disc-label-from : (S : Tree n)
                → .⦃ _ : is-linear S ⦄
                → (P : Branch S l)
                → (T : Tree m)
                → .⦃ _ : has-trunk-height l T ⦄
                → (L : Label X S)
                → (M : Label X T)
                → label-from-insertion S P T L M ≃l label-≃ (disc-insertion S P T) M
disc-label-from (Susp S) BHere T L M = ++l-right-unit M (L ∘ PShift)
disc-label-from (Susp S) (BExt P) (Susp T) L M .get PHere = refl≃stm
disc-label-from (Susp S) (BExt P) (Susp T) L M .get (PExt Z) = disc-label-from S P T (L ∘ PExt) (M ∘ PExt) .get Z
disc-label-from (Susp S) (BExt P) (Susp T) L M .get (PShift PHere) = refl≃stm

insertion-disc : (S : Tree n)
               → (p : Branch S l)
               → insertion-tree S p (n-disc (ih p))
                                ⦃ has-trunk-height-n-disc (<⇒≤ (bh-<-ih p)) ⦄ ≃′ S
insertion-disc (Join S₁ S₂) BHere = Join≃′ (linear-tree-unique (n-disc (tree-dim S₁)) S₁ (≃n-to-≡ it)) refl≃′
insertion-disc (Join S₁ S₂) (BExt p) = Join≃′ (insertion-disc S₁ p) refl≃′
insertion-disc (Join S₁ S₂) (BShift p) = Join≃′ refl≃′ (insertion-disc S₂ p)

disc-label-from-2 : (S : Tree n)
                → (p : Branch S l)
                → (L : Label X S)
                → (M : Label X (n-disc (ih p)))
                → L ⌊ p ⌋p
                  ≃stm
                  M (is-linear-max-path (n-disc (ih p)))
                → label-from-insertion S
                                       p
                                       (n-disc (ih p))
                                       ⦃ has-trunk-height-n-disc (<⇒≤ (bh-<-ih p)) ⦄
                                       L
                                       M
                  ≃lm
                  label-≃ (insertion-disc S p) L
disc-label-from-2 (Join S T) BHere L M q .get (PExt Z) = begin
  < M (PExt Z) >stm
    ≈˘⟨ ap-≃ (refl≃l {L = M}) (max-path-lin-tree (n-disc (suc (tree-dim S))) (PExt Z) refl≃) ⟩
  < M (is-linear-max-path (n-disc (suc (tree-dim S)))) >stm
    ≈˘⟨ q ⟩
  < L (PExt (is-linear-max-path S)) >stm
    ≈⟨ ap-≃ (refl≃l {L = L})
            (Ext≃ (trans≃p (max-path-lin-tree S Z (≃′-to-≃ (linear-tree-unique S (n-disc (tree-dim S))
                                                                                 (sym (≃n-to-≡ it)))))
                           (ppath-≃-≃p (linear-tree-unique (n-disc (tree-dim S)) S _) Z)) refl≃) ⟩
  < L (PExt (ppath-≃ (linear-tree-unique (n-disc (tree-dim S)) S _) Z)) >stm ∎
  where
    open Reasoning stm-setoid
disc-label-from-2 (Join S T) BHere L M q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
disc-label-from-2 (Join S T) (BExt p) L M q .get (PExt Z) = disc-label-from-2 S p (L ∘ PExt) (M ∘ PExt) q .get Z
disc-label-from-2 (Join S T) (BExt p) L M q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
disc-label-from-2 (Join S T) (BShift p) L M q .get (PExt Z) = refl≃stm
disc-label-from-2 (Join S T) (BShift p) L M q .get (PShift Z) = disc-label-from-2 T p (L ∘ PShift) M q .get Z

label-from-insertion-map : (f : STm X → STm Y)
                         → (S : Tree n)
                         → (p : Branch S l)
                         → (T : Tree m)
                         → .⦃ _ : has-trunk-height l T ⦄
                         → (L : Label X S)
                         → (M : Label X T)
                         → (f ∘ label-from-insertion S p T L M) ≃l label-from-insertion S p T (f ∘ L) (f ∘ M)
label-from-insertion-map f (Join S₁ S₂) BHere T L M = ++l-map f M (L ∘ PShift)
label-from-insertion-map f (Join S₁ S₂) (BExt p) (Susp T) L M .get PHere = refl≃stm
label-from-insertion-map f (Join S₁ S₂) (BExt p) (Susp T) L M .get (PExt Z) = label-from-insertion-map f S₁ p T (L ∘ PExt) (M ∘ PExt) .get Z
label-from-insertion-map f (Join S₁ S₂) (BExt p) (Susp T) L M .get (PShift Z) = replace-label-map f (L ∘ PShift) (M (PShift PHere)) .get Z
label-from-insertion-map f (Join S₁ S₂) (BShift p) T L M .get PHere = refl≃stm
label-from-insertion-map f (Join S₁ S₂) (BShift p) T L M .get (PExt Z) = refl≃stm
label-from-insertion-map f (Join S₁ S₂) (BShift p) T L M .get (PShift Z) = label-from-insertion-map f S₂ p T (L ∘ PShift) M .get Z

κ-ι-prop : (S : Tree n)
                       → (p : Branch S l)
                       → (T : Tree m)
                       → .⦃ _ : has-trunk-height (bh p) T ⦄
                       → label-from-insertion S p T (κ S p T) (ι S p T) ≃l id-label (insertion-tree S p T)
κ-ι-prop (Join S₁ S₂) BHere T = ++l-prop T S₂
κ-ι-prop (Join S₁ S₂) (BExt p) (Susp T) .get PHere = refl≃stm
κ-ι-prop (Join S₁ S₂) (BExt p) (Susp T) .get (PExt Z) = begin
  < label-from-insertion S₁ p T
      (SExt ∘ κ S₁ p T)
      (SExt ∘ ι S₁ p T) Z >stm
    ≈˘⟨ label-from-insertion-map SExt S₁ p T (κ S₁ p T) (ι S₁ p T) .get Z ⟩
  < (SExt ∘ label-from-insertion S₁ p T (κ S₁ p T) (ι S₁ p T)) Z >stm
    ≈⟨ compute-≃ (SExt≃ (κ-ι-prop S₁ p T .get Z) refl≃) ⟩
  < SPath (PExt Z) >stm ∎
  where
    open Reasoning stm-setoid
κ-ι-prop (Join S₁ S₂) (BExt p) (Susp T) .get (PShift Z) = compute-≃ (compute-stm-≃ (replace-label-prop (SShift ∘ id-label S₂) (SShift SHere) refl≃stm .get Z))
κ-ι-prop (Join S₁ S₂) (BShift p) T .get PHere = refl≃stm
κ-ι-prop (Join S₁ S₂) (BShift p) T .get (PExt Z) = compute-≃ refl≃stm
κ-ι-prop (Join S₁ S₂) (BShift p) T .get (PShift Z) = begin
  < label-from-insertion S₂ p T
      (SShift ∘ κ S₂ p T)
      (SShift ∘ ι S₂ p T) Z >stm
    ≈˘⟨ label-from-insertion-map SShift S₂ p T (κ S₂ p T) (ι S₂ p T) .get Z ⟩
  < (SShift ∘ label-from-insertion S₂ p T (κ S₂ p T) (ι S₂ p T)) Z >stm
    ≈⟨ compute-≃ (SShift≃ refl≃ (κ-ι-prop S₂ p T .get Z )) ⟩
  < SPath (PShift Z) >stm ∎
  where
    open Reasoning stm-setoid

κ-branch-path : (S : Tree n)
                 → (p : Branch S l)
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height l T ⦄
                 → κ S p T ⌊ p ⌋p
                   ≃stm
                   canonical-comp′ (ih p) T >>= (ι S p T ,, S⋆)
κ-branch-path (Join S₁ S₂) BHere T
  = >>=-≃ (canonical-label-max (Susp S₁) T (is-linear-max-path (Susp S₁)) ⦃ inst ⦄)
          refl≃l
          refl≃sty
κ-branch-path (Join S₁ S₂) (BExt {n = n} p) (Susp T) = begin
  < SExt (κ S₁ p T ⌊ p ⌋p) >stm
    ≈⟨ SExt≃ (κ-branch-path S₁ p T) refl≃ ⟩
  < SExt (canonical-comp′ (ih p) T >>= (ι S₁ p T ,, S⋆)) >stm
   ≈˘⟨ >>=-ext (canonical-comp′ (ih p) T) (ι S₁ p T ,, S⋆) ⟩
  < canonical-comp′ (ih p) T >>= map-ext (ι S₁ p T ,, S⋆) >stm ∎
  where
    open Reasoning stm-setoid
κ-branch-path (Join S₁ S₂) (BShift {n = n} p) T = begin
  < SShift (κ S₂ p T ⌊ p ⌋p) >stm
    ≈⟨ SShift≃ refl≃ (κ-branch-path S₂ p T) ⟩
  < SShift (canonical-comp′ (ih p) T >>= (ι S₂ p T ,, S⋆)) >stm
    ≈˘⟨ >>=-shift (canonical-comp′ (ih p) T) (ι S₂ p T ,, S⋆) ⟩
  < canonical-comp′ (ih p) T >>= map-shift (ι S₂ p T ,, S⋆) >stm ∎
  where
    open Reasoning stm-setoid

insertion-parallel : (S : Tree n)
                   → (P : Branch S l)
                   → (Q : Branch S l′)
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height l T ⦄
                   → .⦃ _ : has-trunk-height l′ T ⦄
                   → ⌊ P ⌋p ≃p ⌊ Q ⌋p
                   → insertion-tree S P T ≃′ insertion-tree S Q T
insertion-parallel (Join S₁ S₂) BHere BHere T p = Refl≃′
insertion-parallel (Join S₁ S₂) BHere (BExt Q) (Susp T) p = Join≃′ (sym≃′ (disc-insertion S₁ Q T)) Refl≃′
insertion-parallel (Join S₁ S₂) (BExt P) BHere (Susp T) p = Join≃′ (disc-insertion S₁ P T) Refl≃′
insertion-parallel (Join S₁ S₂) (BExt P) (BExt Q) (Susp T) p = Join≃′ (insertion-parallel S₁ P Q T (proj-ext p)) Refl≃′
insertion-parallel (Join S₁ S₂) (BShift P) (BShift Q) T p = Join≃′ Refl≃′ (insertion-parallel S₂ P Q T (proj-shift p))

module _ where
  open Reasoning stm-setoid
  κ-parallel : (S : Tree n)
                    → (P : Branch S l)
                    → (Q : Branch S l′)
                    → (T : Tree m)
                    → .⦃ _ : has-trunk-height l T ⦄
                    → .⦃ _ : has-trunk-height l′ T ⦄
                    → ⌊ P ⌋p ≃p ⌊ Q ⌋p
                    → κ S P T ≃lm κ S Q T
  κ-parallel (Join S₁ S₂) BHere BHere T p = refl≃lm
  κ-parallel (Join S₁ S₂) BHere (BExt {n = n} Q) (Susp T) p .get (PExt Z) = begin
    < canonical-label (Susp S₁) (Susp T) (PExt Z) >>= ++t-inc-left (Susp T) S₂ >stm
      ≈⟨ >>=-≃ (canonical-label-max (Susp S₁) (Susp T) (PExt Z)) refl≃l refl≃sty ⟩
    < canonical-comp′ (tree-dim S₁) T >>= label₁ (++t-inc-left (Susp T) S₂) >stm
      ≈˘⟨ >>=-≃ (canonical-comp′-≃ (ih-linear _ Q) (refl≃ {T = T}))
                [ (λ P → compute-≃ refl≃stm) ]
                (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
    < canonical-comp′ (ih Q) T >>= map-ext (id-label-wt T) >stm
      ≈⟨ >>=-ext (canonical-comp′ (ih Q) T) (id-label-wt T) ⟩
    < SExt (canonical-comp′ (ih Q) T >>= id-label-wt T) >stm
      ≈˘⟨ SExt≃ (>>=-≃ (refl≃stm {a = canonical-comp′ (ih Q) T})
                       (disc-ι S₁ Q T)
                       (S⋆-≃ (≃′-to-≃ (disc-insertion S₁ Q T)))) refl≃ ⟩
    < SExt (canonical-comp′ (ih Q) T >>= (ι S₁ Q T ,, S⋆)) >stm
      ≈˘⟨ SExt≃ (κ-branch-path S₁ Q T) refl≃ ⟩
    < SExt (κ S₁ Q T ⌊ Q ⌋p) >stm
      ≈⟨ SExt≃ (ap-≃ (refl≃l {L = κ S₁ Q T})
                     (max-path-unique S₁ ⌊ Q ⌋p Z)) refl≃ ⟩
    < SExt (κ S₁ Q T Z) >stm ∎
  κ-parallel (Join S₁ S₂) BHere (BExt Q) (Susp T) p .get (PShift Z) = compute-≃ (SShift≃ (sym≃ (≃′-to-≃ (disc-insertion S₁ Q T))) refl≃stm)
  κ-parallel (Join S₁ S₂) (BExt P) BHere (Susp T) p .get (PExt Z)
    = sym≃stm (κ-parallel (Join S₁ S₂) BHere (BExt P) (Susp T) (sym≃p p) .get (PExt Z))
  κ-parallel (Join S₁ S₂) (BExt P) BHere (Susp T) p .get (PShift Z)
    = sym≃stm (κ-parallel (Join S₁ S₂) BHere (BExt P) (Susp T) (sym≃p p) .get (PShift Z))
  κ-parallel (Join S₁ S₂) (BExt P) (BExt Q) (Susp T) p .get (PExt Z)
    = SExt≃ (κ-parallel S₁ P Q T (proj-ext p) .get Z) refl≃
  κ-parallel (Join S₁ S₂) (BExt P) (BExt Q) (Susp T) p .get (PShift Z)
    = SShift≃ (≃′-to-≃ (insertion-parallel S₁ P Q T (proj-ext p))) refl≃stm
  κ-parallel (Join S₁ S₂) (BShift P) (BShift Q) T p .get (PExt Z)
    = SExt≃ refl≃stm (≃′-to-≃ (insertion-parallel S₂ P Q T (proj-shift p)))
  κ-parallel (Join S₁ S₂) (BShift P) (BShift Q) T p .get (PShift Z)
    = SShift≃ refl≃ (κ-parallel S₂ P Q T (proj-shift p) .get Z)

parallel-label-from : (S : Tree n)
                  → (P : Branch S l)
                  → (Q : Branch S l′)
                  → (T : Tree m)
                  → .⦃ _ : has-trunk-height (bh P) T ⦄
                  → .⦃ _ : has-trunk-height (bh Q) T ⦄
                  → (p : ⌊ P ⌋p ≃p ⌊ Q ⌋p)
                  → (L : Label X S)
                  → (M : Label X T)
                  → label-from-insertion S P T L M ≃lm label-≃ (insertion-parallel S P Q T p) (label-from-insertion S Q T L M)
parallel-label-from (Join S₁ S₂) BHere BHere T p L M = refl≃lm
parallel-label-from (Join S₁ S₂) BHere (BExt Q) (Susp T) p L M .get (PExt Z) = sym≃stm (label-≃-sym (disc-insertion S₁ Q T) (disc-label-from S₁ Q T (L ∘ PExt) (M ∘ PExt)) .get Z)
parallel-label-from (Join S₁ S₂) BHere (BExt Q) (Susp T) p L M .get (PShift Z) = refl≃stm
parallel-label-from (Join S₁ S₂) (BExt P) BHere (Susp T) p L M .get (PExt Z) = disc-label-from S₁ P T (L ∘ PExt) (M ∘ PExt) .get Z
parallel-label-from (Join S₁ S₂) (BExt P) BHere (Susp T) p L M .get (PShift Z) = refl≃stm
parallel-label-from (Join S₁ S₂) (BExt P) (BExt Q) (Susp T) p L M .get (PExt Z) = parallel-label-from S₁ P Q T (proj-ext p) (L ∘ PExt) (M ∘ PExt) .get Z
parallel-label-from (Join S₁ S₂) (BExt P) (BExt Q) (Susp T) p L M .get (PShift Z) = refl≃stm
parallel-label-from (Join S₁ S₂) (BShift P) (BShift Q) T p L M .get (PExt Z) = refl≃stm
parallel-label-from (Join S₁ S₂) (BShift P) (BShift Q) T p L M .get (PShift Z) = parallel-label-from S₂ P Q T (proj-shift p) (L ∘ PShift) M .get Z

label-from-insertion-≃ : (S : Tree n)
                       → (p : Branch S d)
                       → (T : Tree m)
                       → .⦃ lh : has-trunk-height d T ⦄
                       → {L : Label X S}
                       → {L′ : Label Y S}
                       → {M : Label X T}
                       → {M′ : Label Y T}
                       → L ≃l L′
                       → M ≃l M′
                       → label-from-insertion S p T L M ≃l label-from-insertion S p T L′ M′
label-from-insertion-≃ (Join S₁ S₂) BHere T p q = ++l-≃ q [ (λ P → p .get (PShift P)) ]
label-from-insertion-≃ (Join S₁ S₂) (BExt P) (Susp T) p q .get PHere = q .get PHere
label-from-insertion-≃ (Join S₁ S₂) (BExt P) (Susp T) p q .get (PExt Z) = label-from-insertion-≃ S₁ P T [ (λ Z → p .get (PExt Z)) ] [ (λ Z → q .get (PExt Z)) ] .get Z
label-from-insertion-≃ (Join S₁ S₂) (BExt P) (Susp T) p q .get (PShift Z) = replace-label-≃ [ (λ Z → p .get (PShift Z)) ] (q .get (PShift PHere)) .get Z
label-from-insertion-≃ (Join S₁ S₂) (BShift P) T p q .get PHere = p .get PHere
label-from-insertion-≃ (Join S₁ S₂) (BShift P) T p q .get (PExt Z) = p .get (PExt Z)
label-from-insertion-≃ (Join S₁ S₂) (BShift P) T p q .get (PShift Z) = label-from-insertion-≃ S₂ P T [ (λ Z → p .get (PShift Z)) ] q .get Z

label-from-prune-≃ : (S : Tree n)
                   → (p : Branch S d)
                   → {L : Label X S}
                   → {L′ : Label Y S}
                   → {M : Label X (n-disc (pred (ih p)))}
                   → {M′ : Label Y (n-disc (pred (ih p)))}
                   → L ≃l L′
                   → M ≃l M′
                   → label-from-prune S p L M ≃l label-from-prune S p L′ M′
label-from-prune-≃ S P p q = label-from-insertion-≃ S P (n-disc (pred (ih P))) ⦃ prune-tree-lem S P ⦄ p q

connect-bp-left : (S : Tree n)
                → (T : Tree m)
                → (P : Branch S l)
                → Branch (S ++t T) l
connect-bp-left (Join S₁ S₂) T BHere = BHere
connect-bp-left (Join S₁ S₂) T (BExt P) = BExt P
connect-bp-left (Join S₁ S₂) T (BShift P) = BShift (connect-bp-left S₂ T P)

connect-bp-left-prop : (S : Tree n)
                     → (T : Tree m)
                     → (P : Branch S l)
                     → SPath (⌊ connect-bp-left S T P ⌋p)
                     ≃stm ap (++t-inc-left S T) ⌊ P ⌋p
connect-bp-left-prop (Join S₁ S₂) T BHere = refl≃stm
connect-bp-left-prop (Join S₁ S₂) T (BExt P) = refl≃stm
connect-bp-left-prop (Join S₁ S₂) T (BShift P) = compute-≃ (SShift≃ refl≃ (connect-bp-left-prop S₂ T P))

connect-bp-left-height : (S : Tree n)
                       → (T : Tree m)
                       → (P : Branch S l)
                       → ih (connect-bp-left S T P) ≃n ih P
connect-bp-left-height (Join S₁ S₂) T BHere = refl≃n
connect-bp-left-height (Join S₁ S₂) T (BExt P) = refl≃n
connect-bp-left-height (Join S₁ S₂) T (BShift P) = connect-bp-left-height S₂ T P

insertion-bp-left : (S : Tree n)
                  → (T : Tree m)
                  → (P : Branch S l)
                  → (U : Tree n′)
                  → .⦃ _ : has-trunk-height l U ⦄
                  → insertion-tree (S ++t T) (connect-bp-left S T P) U ≃′ insertion-tree S P U ++t T
insertion-bp-left (Join S₁ S₂) T BHere U = ++t-assoc U S₂ T
insertion-bp-left (Join S₁ S₂) T (BExt P) (Susp U) = refl≃′
insertion-bp-left (Join S₁ S₂) T (BShift P) U = Join≃′ refl≃′ (insertion-bp-left S₂ T P U)

κ-bp-left-inc-left : (S : Tree n)
                          → (T : Tree m)
                          → (P : Branch S l)
                          → (U : Tree n′)
                          → .⦃ _ : has-trunk-height l U ⦄
                          → ap (++t-inc-left S T) ●l (κ (S ++t T) (connect-bp-left S T P) U ,, S⋆)
                            ≃l
                            κ S P U ●l (++t-inc-left (insertion-tree S P U) T)
κ-bp-left-inc-left (Join S₁ S₂) T BHere U .get PHere = SPath≃ (begin
  < ++t-inc-left′ U (S₂ ++t T) PHere >p
    ≈⟨ ++t-inc-left-phere U (S₂ ++t T) ⟩
  < PHere >p
    ≈⟨ Here≃ (≃′-to-≃ (++t-assoc U S₂ T)) ⟩
  < PHere >p
    ≈˘⟨ ++t-inc-left-phere (U ++t S₂) T ⟩
  < ++t-inc-left′ (U ++t S₂) T PHere >p
    ≈˘⟨ ap′-≃ (++t-inc-left′ (U ++t S₂) T) (++t-inc-left-phere U S₂) ⟩
  < ++t-inc-left′ (U ++t S₂) T
      (++t-inc-left′ U S₂ PHere) >p ∎)
  where
    open Reasoning path-setoid
κ-bp-left-inc-left (Join S₁ S₂) T BHere U .get (PExt Z) = begin
  < canonical-label (Susp S₁) U (PExt Z) >>= ++t-inc-left U (S₂ ++t T) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = canonical-label (Susp S₁) U (PExt Z)})
              [ (λ P → SPath≃ (++t-inc-left-assoc U S₂ T .get P)) ]
              (S⋆-≃ (≃′-to-≃ (sym≃′ (++t-assoc U S₂ T)))) ⟩
  < canonical-label (Susp S₁) U (PExt Z)
    >>= ++t-inc-left U S₂ ●lt ++t-inc-left (U ++t S₂) T >stm
    ≈˘⟨ >>=-assoc (canonical-label (Susp S₁) U (PExt Z)) _ _ ⟩
  < canonical-label (Susp S₁) U (PExt Z)
    >>= ++t-inc-left U S₂
    >>= ++t-inc-left (U ++t S₂) T >stm ∎
  where
    open Reasoning stm-setoid
κ-bp-left-inc-left (Join S₁ S₂) T BHere U .get (PShift Z) = SPath≃ (++t-inc-assoc U S₂ T .get Z)
κ-bp-left-inc-left (Join S₁ S₂) T (BExt P) (Susp U) .get PHere = refl≃stm
κ-bp-left-inc-left (Join S₁ S₂) T (BExt P) (Susp U) .get (PExt Z) = begin
  < SExt (κ S₁ P U Z) >stm
    ≈˘⟨ SExt≃ (>>=-id (κ S₁ P U Z)) refl≃ ⟩
  < SExt (κ S₁ P U Z >>= id-label-wt (insertion-tree S₁ P U)) >stm
    ≈˘⟨ >>=-ext (κ S₁ P U Z) (id-label-wt (insertion-tree S₁ P U)) ⟩
  < κ S₁ P U Z >>= map-ext {T = S₂ ++t T} (id-label-wt (insertion-tree S₁ P U)) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = κ S₁ P U Z}) [ (λ Z → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ (SShift≃ refl≃ (SPath≃ (++t-inc-left-phere S₂ T))))) ⟩
  < κ S₁ P U Z >>= (SPath ∘ PExt ,, SArr (SPath PHere) S⋆ (SPath (PShift (++t-inc-left′ S₂ T PHere)))) >stm ∎
  where
    open Reasoning stm-setoid
κ-bp-left-inc-left (Join S₁ S₂) T (BExt P) (Susp U) .get (PShift Z) = compute-≃ refl≃stm
κ-bp-left-inc-left (Join S₁ S₂) T (BShift P) U .get PHere = SPath≃ (Here≃ (≃′-to-≃ (insertion-bp-left (Join S₁ S₂) T (BShift P) U)))
κ-bp-left-inc-left (Join S₁ S₂) T (BShift P) U .get (PExt Z) = compute-≃ (SExt≃ refl≃stm (≃′-to-≃ (insertion-bp-left S₂ T P U)))
κ-bp-left-inc-left (Join S₁ S₂) T (BShift P) U .get (PShift Z) = begin
  < SShift (κ (S₂ ++t T) (connect-bp-left S₂ T P) U ⦃ _ ⦄ (++t-inc-left′ S₂ T Z)) >stm
    ≈⟨ SShift≃ refl≃ (κ-bp-left-inc-left S₂ T P U .get Z) ⟩
  < SShift (κ S₂ P U Z >>= ++t-inc-left (insertion-tree S₂ P U) T) >stm
    ≈˘⟨ >>=-shift (κ S₂ P U Z) (++t-inc-left (insertion-tree S₂ P U) T) ⟩
  < κ S₂ P U Z >>= map-shift {S = S₁} (++t-inc-left (insertion-tree S₂ P U) T) >stm
    ≈⟨ >>=-≃ (refl≃stm {a = κ S₂ P U Z}) [ (λ Z → compute-≃ refl≃stm) ] refl≃sty ⟩
  < κ S₂ P U Z >>= label₂ (++t-inc-left (Join S₁ (insertion-tree S₂ P U)) T) >stm ∎
  where open Reasoning stm-setoid

κ-bp-left-inc-right : (S : Tree n)
                           → (T : Tree m)
                           → (P : Branch S l)
                           → (U : Tree n′)
                           → .⦃ _ : has-trunk-height l U ⦄
                           → ap (++t-inc-right S T)
                             ●l (κ (S ++t T) (connect-bp-left S T P) U ,, S⋆)
                           ≃l ap (++t-inc-right (insertion-tree S P U) T)
κ-bp-left-inc-right (Join S₁ S₂) T BHere U .get Z = SPath≃ (++t-inc-right-assoc U S₂ T .get Z)
κ-bp-left-inc-right (Join S₁ S₂) T (BExt P) (Susp U) .get Z = compute-≃ refl≃stm
κ-bp-left-inc-right (Join S₁ S₂) T (BShift P) U .get Z = compute-≃ (SShift≃ refl≃ (κ-bp-left-inc-right S₂ T P U .get Z))

label-from-bp-left : (S : Tree n)
                 → (T : Tree m)
                 → (P : Branch S l)
                 → (U : Tree n′)
                 → .⦃ _ : has-trunk-height l U ⦄
                 → (L : Label X S)
                 → (M : Label X T)
                 → (N : Label X U)
                 → label-from-insertion (S ++t T) (connect-bp-left S T P) U (L ++l M) N
                 ≃lm label-≃ (insertion-bp-left S T P U) (label-from-insertion S P U L N ++l M)
label-from-bp-left (Join S₁ S₂) T BHere U L M N .get Z = ++l-assoc N (L ∘ PShift) M .get Z
label-from-bp-left (Join S₁ S₂) T (BExt P) (Susp U) L M N .get (PExt Z) = refl≃stm
label-from-bp-left (Join S₁ S₂) T (BExt P) (Susp U) L M N .get (PShift Z) = replace-++l (L ∘ PShift) M (N (PShift PHere)) .get Z
label-from-bp-left (Join S₁ S₂) T (BShift P) U L M N .get (PExt Z) = refl≃stm
label-from-bp-left (Join S₁ S₂) T (BShift P) U L M N .get (PShift Z) = label-from-bp-left S₂ T P U (L ∘ PShift) M N .get Z

connect-bp-right : (S : Tree n)
                 → (T : Tree m)
                 → (P : Branch T l)
                 → Branch (S ++t T) l
connect-bp-right Sing T P = P
connect-bp-right (Join S₁ S₂) T P = BShift (connect-bp-right S₂ T P)

connect-bp-right-prop : (S : Tree n)
                      → (T : Tree m)
                      → (P : Branch T l)
                      → SPath ⌊ connect-bp-right S T P ⌋p
                      ≃stm ap (++t-inc-right S T) ⌊ P ⌋p
connect-bp-right-prop Sing T P = refl≃stm
connect-bp-right-prop (Join S₁ S₂) T P = compute-≃ (SShift≃ refl≃ (connect-bp-right-prop S₂ T P))

connect-bp-right-height : (S : Tree n)
                        → (T : Tree m)
                        → (P : Branch T l)
                        → ih (connect-bp-right S T P) ≃n ih P
connect-bp-right-height Sing T P = refl≃n
connect-bp-right-height (Join S₁ S₂) T P = connect-bp-right-height S₂ T P


insertion-bp-right : (S : Tree n)
                   → (T : Tree m)
                   → (P : Branch T l)
                   → (U : Tree n′)
                   → .⦃ _ : has-trunk-height l U ⦄
                   → insertion-tree (S ++t T) (connect-bp-right S T P) U ≃′ S ++t (insertion-tree T P U)
insertion-bp-right Sing T P U = refl≃′
insertion-bp-right (Join S₁ S₂) T P U = Join≃′ refl≃′ (insertion-bp-right S₂ T P U)

κ-bp-right-inc-left : (S : Tree n)
                           → (T : Tree m)
                           → (P : Branch T l)
                           → (U : Tree n′)
                           → .⦃ _ : has-trunk-height l U ⦄
                           → ap (++t-inc-left S T) ●l (κ (S ++t T) (connect-bp-right S T P) U ,, S⋆)
                           ≃l ap (++t-inc-left S (insertion-tree T P U))
κ-bp-right-inc-left Sing T P U .get PHere = κ-phere T P U ⦃ it ⦄
κ-bp-right-inc-left (Join S₁ S₂) T P U .get PHere = SPath≃ (Here≃ (≃′-to-≃ (insertion-bp-right (Join S₁ S₂) T P U)))
κ-bp-right-inc-left (Join S₁ S₂) T P U .get (PExt Z) = compute-≃ (SExt≃ refl≃stm (≃′-to-≃ (insertion-bp-right S₂ T P U)))
κ-bp-right-inc-left (Join S₁ S₂) T P U .get (PShift Z) = compute-≃ (SShift≃ refl≃ (κ-bp-right-inc-left S₂ T P U .get Z))

κ-bp-right-inc-right : (S : Tree n)
                            → (T : Tree m)
                            → (P : Branch T l)
                            → (U : Tree n′)
                            → .⦃ _ : has-trunk-height l U ⦄
                            → ap (++t-inc-right S T) ●l (κ (S ++t T) (connect-bp-right S T P) U ,, S⋆)
                            ≃l κ T P U ●l (++t-inc-right S (insertion-tree T P U))
κ-bp-right-inc-right Sing T P U = sym≃l (comp-right-unit (κ T P U))
κ-bp-right-inc-right (Join S₁ S₂) T P U = begin
  < SShift ∘ (ap (++t-inc-right S₂ T) ●l (κ (S₂ ++t T) (connect-bp-right S₂ T P) U  ,, S⋆)) >l
    ≈⟨ [ (λ Z → SShift≃ refl≃ (κ-bp-right-inc-right S₂ T P U .get Z)) ] ⟩
  < SShift ∘ κ T P U ●l ++t-inc-right S₂ (insertion-tree T P U) >l
    ≈˘⟨ comp-shift (κ T P U) (++t-inc-right S₂ (insertion-tree T P U)) ⟩
  < κ T P U ●l map-shift {S = S₁} (++t-inc-right S₂ (insertion-tree T P U)) >l
    ≈⟨ label-comp-≃ (refl≃l {L = κ T P U}) [ (λ Z → compute-≃ refl≃stm) ] refl≃sty ⟩
  < κ T P U ●l ++t-inc-right (Join S₁ S₂) (insertion-tree T P U) >l  ∎
  where
    open Reasoning (label-setoid T)

label-from-bp-right : (S : Tree n)
                    → (T : Tree m)
                    → (P : Branch T l)
                    → (U : Tree n′)
                    → .⦃ _ : has-trunk-height l U ⦄
                    → (L : Label X S)
                    → (M : Label X T)
                    → (N : Label X U)
                    → label-from-insertion′ (S ++t T) (connect-bp-right S T P) U (L ++l′ M) N
                      ≃lm
                      label-≃ (insertion-bp-right S T P U) (L ++l′ (label-from-insertion′ T P U M N))
label-from-bp-right Sing T P U L M N .get Z = refl≃stm
label-from-bp-right (Join S₁ S₂) T P U L M N .get (PExt Z) = refl≃stm
label-from-bp-right (Join S₁ S₂) T P U L M N .get (PShift Z) = label-from-bp-right S₂ T P U (λ x → L (PShift x)) M N .get Z

Orthogonal : (P : Branch S l) → (Q : Branch S l′) → Set
Orthogonal BHere BHere = ⊥
Orthogonal BHere (BExt Q) = ⊥
Orthogonal BHere (BShift Q) = ⊤
Orthogonal (BExt P) BHere = ⊥
Orthogonal (BExt P) (BExt Q) = Orthogonal P Q
Orthogonal (BExt P) (BShift Q) = ⊤
Orthogonal (BShift P) BHere = ⊤
Orthogonal (BShift P) (BExt Q) = ⊤
Orthogonal (BShift P) (BShift Q) = Orthogonal P Q

Orthogonal-sym : (P : Branch S l) → (Q : Branch S l′) → .⦃ Orthogonal P Q ⦄ → Orthogonal Q P
Orthogonal-sym BHere (BShift Q) = tt
Orthogonal-sym (BExt P) (BExt Q) = Orthogonal-sym P Q
Orthogonal-sym (BExt P) (BShift Q) = tt
Orthogonal-sym (BShift P) BHere = tt
Orthogonal-sym (BShift P) (BExt Q) = tt
Orthogonal-sym (BShift P) (BShift Q) = Orthogonal-sym P Q

orthog-bp : (P : Branch S l)
          → (Q : Branch S l′)
          → .⦃ Orthogonal P Q ⦄
          → (T : Tree m)
          → .⦃ _ : has-trunk-height (bh P) T ⦄
          → Branch (insertion-tree S P T) l′
orthog-bp BHere (BShift Q) T = connect-bp-right T _ Q
orthog-bp (BExt P) (BExt Q) (Susp T) = BExt (orthog-bp P Q T)
orthog-bp (BExt P) (BShift Q) (Susp T) = BShift Q
orthog-bp (BShift P) BHere T = BHere
orthog-bp (BShift P) (BExt Q) T = BExt Q
orthog-bp (BShift P) (BShift Q) T = BShift (orthog-bp P Q T)

orthog-bp-prop : (S : Tree n)
               → (P : Branch S l)
               → (Q : Branch S l′)
               → .⦃ _ : Orthogonal P Q ⦄
               → (T : Tree m)
               → .⦃ _ : has-trunk-height (bh P) T ⦄
               → SPath ⌊ orthog-bp P Q T ⌋p
               ≃stm κ S P T ⌊ Q ⌋p
orthog-bp-prop (Join S₁ S₂) BHere (BShift Q) T = connect-bp-right-prop T S₂ Q
orthog-bp-prop (Join S₁ S₂) (BExt P) (BExt Q) (Susp T) = compute-≃ (SExt≃ (orthog-bp-prop S₁ P Q T) refl≃)
orthog-bp-prop (Join S₁ S₂) (BExt P) (BShift Q) (Susp T) = compute-≃ refl≃stm
orthog-bp-prop (Join S₁ S₂) (BShift P) BHere T = compute-≃ refl≃stm
orthog-bp-prop (Join S₁ S₂) (BShift P) (BExt Q) T = compute-≃ refl≃stm
orthog-bp-prop (Join S₁ S₂) (BShift P) (BShift Q) T = compute-≃ (SShift≃ refl≃ (orthog-bp-prop S₂ P Q T))

orthog-bh : (P : Branch S l)
                 → (Q : Branch S l′)
                 → .⦃ _ : Orthogonal P Q ⦄
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height (bh P) T ⦄
                 → ih (orthog-bp P Q T) ≃n ih Q
orthog-bh BHere (BShift Q) T = connect-bp-right-height T _ Q
orthog-bh (BExt P) (BExt Q) (Susp T) = inst ⦃ orthog-bh P Q T ⦄
orthog-bh (BExt P) (BShift Q) (Susp T) = refl≃n
orthog-bh (BShift P) BHere T = refl≃n
orthog-bh (BShift P) (BExt Q) T = refl≃n
orthog-bh (BShift P) (BShift Q) T = orthog-bh P Q T

insertion-orthog : (S : Tree n)
                 → (P : Branch S l)
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height (bh P) T ⦄
                 → (Q : Branch S l′)
                 → .⦃ _ : Orthogonal P Q ⦄
                 → (U : Tree m′)
                 → .⦃ _ : has-trunk-height (bh Q) U ⦄
                 → insertion-tree (insertion-tree S P T) (orthog-bp P Q T) U ≃′ insertion-tree (insertion-tree S Q U) (orthog-bp Q P ⦃ Orthogonal-sym P Q ⦄ U) T
insertion-orthog (Join S₁ S₂) BHere T (BShift Q) U = insertion-bp-right T S₂ Q U
insertion-orthog (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) = Join≃′ (insertion-orthog S₁ P T Q U) Refl≃′
insertion-orthog (Join S₁ S₂) (BExt P) (Susp T) (BShift Q) U = Refl≃′
insertion-orthog (Join S₁ S₂) (BShift P) T BHere U = sym≃′ (insertion-bp-right U S₂ P T)
insertion-orthog (Join S₁ S₂) (BShift P) T (BExt Q) (Susp U) = Refl≃′
insertion-orthog (Join S₁ S₂) (BShift P) T (BShift Q) U = Join≃′ Refl≃′ (insertion-orthog S₂ P T Q U)

module _ where
  open Reasoning stm-setoid
  κ-orthog : (S : Tree n)
                  → (P : Branch S l)
                  → (T : Tree m)
                  → .⦃ _ : has-trunk-height (bh P) T ⦄
                  → (Q : Branch S l′)
                  → .⦃ _ : Orthogonal P Q ⦄
                  → (U : Tree m′)
                  → .⦃ _ : has-trunk-height (bh Q) U ⦄
                  → κ S P T ●l (κ (insertion-tree S P T) (orthog-bp P Q T) U ,, S⋆)
                  ≃lm κ S Q U ●l (κ (insertion-tree S Q U) (orthog-bp Q P ⦃ Orthogonal-sym P Q ⦄ U) T ,, S⋆)
  κ-orthog (Join S₁ S₂) BHere T (BShift Q) U .get (PExt Z) = begin
    < canonical-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂
      >>= (κ (T ++t S₂) (connect-bp-right T S₂ Q) U ,, S⋆) >stm
      ≈⟨ >>=-assoc (canonical-label (Susp S₁) T (PExt Z)) (++t-inc-left T S₂) _ ⟩
    < canonical-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂ ●lt (κ (T ++t S₂) (connect-bp-right T S₂ Q) U ,, S⋆) >stm
      ≈⟨ >>=-≃ (refl≃stm {a = canonical-label (Susp S₁) T (PExt Z)}) (κ-bp-right-inc-left T S₂ Q U) (S⋆-≃ (≃′-to-≃ (insertion-bp-right T S₂ Q U))) ⟩
    < canonical-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T (insertion-tree S₂ Q U) >stm ∎
  κ-orthog (Join S₁ S₂) BHere T (BShift Q) U .get (PShift Z) = κ-bp-right-inc-right T S₂ Q U .get Z
  κ-orthog (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) .get (PExt Z) = let
    instance _ = Orthogonal-sym P Q
    in begin
    < κ S₁ P T Z >>= map-ext (κ (insertion-tree S₁ P T) (orthog-bp P Q T) U ,, S⋆) >stm
      ≈⟨ >>=-ext (κ S₁ P T Z) (κ (insertion-tree S₁ P T) (orthog-bp P Q T) U ,, S⋆) ⟩
    < SExt (κ S₁ P T Z >>= (κ (insertion-tree S₁ P T) (orthog-bp P Q T) U ,, S⋆)) >stm
      ≈⟨ SExt≃ (κ-orthog S₁ P T Q U .get Z) refl≃ ⟩
    < SExt (κ S₁ Q U Z >>= (κ (insertion-tree S₁ Q U) (orthog-bp Q P U) T ,, S⋆)) >stm
      ≈˘⟨ >>=-ext (κ S₁ Q U Z) (κ (insertion-tree S₁ Q U) (orthog-bp Q P U) T ,, S⋆) ⟩
    < κ S₁ Q U Z >>= map-ext (κ (insertion-tree S₁ Q U) (orthog-bp Q P U) T ,, S⋆) >stm ∎
  κ-orthog (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) .get (PShift Z) = SShift≃ (≃′-to-≃ (insertion-orthog S₁ P T Q U)) refl≃stm
  κ-orthog (Join S₁ S₂) (BExt P) (Susp T) (BShift Q) U .get (PExt Z) = begin
    < κ S₁ P T Z >>= ((SExt ∘ SPath) ,, SArr (SPath PHere) S⋆ (SShift (κ S₂ Q U PHere))) >stm
      ≈⟨ >>=-≃ (refl≃stm {a = κ S₁ P T Z}) refl≃l (SArr≃ refl≃stm refl≃sty (SShift≃ refl≃ (κ-phere S₂ Q U))) ⟩
    < κ S₁ P T Z >>= map-ext (id-label-wt (insertion-tree S₁ P T)) >stm
      ≈⟨ >>=-ext (κ S₁ P T Z) (id-label-wt (insertion-tree S₁ P T)) ⟩
    < SExt (κ S₁ P T Z >>= id-label-wt (insertion-tree S₁ P T)) >stm
      ≈⟨ SExt≃ (>>=-id (κ S₁ P T Z)) refl≃ ⟩
    < SExt (κ S₁ P T Z) >stm ∎
  κ-orthog (Join S₁ S₂) (BExt P) (Susp T) (BShift Q) U .get (PShift Z) = begin
    < SShift (κ S₂ Q U Z) >stm
      ≈˘⟨ SShift≃ refl≃ (>>=-id (κ S₂ Q U Z)) ⟩
    < SShift (κ S₂ Q U Z >>= id-label-wt (insertion-tree S₂ Q U)) >stm
      ≈˘⟨ >>=-shift (κ S₂ Q U Z) (id-label-wt (insertion-tree S₂ Q U)) ⟩
    < κ S₂ Q U Z >>= map-shift (id-label-wt (insertion-tree S₂ Q U)) >stm ∎
  κ-orthog (Join S₁ S₂) (BShift P) T BHere U .get (PExt Z) = sym≃stm (κ-orthog (Join S₁ S₂) BHere U (BShift P) T .get (PExt Z))
  κ-orthog (Join S₁ S₂) (BShift P) T BHere U .get (PShift Z) = sym≃stm (κ-orthog (Join S₁ S₂) BHere U (BShift P) T .get (PShift Z))
  κ-orthog (Join S₁ S₂) (BShift P) T (BExt Q) (Susp U) .get (PExt Z) = begin
    < SExt (κ S₁ Q U Z) >stm
      ≈˘⟨ SExt≃ (>>=-id (κ S₁ Q U Z)) refl≃ ⟩
    < SExt (κ S₁ Q U Z >>= id-label-wt (insertion-tree S₁ Q U)) >stm
      ≈˘⟨ >>=-ext (κ S₁ Q U Z) (id-label-wt (insertion-tree S₁ Q U)) ⟩
    < κ S₁ Q U Z >>= map-ext (id-label-wt (insertion-tree S₁ Q U)) >stm
      ≈˘⟨ >>=-≃ (refl≃stm {a = κ S₁ Q U Z}) refl≃l (SArr≃ refl≃stm refl≃sty (SShift≃ refl≃ (κ-phere S₂ P T))) ⟩
    < κ S₁ Q U Z >>= (SExt ∘ SPath ,, SArr (SPath PHere) S⋆ (SShift (κ S₂ P T PHere))) >stm ∎
  κ-orthog (Join S₁ S₂) (BShift P) T (BExt Q) (Susp U) .get (PShift Z) = begin
    < κ S₂ P T Z >>= map-shift (id-label-wt (insertion-tree S₂ P T)) >stm
      ≈⟨ >>=-shift (κ S₂ P T Z) (id-label-wt (insertion-tree S₂ P T)) ⟩
    < SShift (κ S₂ P T Z >>= id-label-wt (insertion-tree S₂ P T)) >stm
      ≈⟨ SShift≃ refl≃ (>>=-id (κ S₂ P T Z)) ⟩
    < SShift (κ S₂ P T Z) >stm ∎
  κ-orthog (Join S₁ S₂) (BShift P) T (BShift Q) U .get (PExt Z) = SExt≃ refl≃stm (≃′-to-≃ (insertion-orthog S₂ P T Q U))
  κ-orthog (Join S₁ S₂) (BShift P) T (BShift Q) U .get (PShift Z) = let
    instance _ = Orthogonal-sym P Q
    in begin
    < κ S₂ P T Z >>= map-shift (κ (insertion-tree S₂ P T) (orthog-bp P Q T) U ,, S⋆) >stm
      ≈⟨ >>=-shift (κ S₂ P T Z) (κ (insertion-tree S₂ P T) (orthog-bp P Q T) U ,, S⋆) ⟩
    < SShift (κ S₂ P T Z >>= (κ (insertion-tree S₂ P T) (orthog-bp P Q T) U ,, S⋆)) >stm
      ≈⟨ SShift≃ refl≃ (κ-orthog S₂ P T Q U .get Z) ⟩
    < SShift (κ S₂ Q U Z >>= (κ (insertion-tree S₂ Q U) (orthog-bp Q P U) T ,, S⋆)) >stm
      ≈˘⟨ >>=-shift (κ S₂ Q U Z) (κ (insertion-tree S₂ Q U) (orthog-bp Q P U) T ,, S⋆) ⟩
    < κ S₂ Q U Z >>= map-shift (κ (insertion-tree S₂ Q U) (orthog-bp Q P U) T ,, S⋆) >stm ∎

  label-from-insertion′-replace : (S : Tree n)
                                → (P : Branch S l)
                                → (T : Tree m)
                                → .⦃ _ : has-trunk-height l T ⦄
                                → (L : Label X S)
                                → (M : Label X T)
                                → (a : STm X)
                                → label-from-insertion′ S P T (replace-label L a) M ≃l replace-label (label-from-insertion′ S P T L M) a
  label-from-insertion′-replace (Join S₁ S₂) BHere T L M a = sym≃l (replace-replace (M ++l′ (L ∘ PShift)) (L PHere) a)
  label-from-insertion′-replace (Join S₁ S₂) (BExt P) (Susp T) L M a .get PHere = refl≃stm
  label-from-insertion′-replace (Join S₁ S₂) (BExt P) (Susp T) L M a .get (PExt Z) = refl≃stm
  label-from-insertion′-replace (Join S₁ S₂) (BExt P) (Susp T) L M a .get (PShift Z) = refl≃stm
  label-from-insertion′-replace (Join S₁ S₂) (BShift P) T L M a .get PHere = refl≃stm
  label-from-insertion′-replace (Join S₁ S₂) (BShift P) T L M a .get (PExt Z) = refl≃stm
  label-from-insertion′-replace (Join S₁ S₂) (BShift P) T L M a .get (PShift Z) = refl≃stm

  label-from-orthog-lem : (S₁ : Tree n)
                        → (S₂ : Tree n′)
                        → (T : Tree m)
                        → (Q : Branch S₂ l′)
                        → (U : Tree m′)
                        → .⦃ _ : has-trunk-height (bh Q) U ⦄
                        → (L : Label X (Join S₁ S₂))
                        → (M : Label X T)
                        → (N : Label X U)
                        → label-from-insertion′ (T ++t S₂) (connect-bp-right T S₂ Q) U (replace-label (M ++l′ L ∘ PShift) (L PHere)) N
                          ≃lm
                          label-≃ (insertion-bp-right T S₂ Q U) (replace-label (M ++l′ label-from-insertion′ S₂ Q U (L ∘ PShift) N) (L PHere))
  label-from-orthog-lem S₁ S₂ Sing Q U L M N .get Z = label-from-insertion′-replace S₂ Q U (L ∘ PShift) N (L PHere) .get Z
  label-from-orthog-lem S₁ S₂ (Join T₁ T₂) Q U L M N .get (PExt Z) = refl≃stm
  label-from-orthog-lem S₁ S₂ (Join T₁ T₂) Q U L M N .get (PShift Z) = label-from-bp-right T₂ S₂ Q U (M ∘ PShift) (L ∘ PShift) N .get Z

  label-from-orthog : (S : Tree n)
                    → (P : Branch S l)
                    → (T : Tree m)
                    → .⦃ _ : has-trunk-height (bh P) T ⦄
                    → (Q : Branch S l′)
                    → .⦃ _ : Orthogonal P Q ⦄
                    → (U : Tree m′)
                    → .⦃ _ : has-trunk-height (bh Q) U ⦄
                    → (L : Label X S)
                    → (M : Label X T)
                    → (N : Label X U)
                    → label-from-insertion′ (insertion-tree S P T) (orthog-bp P Q T) U (label-from-insertion′ S P T L M) N
                      ≃lm
                      label-≃ (insertion-orthog S P T Q U) (label-from-insertion′ (insertion-tree S Q U) (orthog-bp Q P ⦃ Orthogonal-sym P Q ⦄ U) T (label-from-insertion′ S Q U L N) M)
  label-from-orthog (Join S₁ S₂) BHere T (BShift Q) U L M N = label-from-orthog-lem S₁ S₂ T Q U L M N
  label-from-orthog (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) L M N .get (PExt Z) = label-from-orthog S₁ P T Q U (L ∘ PExt) (M ∘ PExt) (N ∘ PExt) .get Z
  label-from-orthog (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) L M N .get (PShift Z) = refl≃stm
  label-from-orthog (Join S₁ S₂) (BExt P) (Susp T) (BShift Q) U L M N .get (PExt Z) = refl≃stm
  label-from-orthog (Join S₁ S₂) (BExt P) (Susp T) (BShift Q) U L M N .get (PShift Z) = refl≃stm
  label-from-orthog (Join S₁ S₂) (BShift P) T BHere U L M N = sym≃lm (label-≃-sym-max (insertion-bp-right U S₂ P T) (label-from-orthog-lem S₁ S₂ U P T L N M))
  label-from-orthog (Join S₁ S₂) (BShift P) T (BExt Q) (Susp U) L M N .get (PExt Z) = refl≃stm
  label-from-orthog (Join S₁ S₂) (BShift P) T (BExt Q) (Susp U) L M N .get (PShift Z) = refl≃stm
  label-from-orthog (Join S₁ S₂) (BShift P) T (BShift Q) U L M N .get (PExt Z) = refl≃stm
  label-from-orthog (Join S₁ S₂) (BShift P) T (BShift Q) U L M N .get (PShift Z) = label-from-orthog S₂ P T Q U (L ∘ PShift) M N .get Z

insertion-bd-1 : (S : Tree n)
               → (p : Branch S l)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height (bh p) T ⦄
               → (d : ℕ)
               → .(d ≤ trunk-height T)
               → .(ih p ≥ tree-dim T)
               → tree-bd d S ≃′ tree-bd d (insertion-tree S p T)
insertion-bd-1 (Join S₁ S₂) p T zero q r = refl≃′
insertion-bd-1 (Join S₁ S₂) BHere (Susp T) (suc d) q r = let
  .lem : d ≤ tree-dim S₁
  lem = ≤-pred (≤-trans q (≤-trans (s≤s (trunk-height-dim T)) r))
  in Join≃′ (linear-tree-unique (tree-bd d S₁)
                              ⦃ bd-trunk-height d S₁ (≤-trans lem (≤-reflexive (sym (linear-trunk-height S₁)))) ⦄
                              (tree-bd d T)
                              ⦃ bd-trunk-height d T (≤-pred q) ⦄
                              (trans (tree-dim-bd′ d S₁ lem) (sym (tree-dim-bd′ d T (≤-trans (≤-pred q) (trunk-height-dim T))))))
          refl≃′
insertion-bd-1 (Join S₁ S₂) (BExt p) (Susp T) (suc d) q r = Join≃′ (insertion-bd-1 S₁ p T d (≤-pred q) (≤-pred r)) refl≃′
insertion-bd-1 (Join S₁ S₂) (BShift p) T (suc d) q r = Join≃′ refl≃′ (insertion-bd-1 S₂ p T (suc d) q r)

canonical-κ-comm-1 : (S : Tree n)
                          → (p : Branch S l)
                          → (T : Tree m)
                          → .⦃ _ : has-trunk-height (bh p) T ⦄
                          → (d : ℕ)
                          → (d < ih p)
                          → (q : d ≤ trunk-height T)
                          → (r : ih p ≥ tree-dim T)
                          → (b : Bool)
                          → ap (tree-inc-label d S b) ●l (κ S p T ,, S⋆) ≃lm label-≃ (insertion-bd-1 S p T d q r) (ap (tree-inc-label d (insertion-tree S p T) b))
canonical-κ-comm-1 S P T zero p q r false .get Z = κ-phere S P T
canonical-κ-comm-1 S P T zero p q r true .get Z = κ-last-path S P T
canonical-κ-comm-1 (Join S₁ S₂) (BHere ⦃ l ⦄) (Susp T) (suc d) p q r b .get (PExt Z) = begin
  < canonical-label (Susp S₁) (Susp T) (PExt (tree-inc-label′ d S₁ b Z))
        >>= ++t-inc-left (Susp T) S₂ >stm
    ≈⟨ >>=-≃ lem2 refl≃l refl≃sty ⟩
  < SPath (PExt (tree-inc-label′ d T b (is-linear-max-path (tree-bd d T)))) >stm
    ≈⟨ SPath≃ (Ext≃ (ap′-≃ (tree-inc-label′ d T b) lem) refl≃) ⟩
  < SPath (PExt (tree-inc-label′ d T b (ppath-≃ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z))) >stm ∎
  where
    instance _ = bd-trunk-height d T (≤-pred q)
    instance _ = is-linear-bd d S₁

    lem : is-linear-max-path (tree-bd d T) ≃p
            ppath-≃ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z
    lem = begin
      < is-linear-max-path (tree-bd d T) >p
        ≈⟨ max-path-lin-tree (tree-bd d T) Z (≃′-to-≃ (sym≃′ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) (trans (tree-dim-bd′ d S₁ (≤-pred (≤-pred (m≤n⇒m≤1+n p)))) (sym (tree-dim-bd′ d T (≤-trans (≤-pred q) (trunk-height-dim T)))))))) ⟩
      < Z >p
        ≈⟨ ppath-≃-≃p (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z ⟩
      < ppath-≃ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z >p ∎
      where
        open Reasoning path-setoid
    open Reasoning stm-setoid

    lem2 : canonical-label (Susp S₁) (Susp T) (PExt (tree-inc-label′ d S₁ b Z))
           ≃stm
           SPath (PExt (tree-inc-label′ d T b (is-linear-max-path (tree-bd d T))))
    lem2 = begin
      < canonical-label (Susp S₁) (Susp T) (PExt (tree-inc-label′ d S₁ b Z)) >stm
        ≈⟨ canonical-label-bd-< (Susp S₁) (Susp T) (suc d) b p (PExt Z) ⟩
      < canonical-stm (suc d) (tree-bd (suc d) (Susp T)) >>= tree-inc-label (suc d) (Susp T) b >stm
        ≈⟨ >>=-≃ (canonical-stm-linear (suc d) (tree-bd (suc d) (Susp T)) (cong suc (sym (tree-dim-bd′ d T (≤-trans (≤-pred q) (trunk-height-dim T)))))) (refl≃l {L = ap (tree-inc-label (suc d) (Susp T) b)}) refl≃sty ⟩
      < SPath (is-linear-max-path (tree-bd (suc d) (Susp T))) >>= (tree-inc-label (suc d) (Susp T) b) >stm
        ≡⟨⟩
      < SPath (PExt (tree-inc-label′ d T b (is-linear-max-path (tree-bd d T)))) >stm ∎
canonical-κ-comm-1 (Join S₁ S₂) BHere (Susp T) (suc d) p q r b .get (PShift Z) = refl≃stm
canonical-κ-comm-1 (Join S₁ S₂) (BExt P) (Susp T) (suc d) p q r b .get (PExt Z)
  = compute-≃ (SExt≃ (canonical-κ-comm-1 S₁ P T d (≤-pred p) (≤-pred q) (≤-pred r) b .get Z) refl≃)
canonical-κ-comm-1 (Join S₁ S₂) (BExt P) (Susp T) (suc d) p q r b .get (PShift Z)
  = compute-≃ refl≃stm
canonical-κ-comm-1 (Join S₁ S₂) (BShift P) T (suc d) p q r b .get (PExt Z)
  = compute-≃ refl≃stm
canonical-κ-comm-1 (Join S₁ S₂) (BShift P) T (suc d) p q r b .get (PShift Z)
  = compute-≃ (SShift≃ refl≃ (canonical-κ-comm-1 S₂ P T (suc d) p q r b .get Z))

data Condition (d : ℕ) (T : Tree n) (m : ℕ) : Set where
  Cond1 : d > (trunk-height T) → d ≤ m → Condition d T m
  Cond2 : d ≥ m → Condition d T m

cond-pred : Condition (suc d) (Susp T) (suc m) → Condition d T m
cond-pred (Cond1 x y) = Cond1 (≤-pred x) (≤-pred y)
cond-pred (Cond2 x) = Cond2 (≤-pred x)

bd-bp-lem : (p : Branch S l)
          → {T : Tree n}
          → .⦃ has-trunk-height (bh p) T ⦄
          → Condition d T (ih p)
          → d > bh p
bd-bp-lem p {T} (Cond1 x y) = ≤-<-trans (has-trunk-height-prop (bh p) T) x
bd-bp-lem p (Cond2 q) = <-≤-trans (bh-<-ih p) q

bd-branch : (S : Tree n)
                   → (p : Branch S l)
                   → (d : ℕ)
                   → .(q : d > bh p)
                   → Branch (tree-bd d S) l
bd-branch (Join S₁ S₂) BHere (suc d) q = BHere ⦃ is-linear-bd d S₁ ⦄
bd-branch (Join S₁ S₂) (BExt p) (suc d) q = BExt (bd-branch S₁ p d (≤-pred q))
bd-branch (Join S₁ S₂) (BShift p) (suc d) q = BShift (bd-branch S₂ p (suc d) q)

bd-branch-height : (S : Tree n)
                          → (p : Branch S l)
                          → (d : ℕ)
                          → .(q : d > bh p)
                          → ih (bd-branch S p d q) ≡ d ⊓ ih p
bd-branch-height (Join S₁ S₂) BHere (suc d) q = cong suc (tree-dim-bd d S₁)
bd-branch-height (Join S₁ S₂) (BExt p) (suc d) q = cong suc (bd-branch-height S₁ p d (≤-pred q))
bd-branch-height (Join S₁ S₂) (BShift p) (suc d) q = bd-branch-height S₂ p (suc d) q

bd-has-trunk-height : (d : ℕ) → (m : ℕ)
                    → (T : Tree n) → .⦃ has-trunk-height m T ⦄
                    → .(d > m)
                    → has-trunk-height m (tree-bd d T)
bd-has-trunk-height d zero T q = tt
bd-has-trunk-height (suc d) (suc m) (Susp T) q = inst ⦃ bd-has-trunk-height d m T (≤-pred q) ⦄

module _ where
  open Reasoning stm-setoid

  insertion-bd-2 : (S : Tree n)
                 → (p : Branch S l)
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height (bh p) T ⦄
                 → (d : ℕ)
                 → .(q : d > bh p)
                 → insertion-tree (tree-bd d S)
                                  (bd-branch S p d q)
                                  (tree-bd d T)
                                  ⦃ bd-has-trunk-height d l T q ⦄
                   ≃′ tree-bd d (insertion-tree S p T)
  insertion-bd-2 (Join S₁ S₂) BHere T (suc d) q = ++t-bd d T S₂
  insertion-bd-2 (Join S₁ S₂) (BExt p) (Susp T) (suc d) q
    = Join≃′ (insertion-bd-2 S₁ p T d (≤-pred q)) refl≃′
  insertion-bd-2 (Join S₁ S₂) (BShift p) T (suc d) q
    = Join≃′ refl≃′ (insertion-bd-2 S₂ p T (suc d) q)

  canonical-κ-comm-2 : (S : Tree n)
                           → (p : Branch S l)
                           → (T : Tree m)
                           → .⦃ _ : has-trunk-height (bh p) T ⦄
                           → (d : ℕ)
                           → (b : Bool)
                           → ih p ≥ tree-dim T
                           → (c : Condition d T (ih p))
                           → ap (tree-inc-label d S b) ●l (κ S p T ,, S⋆)
                           ≃lm κ (tree-bd d S)
                                                  (bd-branch S p d (bd-bp-lem p c))
                                                  (tree-bd d T)
                                                  ⦃ bd-has-trunk-height d l T (bd-bp-lem p c) ⦄
                               ●l (label-wt-≃ (insertion-bd-2 S p T d (bd-bp-lem p c)) (tree-inc-label d (insertion-tree S p T) b))
  canonical-κ-comm-2 S p T zero b r (Cond1 () x)
  canonical-κ-comm-2 S p T zero b r (Cond2 ())
  canonical-κ-comm-2 (Join S₁ S₂) BHere T (suc d) b r c .get (PShift Z)
    = SPath≃ (tree-inc-inc-right d T S₂ b Z)
  canonical-κ-comm-2 (Join S₁ S₂) BHere T (suc d) b r (Cond1 q r′) .get (PExt Z) = let
    instance _ = is-linear-bd d S₁
    in begin
    < canonical-label (Susp S₁) T (PExt (tree-inc-label′ d S₁ b Z))
        >>= ++t-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (canonical-label-bd->-trunk-height (Susp S₁) T (suc d) b r′ q r (PExt Z)) refl≃l refl≃sty ⟩
    < canonical-comp′ (1 + d) (tree-bd (1 + d) T) >>= tree-inc-label (1 + d) T b >>= ++t-inc-left T S₂ >stm
      ≈˘⟨ reflexive≃stm (cong (λ - → canonical-comp′ (1 + -) (tree-bd (1 + d) T) >>= tree-inc-label (1 + d) T b >>= ++t-inc-left T S₂) (trans (tree-dim-bd d S₁) (m≤n⇒m⊓n≡m (≤-pred r′)))) ⟩
    < canonical-comp′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T) >>= tree-inc-label (suc d) T b >>= ++t-inc-left T S₂ >stm
      ≈⟨ >>=-assoc (canonical-comp′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)) (tree-inc-label (suc d) T b) (++t-inc-left T S₂) ⟩
    < canonical-comp′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)
      >>= tree-inc-label (suc d) T b ●lt ++t-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (sym≃stm (canonical-label-max (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)))
               [ (λ P → SPath≃ (tree-inc-inc-left d T S₂ b P)) ]
               refl≃sty ⟩
    < canonical-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)
      >>= ++t-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
          ●lt (label-wt-≃ (++t-bd d T S₂) (tree-inc-label (suc d) (T ++t S₂) b)) >stm
      ≈˘⟨ >>=-assoc (canonical-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)) _ _ ⟩
    < canonical-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)
        >>=
        ++t-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
        >>=
        label-wt-≃ (++t-bd d T S₂) (tree-inc-label (suc d) (T ++t S₂) b) >stm ∎
  canonical-κ-comm-2 (Join S₁ S₂) BHere T (suc d) b r (Cond2 q) .get (PExt Z) = let
    instance _ = is-linear-bd d S₁
    in begin
    < canonical-label (Susp S₁) T (PExt (tree-inc-label′ d S₁ b Z))
        >>= ++t-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (canonical-label-max (Susp S₁) T (PExt (tree-inc-label′ d S₁ b Z))
                                                ⦃ inst ⦃ tree-inc-full-preserve-max d S₁ b (≤-pred q) Z ⦄ ⦄)
               refl≃l
               refl≃sty ⟩
    < canonical-comp′ (1 + tree-dim S₁) T >>= ++t-inc-left T S₂ >stm
      ≈˘⟨ >>=-≃′ (canonical-comp′-≃ (cong suc (tree-dim-≃ (≃′-to-≃ (tree-bd-full d S₁ (≤-pred q))))) (≃′-to-≃ (tree-bd-full (suc d) T (≤-trans r q)))) ((tree-bd-full (suc d) T (≤-trans r q)) ,, [ (λ P → SPath≃ (ap′-≃ (++t-inc-left′ T S₂) (tree-inc-label-full (suc d) T b (≤-trans r q) .get P))) ]) refl≃sty ⟩
    < canonical-comp′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)
      >>= tree-inc-label (suc d) T b ●lt ++t-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (sym≃stm (canonical-label-max (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z))) [ (λ P → SPath≃ (tree-inc-inc-left d T S₂ b P)) ] refl≃sty ⟩
    < canonical-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)
      >>= ++t-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
          ●lt (label-wt-≃ (++t-bd d T S₂) (tree-inc-label (suc d) (T ++t S₂) b)) >stm
      ≈˘⟨ >>=-assoc (canonical-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)) _ _ ⟩
    < canonical-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)
        >>=
        ++t-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
        >>=
        label-wt-≃ (++t-bd d T S₂) (tree-inc-label (suc d) (T ++t S₂) b) >stm ∎

  canonical-κ-comm-2 (Join S₁ S₂) (BExt p) (Susp T) (suc d) b r c .get (PExt Z) = let
    instance _ = bd-has-trunk-height d (bh p) T (bd-bp-lem p (cond-pred c))
    in begin
    < SExt (κ S₁ p T (tree-inc-label′ d S₁ b Z)) >stm
      ≈⟨ SExt≃ (canonical-κ-comm-2 S₁ p T d b (≤-pred r) (cond-pred c) .get Z) refl≃ ⟩
    < SExt ((κ (tree-bd d S₁)
                               (bd-branch S₁ p d (bd-bp-lem p (cond-pred c)))
                               (tree-bd d T)
            ●l label-wt-≃ (insertion-bd-2 S₁ p T d (bd-bp-lem p (cond-pred c)))
                            (tree-inc-label d (insertion-tree S₁ p T) b)) Z) >stm
      ≈˘⟨ >>=-ext (κ (tree-bd d S₁) (bd-branch S₁ p d (bd-bp-lem p (cond-pred c))) (tree-bd d T) Z) (label-wt-≃ (insertion-bd-2 S₁ p T d (bd-bp-lem p (cond-pred c))) (tree-inc-label d (insertion-tree S₁ p T) b)) ⟩
    < κ (tree-bd d S₁) (bd-branch S₁ p d (bd-bp-lem p (cond-pred c))) (tree-bd d T) Z
       >>= map-ext {T = S₂} (label-wt-≃ (insertion-bd-2 S₁ p T d (bd-bp-lem p (cond-pred c))) (tree-inc-label d (insertion-tree S₁ p T) b)) >stm
       ≈˘⟨ >>=-≃ (refl≃stm {a = κ (tree-bd d S₁) (bd-branch S₁ p d (bd-bp-lem p (cond-pred c))) (tree-bd d T) Z}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ (SShift≃ refl≃ (SPath≃ (tree-inc-label-phere d S₂ b))))) ⟩
    < κ (tree-bd d S₁) (bd-branch S₁ p d (bd-bp-lem p (cond-pred c))) (tree-bd d T) Z
       >>= label₁ (label-wt-≃ (Join≃′ (insertion-bd-2 S₁ p T d (bd-bp-lem p (cond-pred c))) refl≃′) (tree-inc-label (suc d) (Join (insertion-tree S₁ p T) S₂) b)) >stm ∎
  canonical-κ-comm-2 (Join S₁ S₂) (BExt p) (Susp T) (suc d) b r c .get (PShift Z)
    = compute-≃ refl≃stm
  canonical-κ-comm-2 (Join S₁ S₂) (BShift p) T (suc d) b r c .get (PExt Z)
    = compute-≃ refl≃stm
  canonical-κ-comm-2 (Join S₁ S₂) (BShift p) T (suc d) b r c .get (PShift Z) = let
    instance _ = bd-has-trunk-height (suc d) (bh p) T (bd-bp-lem p c)
    in begin
    < SShift (κ S₂ p T (tree-inc-label′ (suc d) S₂ b Z)) >stm
      ≈⟨ SShift≃ refl≃ (canonical-κ-comm-2 S₂ p T (suc d) b r c .get Z) ⟩
    < SShift (κ (tree-bd (suc d) S₂) (bd-branch S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z
        >>= label-wt-≃ (insertion-bd-2 S₂ p T (suc d) (bd-bp-lem p c)) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) >stm
      ≈˘⟨ >>=-shift (κ (tree-bd (suc d) S₂) (bd-branch S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z) (label-wt-≃ (insertion-bd-2 S₂ p T (suc d) (bd-bp-lem p c)) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) ⟩
    < κ (tree-bd (suc d) S₂) (bd-branch S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z
       >>= map-shift (label-wt-≃ (insertion-bd-2 S₂ p T (suc d) (bd-bp-lem p c)) (tree-inc-label (suc d) (insertion-tree S₂ p T) b)) >stm
      ≈⟨ >>=-≃ (refl≃stm {a = κ (tree-bd (suc d) S₂) (bd-branch S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z}) [ (λ P → compute-≃ refl≃stm) ] refl≃sty ⟩
    < κ (tree-bd (suc d) S₂) (bd-branch S₂ p (suc d) (bd-bp-lem p c)) (tree-bd (suc d) T) Z
       >>= label₂ (label-wt-≃ (Join≃′ refl≃′ (insertion-bd-2 S₂ p T (suc d) (bd-bp-lem p c)))
                           (tree-inc-label (suc d) (Join S₁ (insertion-tree S₂ p T)) b)) >stm ∎

data Bd-Conditions (d : ℕ) {S : Tree n} (P : Branch S l) (T : Tree m) : Set where
  Bd-Cond1 : d < ih P → d ≤ trunk-height T → Bd-Conditions d P T
  Bd-Cond2 : Condition d T (ih P) → Bd-Conditions d P T

Bd-Conditions-one-of : (d : ℕ) → (P : Branch S l) → (T : Tree m) → Bd-Conditions d P T
Bd-Conditions-one-of d P T with <-cmp d (ih P)
... | tri≈ ¬a b ¬c = Bd-Cond2 (Cond2 (≤-reflexive (sym b)))
... | tri> ¬a ¬b c = Bd-Cond2 (Cond2 (<⇒≤ c))
... | tri< a ¬b ¬c with <-cmp d (trunk-height T)
... | tri< a₁ ¬b₁ ¬c₁ = Bd-Cond1 a (<⇒≤ a₁)
... | tri≈ ¬a b ¬c₁ = Bd-Cond1 a (≤-reflexive b)
... | tri> ¬a ¬b₁ c = Bd-Cond2 (Cond1 c (<⇒≤ a))

pruned-bp : (S : Tree n)
          → (p : Branch S l)
          → .(bh p < pred (ih p))
          → Branch (prune-tree S p) l
pruned-bp (Join S T) (BExt p) q = BExt (pruned-bp S p (≤-pred q))
pruned-bp (Join S T) (BShift p) q = BShift (pruned-bp T p q)
pruned-bp (Join (Susp S) T) BHere q = BHere

insertion-tree-pruned-bp : (S : Tree n)
                         → (p : Branch S l)
                         → (T : Tree m)
                         → .⦃ _ : has-trunk-height (bh p) T ⦄
                         → .(q : bh p < pred (ih p))
                         → insertion-tree (prune-tree S p) (pruned-bp S p q) T ≃′ insertion-tree S p T
insertion-tree-pruned-bp (Join S₁ S₂) (BExt p) (Susp T) q = Join≃′ (insertion-tree-pruned-bp S₁ p T (≤-pred q)) refl≃′
insertion-tree-pruned-bp (Join S₁ S₂) (BShift p) T q = Join≃′ refl≃′ (insertion-tree-pruned-bp S₂ p T q)
insertion-tree-pruned-bp (Join (Susp S₁) S₂) BHere T q = refl≃′


pruned-bp-prop-2 : (S : Tree n)
               → (p : Branch S l)
               → .(q : bh p < pred (ih p))
               → SPath ⌊ pruned-bp S p q ⌋p
                 ≃stm
                 ι S
                                p
                                (n-disc (pred (ih p)))
                                ⦃ has-trunk-height-n-disc (≤-pred (bh-<-ih p)) ⦄
                                (is-linear-max-path (n-disc (pred (ih p))))
pruned-bp-prop-2 (Join S T) (BExt p) q = compute-≃ (SExt≃ (pruned-bp-prop-2 S p (≤-pred q)) refl≃)
pruned-bp-prop-2 (Join S T) (BShift p) q = compute-≃ (SShift≃ refl≃ (pruned-bp-prop-2 T p q))
pruned-bp-prop-2 (Join (Susp S) T) BHere q = refl≃stm

label-from-pruned-bp-lem : (n : ℕ)
                   → .⦃ NonZero n ⦄
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height l T ⦄
                   → (As : STy (someTree (chop-trunk l T)))
                   → ⦃ _ : n ≃n l + suc (sty-dim As) ⦄
                   → tree-dim (n-disc (pred n)) ≃n sty-dim (resuspend l As)
label-from-pruned-bp-lem {l = l} (suc n) T As ⦃ p ⦄ = ≡-to-≃n (begin
  tree-dim (n-disc n)
    ≡⟨ ≃n-to-≡ tree-dim-n-disc ⟩
  n
    ≡⟨ cong pred (≃n-to-≡ p) ⟩
  pred (l + suc (sty-dim As))
    ≡⟨ cong pred (+-suc l (sty-dim As)) ⟩
  l + sty-dim As
    ≡˘⟨ sty-dim-resuspend l T As ⟩
  sty-dim (resuspend l As) ∎)
  where
    open ≡-Reasoning

label-from-pruned-bp : (S : Tree n)
                     → (p : Branch S l)
                     → (T : Tree m)
                     → .⦃ _ : has-trunk-height l T ⦄
                     → .(q : bh p < pred (ih p))
                     → (L : Label X S)
                     → (M : Label-WT X T)
                     → L ⌊ p ⌋p ≃stm canonical-comp′ (ih p) T >>= M
                     → label-from-insertion
                         (prune-tree S p)
                         (pruned-bp S p q)
                         T
                         (label-from-prune S p L
                           (canonical-label (n-disc (pred (ih p))) T ●l M))
                         (ap M)
                       ≃lm
                       label-≃ (insertion-tree-pruned-bp S p T q)
                               (label-from-insertion S p T L (ap M))
label-from-pruned-bp (Join S₁ S₂) (BExt {n = n} p) (Susp T) q L M pf .get (PExt Z) = begin
  < label-from-insertion
      (prune-tree S₁ p)
      (pruned-bp S₁ p _) T
      (label-from-prune S₁ p (L ∘ PExt)
         ((canonical-label (n-disc (ih p)) (Susp T) ●l M) ∘ PExt))
      (ap M ∘ PExt) Z >stm
    ≈⟨ label-from-insertion-≃
         (prune-tree S₁ p)
         (pruned-bp S₁ p _) T
         (label-from-prune-≃ S₁ p refl≃l
           (label-comp-≃ [ (λ P → canonical-label-susp-lem (n-disc (pred (ih p))) T .get (PExt P)) ]
                         refl≃l
                         refl≃sty))
         refl≃l
         .get Z ⟩
  < label-from-insertion
      (prune-tree S₁ p)
      (pruned-bp S₁ p _) T
      (label-from-prune S₁ p (L ∘ PExt)
         (canonical-label (n-disc (pred (ih p))) T ●l label₁ M))
      (ap M ∘ PExt) Z >stm
    ≈⟨ label-from-pruned-bp S₁ p T (≤-pred q) (L ∘ PExt) (label₁ M) pf .get Z ⟩
  < label-≃ (insertion-tree-pruned-bp S₁ p T _)
            (label-from-insertion S₁ p T (L ∘ PExt) (ap (label₁ M))) Z >stm ∎
  where
    open Reasoning stm-setoid

label-from-pruned-bp (Join S₁ S₂) (BExt {n = n} p) (Susp T) q L M pf .get (PShift Z) = begin
  < replace-label
      (label-from-prune (Join S₁ S₂) (BExt p) L (canonical-label (Susp (n-disc (ih′ p))) (Susp T) ●l M) ∘ PShift)
      (ap M (PShift PHere)) Z >stm
    ≈⟨ replace-not-here _ (ap M (PShift PHere)) Z ⟩
  < label-from-prune (Join S₁ S₂) (BExt p) L (canonical-label (Susp (n-disc (ih′ p))) (Susp T) ●l M) (PShift Z) >stm
    ≈⟨ replace-not-here (L ∘ PShift) _ Z ⟩
  < L (PShift Z) >stm
    ≈˘⟨ replace-not-here (L ∘ PShift) (ap M (PShift PHere)) Z ⟩
  < replace-label (L ∘ PShift) (ap M (PShift PHere)) Z >stm ∎
  where
    open Reasoning stm-setoid
label-from-pruned-bp (Join S₁ S₂) (BShift p) T q L M pf .get (PExt Z) = refl≃stm
label-from-pruned-bp {l = l} (Join S₁ S₂) (BShift p) T q L M pf .get (PShift Z)
  = label-from-pruned-bp S₂ p T q (L ∘ PShift) M pf .get Z
label-from-pruned-bp (Susp (Susp S₁)) BHere T q L M pf = ≃l-to-≃lm (++l-sing (ap M) _ _)
label-from-pruned-bp (Join (Susp S₁) (Join S₂ S₃)) BHere T q L M pf
  = ++l-≃m (refl≃lm {L = ap M}) (replace-join-≃lm (L ∘ PShift) _)

insertion-trunk-height : (S : Tree n)
                        → .⦃ non-linear S ⦄
                        → (P : Branch S l)
                        → (T : Tree m)
                        → .⦃ _ : has-trunk-height l T ⦄
                        → (d : ℕ)
                        → .⦃ has-trunk-height d S ⦄
                        → has-trunk-height d (insertion-tree S P T)
insertion-trunk-height S P T zero = tt
insertion-trunk-height (Susp S) BHere T (suc d) = ⊥-elim (linear-non-linear S)
insertion-trunk-height (Susp S) (BExt P) (Susp T) (suc d) = inst ⦃ insertion-trunk-height S P T d ⦄

inserted-bp : (S : Tree n)
            → (P : Branch S l)
            → (T : Tree m)
            → .⦃ _ : has-trunk-height l T ⦄
            → .⦃ _ : non-linear T ⦄
            → (Q : Branch T l′)
            → Branch (insertion-tree S P T) l′
inserted-bp (Join S₁ S₂) BHere T Q = connect-bp-left T S₂ Q
inserted-bp (Join S₁ S₂) (BExt P) (Susp T) BHere = ⊥-elim (linear-non-linear T)
inserted-bp (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) = BExt (inserted-bp S₁ P T Q)
inserted-bp (Join S₁ S₂) (BShift P) T Q = BShift (inserted-bp S₂ P T Q)

inserted-bp-prop : (S : Tree n)
                 → (P : Branch S l)
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height l T ⦄
                 → .⦃ _ : non-linear T ⦄
                 → (Q : Branch T l′)
                 → SPath ⌊ inserted-bp S P T Q ⌋p
                 ≃stm ι S P T ⌊ Q ⌋p
inserted-bp-prop (Join S₁ S₂) BHere T Q = connect-bp-left-prop T S₂ Q
inserted-bp-prop (Join S₁ S₂) (BExt P) (Susp T) BHere = ⊥-elim (linear-non-linear T)
inserted-bp-prop (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) = compute-≃ (SExt≃ (inserted-bp-prop S₁ P T Q) refl≃)
inserted-bp-prop (Join S₁ S₂) (BShift P) T Q = compute-≃ (SShift≃ refl≃ (inserted-bp-prop S₂ P T Q))

insertion-tree-inserted-bp : (S : Tree n)
                           → (P : Branch S l)
                           → (T : Tree m)
                           → .⦃ _ : has-trunk-height l T ⦄
                           → .⦃ _ : non-linear T ⦄
                           → (Q : Branch T l′)
                           → (U : Tree m′)
                           → .⦃ _ : has-trunk-height l′ U ⦄
                           → insertion-tree (insertion-tree S P T) (inserted-bp S P T Q) U
                           ≃′ insertion-tree S P (insertion-tree T Q U) ⦃ insertion-trunk-height T Q U l ⦄
insertion-tree-inserted-bp (Join S₁ S₂) BHere T Q U = insertion-bp-left T S₂ Q U
insertion-tree-inserted-bp (Join S₁ S₂) (BExt P) (Susp T) BHere U = ⊥-elim (linear-non-linear T)
insertion-tree-inserted-bp (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) = Join≃′ (insertion-tree-inserted-bp S₁ P T Q U) refl≃′
insertion-tree-inserted-bp (Join S₁ S₂) (BShift P) T Q U = Join≃′ refl≃′ (insertion-tree-inserted-bp S₂ P T Q U)

module _ where
  open Reasoning stm-setoid

  label-from-inserted-bp : (S : Tree n)
                       → (P : Branch S l)
                       → (T : Tree m)
                       → .⦃ _ : has-trunk-height l T ⦄
                       → .⦃ _ : non-linear T ⦄
                       → (Q : Branch T l′)
                       → (U : Tree m′)
                       → .⦃ _ : has-trunk-height l′ U ⦄
                       → (L : Label X S)
                       → (M : Label X T)
                       → (N : Label X U)
                       → label-from-insertion (insertion-tree S P T) (inserted-bp S P T Q) U (label-from-insertion S P T L M) N
                       ≃lm label-≃ (insertion-tree-inserted-bp S P T Q U) (label-from-insertion S P (insertion-tree T Q U) ⦃ insertion-trunk-height T Q U l ⦄ L (label-from-insertion T Q U M N))
  label-from-inserted-bp (Join S₁ S₂) BHere T Q U L M N = label-from-bp-left T S₂ Q U M (L ∘ PShift) N
  label-from-inserted-bp (Join S₁ S₂) (BExt P) (Susp T) BHere U L M N = ⊥-elim (linear-non-linear T)
  label-from-inserted-bp (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) L M N .get (PExt Z) = label-from-inserted-bp S₁ P T Q U (L ∘ PExt) (M ∘ PExt) (N ∘ PExt) .get Z
  label-from-inserted-bp (Join S₁ .(Join _ _)) (BExt P) (Susp T) (BExt Q) (Susp U) L M N .get (PShift (PExt Z)) = refl≃stm
  label-from-inserted-bp (Join S₁ .(Join _ _)) (BExt P) (Susp T) (BExt Q) (Susp U) L M N .get (PShift (PShift Z)) = refl≃stm
  label-from-inserted-bp (Join S₁ S₂) (BShift P) T Q U L M N .get (PExt Z) = refl≃stm
  label-from-inserted-bp (Join S₁ S₂) (BShift P) T Q U L M N .get (PShift Z) = label-from-inserted-bp S₂ P T Q U (L ∘ PShift) M N .get Z
