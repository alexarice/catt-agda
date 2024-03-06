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
open import Catt.Wedge
open import Catt.Wedge.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
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

branch-type-is-path-type : (P : Branch S d) → getPathType ⌊ P ⌋p ≃sty branch-type S P
branch-type-is-path-type {S = Join S₁ S₂} BHere = map-sty-ext-≃ (linear-max-path-type S₁ (is-linear-max-path S₁))
branch-type-is-path-type (BExt P) = map-sty-ext-≃ (branch-type-is-path-type P)
branch-type-is-path-type (BShift P) = map-sty-shift-≃ (branch-type-is-path-type P)

lh-linear : (S : Tree n) → .⦃ is-linear S ⦄ → (P : Branch S l) → lh P ≡ tree-dim S
lh-linear (Susp S) BHere = refl
lh-linear (Susp S) (BExt P) = cong suc (lh-linear S P)

insertion-tree-dim : (S : Tree n)
                   → (P : Branch S l)
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height l T ⦄
                   → (lh P ≥ tree-dim T)
                   → tree-dim (S >>[ P ] T) ≤ tree-dim S
insertion-tree-dim (Join S₁ S₂) BHere T p = begin
  tree-dim (T ++t S₂)
    ≡⟨ ++t-dim T S₂ ⟩
  tree-dim T ⊔ tree-dim S₂
    ≤⟨ ⊔-mono-≤ p (suc-pred-≤ (tree-dim S₂)) ⟩
  suc (tree-dim S₁) ⊔ suc (pred (tree-dim S₂))
    ≡⟨ ⊔-comm (suc (tree-dim S₁)) (suc (pred (tree-dim S₂))) ⟩
  suc (pred (tree-dim S₂)) ⊔ suc (tree-dim S₁) ∎
  where
    open ≤-Reasoning
insertion-tree-dim (Join S₁ S₂) (BExt P) (Susp T) p
  = s≤s (⊔-monoʳ-≤ (pred (tree-dim S₂)) (insertion-tree-dim S₁ P T (≤-pred p)))
insertion-tree-dim (Join S₁ S₂) (BShift P) T p
  = s≤s (⊔-monoˡ-≤ (tree-dim S₁) (∸-monoˡ-≤ 1 (insertion-tree-dim S₂ P T p)))

κ-phere : (S : Tree n)
        → (p : Branch S d)
        → (T : Tree m)
        → .⦃ _ : has-trunk-height d T ⦄
        → κ S p T PHere ≃stm SHere {S = S >>[ p ] T}
κ-phere (Join S₁ S₂) BHere T = SPath≃ (++t-inc-left-phere T S₂)
κ-phere (Join S₁ S₂) (BExt p) (Susp T) = refl≃stm
κ-phere (Join S₁ S₂) (BShift p) T = refl≃stm

label-from-replace-lem : (L : Label X S)
                       → (a : STm X)
                       → (P : Branch S l)
                       → (M : Label X T)
                       → .⦃ _ : has-trunk-height l T ⦄
                       → replace-label L a >>l[ P ] M ≃lm L >>l[ P ] M
label-from-replace-lem L a BHere M = refl≃lm
label-from-replace-lem {T = Susp T} L a (BExt P) M .get (PExt Z) = refl≃stm
label-from-replace-lem {T = Susp T} L a (BExt P) M .get (PShift Z) = refl≃stm
label-from-replace-lem L a (BShift P) M .get (PExt Z) = refl≃stm
label-from-replace-lem L a (BShift P) M .get (PShift Z) = refl≃stm

module _ where
  open Reasoning stm-setoid

  κ-last-path : (S : Tree n)
              → (P : Branch S d)
              → (T : Tree m)
              → .⦃ _ : has-trunk-height d T ⦄
              → κ S P T (last-path S) ≃stm SPath (last-path (S >>[ P ] T))
  κ-last-path (Join S₁ S₂) (BExt P) (Susp T) = compute-≃ refl≃stm
  κ-last-path (Join S₁ S₂) (BShift P) T = compute-≃ (SShift≃ refl≃ (κ-last-path S₂ P T))
  κ-last-path (Susp S₁) BHere T = SPath≃ (++t-inc-right-last-path T Sing)
  κ-last-path (Join S₁ S₂@(Join S₃ S₄)) BHere T = SPath≃ (++t-inc-right-last-path T S₂)

  ι-comm : (L : Label X S)
         → (P : Branch S d)
         → (M : Label X T)
         → .⦃ _ : has-trunk-height d T ⦄
         → (As : STy X)
         → ι S P T ●l (L >>l[ P ] M ,, As) ≃l M
  ι-comm L BHere M A .get Z = ++l-inc-left M (L ∘ PShift) A .get Z
  ι-comm {T = Susp T} L (BExt P) M A .get PHere = refl≃stm
  ι-comm {T = Susp T} L (BExt P) M A .get (PExt Z)
    = ι-comm (L ∘ PExt) P (M ∘ PExt) _ .get Z
  ι-comm {T = Susp T} L (BExt P) M A .get (PShift PHere) = refl≃stm
  ι-comm L (BShift P) M = ι-comm (L ∘ PShift) P M

  κ-comm : (L : Label X S)
         → (P : Branch S d)
         → (M : Label X T)
         → .⦃ _ : has-trunk-height d T ⦄
         → (Bs : STy X)
         → L ⌊ P ⌋p ≃stm standard-coh′ (lh P) T >>= (M ,, Bs)
         → κ S P T ●l (L >>l[ P ] M ,, Bs) ≃lm L
  κ-comm {S = Join S₁ S₂} {T = T} L BHere M Bs q .get (PExt Z) = begin
    < standard-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂
      >>= (M ++l (L ∘ PShift) ,, Bs) >stm
      ≈⟨ >>=-assoc (standard-label (Susp S₁) T (PExt Z))
                   (++t-inc-left T S₂)
                   ((M ++l L ∘ PShift ,, Bs)) ⟩
    < standard-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂ ●lt (M ++l L ∘ PShift ,, Bs) >stm
      ≈⟨ >>=-≃ (standard-label-max (Susp S₁) T (PExt Z))
               (++l-inc-left M (L ∘ PShift) Bs) refl≃sty ⟩
    < standard-coh′ (suc (tree-dim S₁)) T >>= (M ,, Bs) >stm
      ≈˘⟨ q ⟩
    < L (PExt (is-linear-max-path S₁)) >stm
      ≈⟨ ap-≃ (refl≃l {L = L ∘ PExt}) (max-path-lin-tree S₁ Z refl≃) ⟩
    < L (PExt Z) >stm ∎
  κ-comm L BHere M Bs q .get (PShift Z) = ++l-inc-right M (L ∘ PShift) Bs Z
  κ-comm {T = Susp T} L (BExt {n = n} P) M Bs q .get (PExt Z) = κ-comm (L ∘ PExt) P (M ∘ PExt) _ q .get Z
  κ-comm {T = Susp T} L (BExt P) M Bs q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
  κ-comm L (BShift P) M Bs q .get (PExt Z) = refl≃stm
  κ-comm L (BShift P) M Bs q .get (PShift Z) = κ-comm (L ∘ PShift) P M Bs q .get Z

disc-insertion : (S : Tree n)
               → .⦃ is-linear S ⦄
               → (P : Branch S l)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height l T ⦄
               → S >>[ P ] T ≃′ T
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

disc-label-from : (L : Label X S)
                → .⦃ _ : is-linear S ⦄
                → (P : Branch S l)
                → {T : Tree m}
                → (M : Label X T)
                → .⦃ _ : has-trunk-height l T ⦄
                → L >>l[ P ] M ≃l label-≃ (disc-insertion S P T) M
disc-label-from {S = Susp S} L BHere M = ++l-right-unit M (L ∘ PShift)
disc-label-from {S = Susp S} L (BExt P) {Susp T} M .get PHere = refl≃stm
disc-label-from {S = Susp S} L (BExt P) {Susp T} M .get (PExt Z) = disc-label-from (L ∘ PExt) P (M ∘ PExt) .get Z
disc-label-from {S = Susp S} L (BExt P) {Susp T} M .get (PShift PHere) = refl≃stm

insertion-disc : (S : Tree n)
               → (P : Branch S l)
               → (S >>[ P ] (n-disc (lh P))) ⦃ has-trunk-height-n-disc (<⇒≤ (bh-<-lh P)) ⦄ ≃′ S
insertion-disc (Join S₁ S₂) BHere = Join≃′ (linear-tree-unique (n-disc (tree-dim S₁)) S₁ (≃n-to-≡ it)) refl≃′
insertion-disc (Join S₁ S₂) (BExt P) = Join≃′ (insertion-disc S₁ P) refl≃′
insertion-disc (Join S₁ S₂) (BShift P) = Join≃′ refl≃′ (insertion-disc S₂ P)

disc-label-from-2 : (L : Label X S)
                  → (P : Branch S l)
                  → (M : Label X (n-disc (lh P)))
                  → L ⌊ P ⌋p ≃stm M (is-linear-max-path (n-disc (lh P)))
                  → (L >>l[ P ] M) ⦃ has-trunk-height-n-disc (<⇒≤ (bh-<-lh P)) ⦄
                    ≃lm
                    label-≃ (insertion-disc S P) L
disc-label-from-2 {S = Join S T} L BHere M q .get (PExt Z) = begin
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
disc-label-from-2 L BHere M q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
disc-label-from-2 L (BExt P) M q .get (PExt Z) = disc-label-from-2 (L ∘ PExt) P (M ∘ PExt) q .get Z
disc-label-from-2 L (BExt P) M q .get (PShift Z) = replace-not-here (L ∘ PShift) (M (PShift PHere)) Z
disc-label-from-2 L (BShift P) M q .get (PExt Z) = refl≃stm
disc-label-from-2 L (BShift P) M q .get (PShift Z) = disc-label-from-2 (L ∘ PShift) P M q .get Z

label-from-insertion-map : (f : STm X → STm Y)
                         → (L : Label X S)
                         → (P : Branch S l)
                         → (M : Label X T)
                         → .⦃ _ : has-trunk-height l T ⦄
                         → (f ∘ (L >>l[ P ] M)) ≃l f ∘ L >>l[ P ] f ∘ M
label-from-insertion-map f L BHere M = ++l-map f M (L ∘ PShift)
label-from-insertion-map {T = Susp T} f L (BExt P) M .get PHere = refl≃stm
label-from-insertion-map {T = Susp T} f L (BExt P) M .get (PExt Z) = label-from-insertion-map f (L ∘ PExt) P (M ∘ PExt) .get Z
label-from-insertion-map {T = Susp T} f L (BExt P) M .get (PShift Z) = replace-label-map f (L ∘ PShift) (M (PShift PHere)) .get Z
label-from-insertion-map f L (BShift P) M .get PHere = refl≃stm
label-from-insertion-map f L (BShift P) M .get (PExt Z) = refl≃stm
label-from-insertion-map f L (BShift P) M .get (PShift Z) = label-from-insertion-map f (L ∘ PShift) P M .get Z

κ-ι-prop : (S : Tree n)
         → (P : Branch S l)
         → (T : Tree m)
         → .⦃ _ : has-trunk-height (bh P) T ⦄
         → κ S P T >>l[ P ] ι S P T ≃l id-label (S >>[ P ] T)
κ-ι-prop (Join S₁ S₂) BHere T = ++l-prop T S₂
κ-ι-prop (Join S₁ S₂) (BExt P) (Susp T) .get PHere = refl≃stm
κ-ι-prop (Join S₁ S₂) (BExt P) (Susp T) .get (PExt Z) = begin
  < (SExt ∘ κ S₁ P T >>l[ P ] SExt ∘ ι S₁ P T) Z >stm
    ≈˘⟨ label-from-insertion-map SExt (κ S₁ P T) P (ι S₁ P T) .get Z ⟩
  < (SExt ∘ (κ S₁ P T >>l[ P ] ι S₁ P T)) Z >stm
    ≈⟨ compute-≃ (SExt≃ (κ-ι-prop S₁ P T .get Z) refl≃) ⟩
  < SPath (PExt Z) >stm ∎
  where
    open Reasoning stm-setoid
κ-ι-prop (Join S₁ S₂) (BExt P) (Susp T) .get (PShift Z)
  = compute-≃ (compute-stm-≃ (replace-label-prop (SShift ∘ id-label S₂) (SShift SHere) refl≃stm .get Z))
κ-ι-prop (Join S₁ S₂) (BShift P) T .get PHere = refl≃stm
κ-ι-prop (Join S₁ S₂) (BShift P) T .get (PExt Z) = compute-≃ refl≃stm
κ-ι-prop (Join S₁ S₂) (BShift P) T .get (PShift Z) = begin
  < (SShift ∘ κ S₂ P T >>l[ P ] SShift ∘ ι S₂ P T) Z >stm
    ≈˘⟨ label-from-insertion-map SShift (κ S₂ P T) P (ι S₂ P T) .get Z ⟩
  < (SShift ∘ (κ S₂ P T >>l[ P ] ι S₂ P T)) Z >stm
    ≈⟨ compute-≃ (SShift≃ refl≃ (κ-ι-prop S₂ P T .get Z )) ⟩
  < SPath (PShift Z) >stm ∎
  where
    open Reasoning stm-setoid

κ-branch-path : (S : Tree n)
              → (P : Branch S l)
              → (T : Tree m)
              → .⦃ _ : has-trunk-height l T ⦄
              → κ S P T ⌊ P ⌋p
                ≃stm
                standard-coh′ (lh P) T >>= (ι S P T ,, S⋆)
κ-branch-path (Join S₁ S₂) BHere T
  = >>=-≃ (standard-label-max (Susp S₁) T (is-linear-max-path (Susp S₁)) ⦃ inst ⦄)
          refl≃l
          refl≃sty
κ-branch-path (Join S₁ S₂) (BExt {n = n} P) (Susp T) = begin
  < SExt (κ S₁ P T ⌊ P ⌋p) >stm
    ≈⟨ SExt≃ (κ-branch-path S₁ P T) refl≃ ⟩
  < SExt (standard-coh′ (lh P) T >>= (ι S₁ P T ,, S⋆)) >stm
   ≈˘⟨ >>=-ext (standard-coh′ (lh P) T) (ι S₁ P T ,, S⋆) ⟩
  < standard-coh′ (lh P) T >>= map-ext (ι S₁ P T ,, S⋆) >stm ∎
  where
    open Reasoning stm-setoid
κ-branch-path (Join S₁ S₂) (BShift {n = n} P) T = begin
  < SShift (κ S₂ P T ⌊ P ⌋p) >stm
    ≈⟨ SShift≃ refl≃ (κ-branch-path S₂ P T) ⟩
  < SShift (standard-coh′ (lh P) T >>= (ι S₂ P T ,, S⋆)) >stm
    ≈˘⟨ >>=-shift (standard-coh′ (lh P) T) (ι S₂ P T ,, S⋆) ⟩
  < standard-coh′ (lh P) T >>= map-shift (ι S₂ P T ,, S⋆) >stm ∎
  where
    open Reasoning stm-setoid

insertion-parallel : (S : Tree n)
                   → (P : Branch S l)
                   → (Q : Branch S l′)
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height l T ⦄
                   → .⦃ _ : has-trunk-height l′ T ⦄
                   → ⌊ P ⌋p ≃p ⌊ Q ⌋p
                   → S >>[ P ] T ≃′ S >>[ Q ] T
insertion-parallel (Join S₁ S₂) BHere BHere T Z = Refl≃′
insertion-parallel (Join S₁ S₂) BHere (BExt Q) (Susp T) p = Join≃′ (sym≃′ (disc-insertion S₁ Q T)) Refl≃′
insertion-parallel (Join S₁ S₂) (BExt P) BHere (Susp T) p = Join≃′ (disc-insertion S₁ P T) Refl≃′
insertion-parallel (Join S₁ S₂) (BExt P) (BExt Q) (Susp T) p = Join≃′ (insertion-parallel S₁ P Q T (proj-ext p)) Refl≃′
insertion-parallel (Join S₁ S₂) (BShift P) (BShift Q) T p = Join≃′ Refl≃′ (insertion-parallel S₂ P Q T (proj-shift p))

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
  < standard-label (Susp S₁) (Susp T) (PExt Z) >>= ++t-inc-left (Susp T) S₂ >stm
    ≈⟨ >>=-≃ (standard-label-max (Susp S₁) (Susp T) (PExt Z)) refl≃l refl≃sty ⟩
  < standard-coh′ (tree-dim S₁) T >>= label₁ (++t-inc-left (Susp T) S₂) >stm
    ≈˘⟨ >>=-≃ (standard-coh′-≃ (lh-linear _ Q) (refl≃ {T = T}))
              [ (λ P → compute-≃ refl≃stm) ]
              (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
  < standard-coh′ (lh Q) T >>= map-ext (id-label-wt T) >stm
    ≈⟨ >>=-ext (standard-coh′ (lh Q) T) (id-label-wt T) ⟩
  < SExt (standard-coh′ (lh Q) T >>= id-label-wt T) >stm
    ≈˘⟨ SExt≃ (>>=-≃ (refl≃stm {a = standard-coh′ (lh Q) T})
                     (disc-ι S₁ Q T)
                     (S⋆-≃ (≃′-to-≃ (disc-insertion S₁ Q T)))) refl≃ ⟩
  < SExt (standard-coh′ (lh Q) T >>= (ι S₁ Q T ,, S⋆)) >stm
    ≈˘⟨ SExt≃ (κ-branch-path S₁ Q T) refl≃ ⟩
  < SExt (κ S₁ Q T ⌊ Q ⌋p) >stm
    ≈⟨ SExt≃ (ap-≃ (refl≃l {L = κ S₁ Q T})
                   (max-path-unique S₁ ⌊ Q ⌋p Z)) refl≃ ⟩
  < SExt (κ S₁ Q T Z) >stm ∎
  where
    open Reasoning stm-setoid
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

parallel-label-from : (L : Label X S)
                    → (P : Branch S l)
                    → (Q : Branch S l′)
                    → (M : Label X T)
                    → .⦃ _ : has-trunk-height (bh P) T ⦄
                    → .⦃ _ : has-trunk-height (bh Q) T ⦄
                    → (p : ⌊ P ⌋p ≃p ⌊ Q ⌋p)
                    → L >>l[ P ] M ≃lm label-≃ (insertion-parallel S P Q T p) (L >>l[ Q ] M)
parallel-label-from L BHere BHere M p = refl≃lm
parallel-label-from {T = Susp T} L BHere (BExt Q) M p .get (PExt Z)
  = sym≃stm (label-≃-sym (disc-insertion _ Q T) (disc-label-from (L ∘ PExt) Q (M ∘ PExt)) .get Z)
parallel-label-from {T = Susp T} L BHere (BExt Q) M p .get (PShift Z) = refl≃stm
parallel-label-from {T = Susp T} L (BExt P) BHere M p .get (PExt Z) = disc-label-from (L ∘ PExt) P (M ∘ PExt) .get Z
parallel-label-from {T = Susp T} L (BExt P) BHere M p .get (PShift Z) = refl≃stm
parallel-label-from {T = Susp T} L (BExt P) (BExt Q) M p .get (PExt Z) = parallel-label-from (L ∘ PExt) P Q (M ∘ PExt) (proj-ext p) .get Z
parallel-label-from {T = Susp T} L (BExt P) (BExt Q) M p .get (PShift Z) = refl≃stm
parallel-label-from L (BShift P) (BShift Q) M p .get (PExt Z) = refl≃stm
parallel-label-from L (BShift P) (BShift Q) M p .get (PShift Z) = parallel-label-from (L ∘ PShift) P Q M (proj-shift p) .get Z

label-from-insertion-≃ : {L : Label X S}
                       → {L′ : Label Y S}
                       → L ≃l L′
                       → (P : Branch S d)
                       → {M : Label X T}
                       → {M′ : Label Y T}
                       → M ≃l M′
                       → .⦃ lh : has-trunk-height d T ⦄
                       → L >>l[ P ] M ≃l L′ >>l[ P ] M′
label-from-insertion-≃ p BHere q = ++l-≃ q [ (λ P → p .get (PShift P)) ]
label-from-insertion-≃ {T = Susp T} p (BExt P) q .get PHere = q .get PHere
label-from-insertion-≃ {T = Susp T} p (BExt P) q .get (PExt Z) = label-from-insertion-≃ [ (λ Z → p .get (PExt Z)) ] P [ (λ Z → q .get (PExt Z)) ] .get Z
label-from-insertion-≃ {T = Susp T} p (BExt P) q .get (PShift Z) = replace-label-≃ [ (λ Z → p .get (PShift Z)) ] (q .get (PShift PHere)) .get Z
label-from-insertion-≃ p (BShift P) q .get PHere = p .get PHere
label-from-insertion-≃ p (BShift P) q .get (PExt Z) = p .get (PExt Z)
label-from-insertion-≃ p (BShift P) q .get (PShift Z) = label-from-insertion-≃ [ (λ Z → p .get (PShift Z)) ] P q .get Z

label-from-prune-≃ : {L : Label X S}
                   → {L′ : Label Y S}
                   → L ≃l L′
                   → (P : Branch S d)
                   → {M : Label X (n-disc (pred (lh P)))}
                   → {M′ : Label Y (n-disc (pred (lh P)))}
                   → M ≃l M′
                   → L >>p[ P ] M ≃l L′ >>p[ P ] M′
label-from-prune-≃ p P q = label-from-insertion-≃ p P q ⦃ prune-lem P ⦄

wedge-branch-left : (S : Tree n)
                    → (T : Tree m)
                    → (P : Branch S l)
                    → Branch (S ++t T) l
wedge-branch-left (Join S₁ S₂) T BHere = BHere
wedge-branch-left (Join S₁ S₂) T (BExt P) = BExt P
wedge-branch-left (Join S₁ S₂) T (BShift P) = BShift (wedge-branch-left S₂ T P)

wedge-branch-left-prop : (S : Tree n)
                         → (T : Tree m)
                         → (P : Branch S l)
                         → SPath (⌊ wedge-branch-left S T P ⌋p)
                           ≃stm ap (++t-inc-left S T) ⌊ P ⌋p
wedge-branch-left-prop (Join S₁ S₂) T BHere = refl≃stm
wedge-branch-left-prop (Join S₁ S₂) T (BExt P) = refl≃stm
wedge-branch-left-prop (Join S₁ S₂) T (BShift P) = compute-≃ (SShift≃ refl≃ (wedge-branch-left-prop S₂ T P))

wedge-branch-left-height : (S : Tree n)
                           → (T : Tree m)
                           → (P : Branch S l)
                           → lh (wedge-branch-left S T P) ≃n lh P
wedge-branch-left-height (Join S₁ S₂) T BHere = refl≃n
wedge-branch-left-height (Join S₁ S₂) T (BExt P) = refl≃n
wedge-branch-left-height (Join S₁ S₂) T (BShift P) = wedge-branch-left-height S₂ T P

insertion-branch-left : (S : Tree n)
                      → (T : Tree m)
                      → (P : Branch S l)
                      → (U : Tree n′)
                      → .⦃ _ : has-trunk-height l U ⦄
                      → S ++t T >>[ wedge-branch-left S T P ] U ≃′ (S >>[ P ] U) ++t T
insertion-branch-left (Join S₁ S₂) T BHere U = ++t-assoc U S₂ T
insertion-branch-left (Join S₁ S₂) T (BExt P) (Susp U) = refl≃′
insertion-branch-left (Join S₁ S₂) T (BShift P) U = Join≃′ refl≃′ (insertion-branch-left S₂ T P U)

κ-branch-left-inc-left : (S : Tree n)
                       → (T : Tree m)
                       → (P : Branch S l)
                       → (U : Tree n′)
                       → .⦃ _ : has-trunk-height l U ⦄
                       → ap (++t-inc-left S T) ●l (κ (S ++t T) (wedge-branch-left S T P) U ,, S⋆)
                         ≃l
                         κ S P U ●l (++t-inc-left (S >>[ P ] U) T)
κ-branch-left-inc-left (Join S₁ S₂) T BHere U .get PHere = SPath≃ (begin
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
κ-branch-left-inc-left (Join S₁ S₂) T BHere U .get (PExt Z) = begin
  < standard-label (Susp S₁) U (PExt Z) >>= ++t-inc-left U (S₂ ++t T) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = standard-label (Susp S₁) U (PExt Z)})
              [ (λ P → SPath≃ (++t-inc-left-assoc U S₂ T .get P)) ]
              (S⋆-≃ (≃′-to-≃ (sym≃′ (++t-assoc U S₂ T)))) ⟩
  < standard-label (Susp S₁) U (PExt Z)
    >>= ++t-inc-left U S₂ ●lt ++t-inc-left (U ++t S₂) T >stm
    ≈˘⟨ >>=-assoc (standard-label (Susp S₁) U (PExt Z)) _ _ ⟩
  < standard-label (Susp S₁) U (PExt Z)
    >>= ++t-inc-left U S₂
    >>= ++t-inc-left (U ++t S₂) T >stm ∎
  where
    open Reasoning stm-setoid
κ-branch-left-inc-left (Join S₁ S₂) T BHere U .get (PShift Z) = SPath≃ (++t-inc-assoc U S₂ T .get Z)
κ-branch-left-inc-left (Join S₁ S₂) T (BExt P) (Susp U) .get PHere = refl≃stm
κ-branch-left-inc-left (Join S₁ S₂) T (BExt P) (Susp U) .get (PExt Z) = begin
  < SExt (κ S₁ P U Z) >stm
    ≈˘⟨ SExt≃ (>>=-id (κ S₁ P U Z)) refl≃ ⟩
  < SExt (κ S₁ P U Z >>= id-label-wt (S₁ >>[ P ] U)) >stm
    ≈˘⟨ >>=-ext (κ S₁ P U Z) (id-label-wt (S₁ >>[ P ] U)) ⟩
  < κ S₁ P U Z >>= map-ext {T = S₂ ++t T} (id-label-wt (S₁ >>[ P ] U)) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = κ S₁ P U Z}) [ (λ Z → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ (SShift≃ refl≃ (SPath≃ (++t-inc-left-phere S₂ T))))) ⟩
  < κ S₁ P U Z >>= (SPath ∘ PExt ,, SArr (SPath PHere) S⋆ (SPath (PShift (++t-inc-left′ S₂ T PHere)))) >stm ∎
  where
    open Reasoning stm-setoid
κ-branch-left-inc-left (Join S₁ S₂) T (BExt P) (Susp U) .get (PShift Z) = compute-≃ refl≃stm
κ-branch-left-inc-left (Join S₁ S₂) T (BShift P) U .get PHere = SPath≃ (Here≃ (≃′-to-≃ (insertion-branch-left (Join S₁ S₂) T (BShift P) U)))
κ-branch-left-inc-left (Join S₁ S₂) T (BShift P) U .get (PExt Z) = compute-≃ (SExt≃ refl≃stm (≃′-to-≃ (insertion-branch-left S₂ T P U)))
κ-branch-left-inc-left (Join S₁ S₂) T (BShift P) U .get (PShift Z) = begin
  < SShift (κ (S₂ ++t T) (wedge-branch-left S₂ T P) U ⦃ _ ⦄ (++t-inc-left′ S₂ T Z)) >stm
    ≈⟨ SShift≃ refl≃ (κ-branch-left-inc-left S₂ T P U .get Z) ⟩
  < SShift (κ S₂ P U Z >>= ++t-inc-left (S₂ >>[ P ] U) T) >stm
    ≈˘⟨ >>=-shift (κ S₂ P U Z) (++t-inc-left (S₂ >>[ P ] U) T) ⟩
  < κ S₂ P U Z >>= map-shift {S = S₁} (++t-inc-left (S₂ >>[ P ] U) T) >stm
    ≈⟨ >>=-≃ (refl≃stm {a = κ S₂ P U Z}) [ (λ Z → compute-≃ refl≃stm) ] refl≃sty ⟩
  < κ S₂ P U Z >>= label₂ (++t-inc-left (Join S₁ (S₂ >>[ P ] U)) T) >stm ∎
  where open Reasoning stm-setoid

κ-branch-left-inc-right : (S : Tree n)
                        → (T : Tree m)
                        → (P : Branch S l)
                        → (U : Tree n′)
                        → .⦃ _ : has-trunk-height l U ⦄
                        → ap (++t-inc-right S T)
                          ●l (κ (S ++t T) (wedge-branch-left S T P) U ,, S⋆)
                          ≃l
                          ap (++t-inc-right (S >>[ P ] U) T)
κ-branch-left-inc-right (Join S₁ S₂) T BHere U .get Z = SPath≃ (++t-inc-right-assoc U S₂ T .get Z)
κ-branch-left-inc-right (Join S₁ S₂) T (BExt P) (Susp U) .get Z = compute-≃ refl≃stm
κ-branch-left-inc-right (Join S₁ S₂) T (BShift P) U .get Z = compute-≃ (SShift≃ refl≃ (κ-branch-left-inc-right S₂ T P U .get Z))

label-from-branch-left : (L : Label X S)
                       → (M : Label X T)
                       → (P : Branch S l)
                       → {U : Tree n}
                       → (N : Label X U)
                       → .⦃ _ : has-trunk-height l U ⦄
                       → L ++l M >>l[ wedge-branch-left S T P ] N
                         ≃lm
                         label-≃ (insertion-branch-left S T P U) ((L >>l[ P ] N) ++l M)
label-from-branch-left L M BHere N .get Z = ++l-assoc N (L ∘ PShift) M .get Z
label-from-branch-left L M (BExt P) {Susp U} N .get (PExt Z) = refl≃stm
label-from-branch-left L M (BExt P) {Susp U} N .get (PShift Z) = replace-++l (L ∘ PShift) M (N (PShift PHere)) .get Z
label-from-branch-left L M (BShift P) N .get (PExt Z) = refl≃stm
label-from-branch-left L M (BShift P) N .get (PShift Z) = label-from-branch-left (L ∘ PShift) M P N .get Z

wedge-branch-right : (S : Tree n)
                     → (T : Tree m)
                     → (P : Branch T l)
                     → Branch (S ++t T) l
wedge-branch-right Sing T P = P
wedge-branch-right (Join S₁ S₂) T P = BShift (wedge-branch-right S₂ T P)

wedge-branch-right-prop : (S : Tree n)
                          → (T : Tree m)
                          → (P : Branch T l)
                          → SPath ⌊ wedge-branch-right S T P ⌋p
                            ≃stm
                            ap (++t-inc-right S T) ⌊ P ⌋p
wedge-branch-right-prop Sing T P = refl≃stm
wedge-branch-right-prop (Join S₁ S₂) T P = compute-≃ (SShift≃ refl≃ (wedge-branch-right-prop S₂ T P))

wedge-branch-right-height : (S : Tree n)
                            → (T : Tree m)
                            → (P : Branch T l)
                            → lh (wedge-branch-right S T P) ≃n lh P
wedge-branch-right-height Sing T P = refl≃n
wedge-branch-right-height (Join S₁ S₂) T P = wedge-branch-right-height S₂ T P

insertion-branch-right : (S : Tree n)
                       → (T : Tree m)
                       → (P : Branch T l)
                       → (U : Tree n′)
                       → .⦃ _ : has-trunk-height l U ⦄
                       → S ++t T >>[ wedge-branch-right S T P ] U ≃′ S ++t (T >>[ P ] U)
insertion-branch-right Sing T P U = refl≃′
insertion-branch-right (Join S₁ S₂) T P U = Join≃′ refl≃′ (insertion-branch-right S₂ T P U)

κ-branch-right-inc-left : (S : Tree n)
                        → (T : Tree m)
                        → (P : Branch T l)
                        → (U : Tree n′)
                        → .⦃ _ : has-trunk-height l U ⦄
                        → ap (++t-inc-left S T) ●l (κ (S ++t T) (wedge-branch-right S T P) U ,, S⋆)
                          ≃l
                          ap (++t-inc-left S (T >>[ P ] U))
κ-branch-right-inc-left Sing T P U .get PHere = κ-phere T P U ⦃ it ⦄
κ-branch-right-inc-left (Join S₁ S₂) T P U .get PHere = SPath≃ (Here≃ (≃′-to-≃ (insertion-branch-right (Join S₁ S₂) T P U)))
κ-branch-right-inc-left (Join S₁ S₂) T P U .get (PExt Z) = compute-≃ (SExt≃ refl≃stm (≃′-to-≃ (insertion-branch-right S₂ T P U)))
κ-branch-right-inc-left (Join S₁ S₂) T P U .get (PShift Z) = compute-≃ (SShift≃ refl≃ (κ-branch-right-inc-left S₂ T P U .get Z))

κ-branch-right-inc-right : (S : Tree n)
                         → (T : Tree m)
                         → (P : Branch T l)
                         → (U : Tree n′)
                         → .⦃ _ : has-trunk-height l U ⦄
                         → ap (++t-inc-right S T) ●l (κ (S ++t T) (wedge-branch-right S T P) U ,, S⋆)
                           ≃l
                           κ T P U ●l (++t-inc-right S (T >>[ P ] U))
κ-branch-right-inc-right Sing T P U = sym≃l (comp-right-unit (κ T P U))
κ-branch-right-inc-right (Join S₁ S₂) T P U = begin
  < SShift ∘ (ap (++t-inc-right S₂ T) ●l (κ (S₂ ++t T) (wedge-branch-right S₂ T P) U  ,, S⋆)) >l
    ≈⟨ [ (λ Z → SShift≃ refl≃ (κ-branch-right-inc-right S₂ T P U .get Z)) ] ⟩
  < SShift ∘ κ T P U ●l ++t-inc-right S₂ (T >>[ P ] U) >l
    ≈˘⟨ comp-shift (κ T P U) (++t-inc-right S₂ (T >>[ P ] U)) ⟩
  < κ T P U ●l map-shift {S = S₁} (++t-inc-right S₂ (T >>[ P ] U)) >l
    ≈⟨ label-comp-≃ (refl≃l {L = κ T P U}) [ (λ Z → compute-≃ refl≃stm) ] refl≃sty ⟩
  < κ T P U ●l ++t-inc-right (Join S₁ S₂) (T >>[ P ] U) >l  ∎
  where
    open Reasoning (label-setoid T)

label-from-branch-right : (L : Label X S)
                        → (M : Label X T)
                        → (P : Branch T l)
                        → (N : Label X U)
                        → .⦃ _ : has-trunk-height l U ⦄
                        → L ++l′ M >>l′[ wedge-branch-right S T P ] N
                          ≃lm
                          label-≃ (insertion-branch-right S T P U) (L ++l′ (M >>l′[ P ] N))
label-from-branch-right {S = Sing} L M P N .get Z = refl≃stm
label-from-branch-right {S = Join S₁ S₂} L M P N .get (PExt Z) = refl≃stm
label-from-branch-right {S = Join S₁ S₂} L M P N .get (PShift Z) = label-from-branch-right (L ∘ PShift) M P N .get Z

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

Orthogonal→≢ : (P : Branch S l) → (Q : Branch S l′) → ⦃ Orthogonal P Q ⦄ → ¬ ⌊ P ⌋p ≃p ⌊ Q ⌋p
Orthogonal→≢ BHere BHere p = it
Orthogonal→≢ BHere (BExt Q) p = it
Orthogonal→≢ BHere (BShift Q) ()
Orthogonal→≢ (BExt P) (BExt Q) (Ext≃ p x) = Orthogonal→≢ P Q p
Orthogonal→≢ (BShift P) (BShift Q) (Shift≃ x p) = Orthogonal→≢ P Q p

orthog-branch : (P : Branch S l)
              → (Q : Branch S l′)
              → .⦃ Orthogonal P Q ⦄
              → (T : Tree m)
              → .⦃ _ : has-trunk-height (bh P) T ⦄
              → Branch (S >>[ P ] T) l′
orthog-branch BHere (BShift Q) T = wedge-branch-right T _ Q
orthog-branch (BExt P) (BExt Q) (Susp T) = BExt (orthog-branch P Q T)
orthog-branch (BExt P) (BShift Q) (Susp T) = BShift Q
orthog-branch (BShift P) BHere T = BHere
orthog-branch (BShift P) (BExt Q) T = BExt Q
orthog-branch (BShift P) (BShift Q) T = BShift (orthog-branch P Q T)

orthog-branch-prop : (S : Tree n)
                   → (P : Branch S l)
                   → (Q : Branch S l′)
                   → .⦃ _ : Orthogonal P Q ⦄
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height (bh P) T ⦄
                   → SPath ⌊ orthog-branch P Q T ⌋p
                     ≃stm
                     κ S P T ⌊ Q ⌋p
orthog-branch-prop (Join S₁ S₂) BHere (BShift Q) T = wedge-branch-right-prop T S₂ Q
orthog-branch-prop (Join S₁ S₂) (BExt P) (BExt Q) (Susp T) = compute-≃ (SExt≃ (orthog-branch-prop S₁ P Q T) refl≃)
orthog-branch-prop (Join S₁ S₂) (BExt P) (BShift Q) (Susp T) = compute-≃ refl≃stm
orthog-branch-prop (Join S₁ S₂) (BShift P) BHere T = compute-≃ refl≃stm
orthog-branch-prop (Join S₁ S₂) (BShift P) (BExt Q) T = compute-≃ refl≃stm
orthog-branch-prop (Join S₁ S₂) (BShift P) (BShift Q) T = compute-≃ (SShift≃ refl≃ (orthog-branch-prop S₂ P Q T))

orthog-lh : (P : Branch S l)
          → (Q : Branch S l′)
          → .⦃ _ : Orthogonal P Q ⦄
          → (T : Tree m)
          → .⦃ _ : has-trunk-height (bh P) T ⦄
          → lh (orthog-branch P Q T) ≃n lh Q
orthog-lh BHere (BShift Q) T = wedge-branch-right-height T _ Q
orthog-lh (BExt P) (BExt Q) (Susp T) = inst ⦃ orthog-lh P Q T ⦄
orthog-lh (BExt P) (BShift Q) (Susp T) = refl≃n
orthog-lh (BShift P) BHere T = refl≃n
orthog-lh (BShift P) (BExt Q) T = refl≃n
orthog-lh (BShift P) (BShift Q) T = orthog-lh P Q T

insertion-orthog : (S : Tree n)
                 → (P : Branch S l)
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height (bh P) T ⦄
                 → (Q : Branch S l′)
                 → .⦃ _ : Orthogonal P Q ⦄
                 → (U : Tree m′)
                 → .⦃ _ : has-trunk-height (bh Q) U ⦄
                 → (S >>[ P ] T) >>[ orthog-branch P Q T ] U ≃′ (S >>[ Q ] U) >>[ orthog-branch Q P ⦃ Orthogonal-sym P Q ⦄ U ] T
insertion-orthog (Join S₁ S₂) BHere T (BShift Q) U = insertion-branch-right T S₂ Q U
insertion-orthog (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) = Join≃′ (insertion-orthog S₁ P T Q U) Refl≃′
insertion-orthog (Join S₁ S₂) (BExt P) (Susp T) (BShift Q) U = Refl≃′
insertion-orthog (Join S₁ S₂) (BShift P) T BHere U = sym≃′ (insertion-branch-right U S₂ P T)
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
           → κ S P T ●l (κ (S >>[ P ] T) (orthog-branch P Q T) U ,, S⋆)
             ≃lm
             κ S Q U ●l (κ (S >>[ Q ] U) (orthog-branch Q P ⦃ Orthogonal-sym P Q ⦄ U) T ,, S⋆)
  κ-orthog (Join S₁ S₂) BHere T (BShift Q) U .get (PExt Z) = begin
    < standard-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂
      >>= (κ (T ++t S₂) (wedge-branch-right T S₂ Q) U ,, S⋆) >stm
      ≈⟨ >>=-assoc (standard-label (Susp S₁) T (PExt Z)) (++t-inc-left T S₂) _ ⟩
    < standard-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂ ●lt (κ (T ++t S₂) (wedge-branch-right T S₂ Q) U ,, S⋆) >stm
      ≈⟨ >>=-≃ (refl≃stm {a = standard-label (Susp S₁) T (PExt Z)}) (κ-branch-right-inc-left T S₂ Q U) (S⋆-≃ (≃′-to-≃ (insertion-branch-right T S₂ Q U))) ⟩
    < standard-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T (S₂ >>[ Q ] U) >stm ∎
  κ-orthog (Join S₁ S₂) BHere T (BShift Q) U .get (PShift Z) = κ-branch-right-inc-right T S₂ Q U .get Z
  κ-orthog (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) .get (PExt Z) = let
    instance _ = Orthogonal-sym P Q
    in begin
    < κ S₁ P T Z >>= map-ext (κ (S₁ >>[ P ] T) (orthog-branch P Q T) U ,, S⋆) >stm
      ≈⟨ >>=-ext (κ S₁ P T Z) (κ (S₁ >>[ P ] T) (orthog-branch P Q T) U ,, S⋆) ⟩
    < SExt (κ S₁ P T Z >>= (κ (S₁ >>[ P ] T) (orthog-branch P Q T) U ,, S⋆)) >stm
      ≈⟨ SExt≃ (κ-orthog S₁ P T Q U .get Z) refl≃ ⟩
    < SExt (κ S₁ Q U Z >>= (κ (S₁ >>[ Q ] U) (orthog-branch Q P U) T ,, S⋆)) >stm
      ≈˘⟨ >>=-ext (κ S₁ Q U Z) (κ (S₁ >>[ Q ] U) (orthog-branch Q P U) T ,, S⋆) ⟩
    < κ S₁ Q U Z >>= map-ext (κ (S₁ >>[ Q ] U) (orthog-branch Q P U) T ,, S⋆) >stm ∎
  κ-orthog (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) .get (PShift Z) = SShift≃ (≃′-to-≃ (insertion-orthog S₁ P T Q U)) refl≃stm
  κ-orthog (Join S₁ S₂) (BExt P) (Susp T) (BShift Q) U .get (PExt Z) = begin
    < κ S₁ P T Z >>= ((SExt ∘ SPath) ,, SArr (SPath PHere) S⋆ (SShift (κ S₂ Q U PHere))) >stm
      ≈⟨ >>=-≃ (refl≃stm {a = κ S₁ P T Z}) refl≃l (SArr≃ refl≃stm refl≃sty (SShift≃ refl≃ (κ-phere S₂ Q U))) ⟩
    < κ S₁ P T Z >>= map-ext (id-label-wt (S₁ >>[ P ] T)) >stm
      ≈⟨ >>=-ext (κ S₁ P T Z) (id-label-wt (S₁ >>[ P ] T)) ⟩
    < SExt (κ S₁ P T Z >>= id-label-wt (S₁ >>[ P ] T)) >stm
      ≈⟨ SExt≃ (>>=-id (κ S₁ P T Z)) refl≃ ⟩
    < SExt (κ S₁ P T Z) >stm ∎
  κ-orthog (Join S₁ S₂) (BExt P) (Susp T) (BShift Q) U .get (PShift Z) = begin
    < SShift (κ S₂ Q U Z) >stm
      ≈˘⟨ SShift≃ refl≃ (>>=-id (κ S₂ Q U Z)) ⟩
    < SShift (κ S₂ Q U Z >>= id-label-wt (S₂ >>[ Q ] U)) >stm
      ≈˘⟨ >>=-shift (κ S₂ Q U Z) (id-label-wt (S₂ >>[ Q ] U)) ⟩
    < κ S₂ Q U Z >>= map-shift (id-label-wt (S₂ >>[ Q ] U)) >stm ∎
  κ-orthog (Join S₁ S₂) (BShift P) T BHere U .get (PExt Z) = sym≃stm (κ-orthog (Join S₁ S₂) BHere U (BShift P) T .get (PExt Z))
  κ-orthog (Join S₁ S₂) (BShift P) T BHere U .get (PShift Z) = sym≃stm (κ-orthog (Join S₁ S₂) BHere U (BShift P) T .get (PShift Z))
  κ-orthog (Join S₁ S₂) (BShift P) T (BExt Q) (Susp U) .get (PExt Z) = begin
    < SExt (κ S₁ Q U Z) >stm
      ≈˘⟨ SExt≃ (>>=-id (κ S₁ Q U Z)) refl≃ ⟩
    < SExt (κ S₁ Q U Z >>= id-label-wt (S₁ >>[ Q ] U)) >stm
      ≈˘⟨ >>=-ext (κ S₁ Q U Z) (id-label-wt (S₁ >>[ Q ] U)) ⟩
    < κ S₁ Q U Z >>= map-ext (id-label-wt (S₁ >>[ Q ] U)) >stm
      ≈˘⟨ >>=-≃ (refl≃stm {a = κ S₁ Q U Z}) refl≃l (SArr≃ refl≃stm refl≃sty (SShift≃ refl≃ (κ-phere S₂ P T))) ⟩
    < κ S₁ Q U Z >>= (SExt ∘ SPath ,, SArr (SPath PHere) S⋆ (SShift (κ S₂ P T PHere))) >stm ∎
  κ-orthog (Join S₁ S₂) (BShift P) T (BExt Q) (Susp U) .get (PShift Z) = begin
    < κ S₂ P T Z >>= map-shift (id-label-wt (S₂ >>[ P ] T)) >stm
      ≈⟨ >>=-shift (κ S₂ P T Z) (id-label-wt (S₂ >>[ P ] T)) ⟩
    < SShift (κ S₂ P T Z >>= id-label-wt (S₂ >>[ P ] T)) >stm
      ≈⟨ SShift≃ refl≃ (>>=-id (κ S₂ P T Z)) ⟩
    < SShift (κ S₂ P T Z) >stm ∎
  κ-orthog (Join S₁ S₂) (BShift P) T (BShift Q) U .get (PExt Z) = SExt≃ refl≃stm (≃′-to-≃ (insertion-orthog S₂ P T Q U))
  κ-orthog (Join S₁ S₂) (BShift P) T (BShift Q) U .get (PShift Z) = let
    instance _ = Orthogonal-sym P Q
    in begin
    < κ S₂ P T Z >>= map-shift (κ (S₂ >>[ P ] T) (orthog-branch P Q T) U ,, S⋆) >stm
      ≈⟨ >>=-shift (κ S₂ P T Z) (κ (S₂ >>[ P ] T) (orthog-branch P Q T) U ,, S⋆) ⟩
    < SShift (κ S₂ P T Z >>= (κ (S₂ >>[ P ] T) (orthog-branch P Q T) U ,, S⋆)) >stm
      ≈⟨ SShift≃ refl≃ (κ-orthog S₂ P T Q U .get Z) ⟩
    < SShift (κ S₂ Q U Z >>= (κ (S₂ >>[ Q ] U) (orthog-branch Q P U) T ,, S⋆)) >stm
      ≈˘⟨ >>=-shift (κ S₂ Q U Z) (κ (S₂ >>[ Q ] U) (orthog-branch Q P U) T ,, S⋆) ⟩
    < κ S₂ Q U Z >>= map-shift (κ (S₂ >>[ Q ] U) (orthog-branch Q P U) T ,, S⋆) >stm ∎

  label-from-insertion′-replace : (L : Label X S)
                                → (P : Branch S l)
                                → (M : Label X T)
                                → .⦃ _ : has-trunk-height l T ⦄
                                → (a : STm X)
                                → replace-label L a >>l′[ P ] M ≃l replace-label (L >>l′[ P ] M) a
  label-from-insertion′-replace L BHere M a = sym≃l (replace-replace (M ++l′ (L ∘ PShift)) (L PHere) a)
  label-from-insertion′-replace {T = Susp T} L (BExt P) M a .get PHere = refl≃stm
  label-from-insertion′-replace {T = Susp T} L (BExt P) M a .get (PExt Z) = refl≃stm
  label-from-insertion′-replace {T = Susp T} L (BExt P) M a .get (PShift Z) = refl≃stm
  label-from-insertion′-replace L (BShift P) M a .get PHere = refl≃stm
  label-from-insertion′-replace L (BShift P) M a .get (PExt Z) = refl≃stm
  label-from-insertion′-replace L (BShift P) M a .get (PShift Z) = refl≃stm

  label-from-orthog-lem : {S₁ : Tree n}
                        → {S₂ : Tree m}
                        → (L : Label X (Join S₁ S₂))
                        → (M : Label X T)
                        → (Q : Branch S₂ l′)
                        → (N : Label X U)
                        → .⦃ _ : has-trunk-height (bh Q) U ⦄
                        → replace-label (M ++l′ L ∘ PShift) (L PHere) >>l′[ wedge-branch-right T S₂ Q ] N
                          ≃lm
                          label-≃ (insertion-branch-right T S₂ Q U) (replace-label (M ++l′ (L ∘ PShift >>l′[ Q ] N)) (L PHere))
  label-from-orthog-lem {T = Sing} L M Q N .get Z = label-from-insertion′-replace (L ∘ PShift) Q N (L PHere) .get Z
  label-from-orthog-lem {T = Join T₁ T₂} L M Q N .get (PExt Z) = refl≃stm
  label-from-orthog-lem {T = Join T₁ T₂} L M Q N .get (PShift Z) = label-from-branch-right (M ∘ PShift) (L ∘ PShift) Q N .get Z

  label-from-orthog : (L : Label X S)
                    → (P : Branch S l)
                    → {T : Tree n}
                    → (M : Label X T)
                    → .⦃ _ : has-trunk-height (bh P) T ⦄
                    → (Q : Branch S l′)
                    → {U : Tree m}
                    → .⦃ _ : Orthogonal P Q ⦄
                    → (N : Label X U)
                    → .⦃ _ : has-trunk-height (bh Q) U ⦄
                    → (L >>l′[ P ] M) >>l′[ orthog-branch P Q T ] N
                      ≃lm
                      label-≃ (insertion-orthog S P T Q U) ((L >>l′[ Q ] N) >>l′[ orthog-branch Q P ⦃ Orthogonal-sym P Q ⦄ U ] M)
  label-from-orthog L BHere M (BShift Q) N = label-from-orthog-lem L M Q N
  label-from-orthog L (BExt P) {T = Susp T} M (BExt Q) {U = Susp U} N .get (PExt Z)
    = label-from-orthog (L ∘ PExt) P (M ∘ PExt) Q (N ∘ PExt) .get Z
  label-from-orthog L (BExt P) {T = Susp T} M (BExt Q) {U = Susp U} N .get (PShift Z) = refl≃stm
  label-from-orthog L (BExt P) {T = Susp T} M (BShift Q) N .get (PExt Z) = refl≃stm
  label-from-orthog L (BExt P) {T = Susp T} M (BShift Q) N .get (PShift Z) = refl≃stm
  label-from-orthog L (BShift P) M BHere N
    = sym≃lm (label-≃-sym-max (insertion-branch-right _ _ P _) (label-from-orthog-lem L N P M))
  label-from-orthog L (BShift P) M (BExt Q) {U = Susp U} N .get (PExt Z) = refl≃stm
  label-from-orthog L (BShift P) M (BExt Q) {U = Susp U} N .get (PShift Z) = refl≃stm
  label-from-orthog L (BShift P) M (BShift Q) N .get (PExt Z) = refl≃stm
  label-from-orthog L (BShift P) M (BShift Q) N .get (PShift Z) = label-from-orthog (L ∘ PShift) P M Q N .get Z

insertion-bd-1 : (S : Tree n)
               → (P : Branch S l)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height (bh P) T ⦄
               → (d : ℕ)
               → .(d ≤ trunk-height T)
               → .(lh P ≥ tree-dim T)
               → tree-bd d S ≃′ tree-bd d (S >>[ P ] T)
insertion-bd-1 (Join S₁ S₂) P T zero q r = refl≃′
insertion-bd-1 (Join S₁ S₂) BHere (Susp T) (suc d) q r = let
  .lem : d ≤ tree-dim S₁
  lem = ≤-pred (≤-trans q (≤-trans (s≤s (trunk-height-dim T)) r))
  in Join≃′ (linear-tree-unique (tree-bd d S₁)
                              ⦃ bd-trunk-height d S₁ (≤-trans lem (≤-reflexive (sym (linear-trunk-height S₁)))) ⦄
                              (tree-bd d T)
                              ⦃ bd-trunk-height d T (≤-pred q) ⦄
                              (trans (tree-dim-bd′ d S₁ lem) (sym (tree-dim-bd′ d T (≤-trans (≤-pred q) (trunk-height-dim T))))))
          refl≃′
insertion-bd-1 (Join S₁ S₂) (BExt P) (Susp T) (suc d) q r = Join≃′ (insertion-bd-1 S₁ P T d (≤-pred q) (≤-pred r)) refl≃′
insertion-bd-1 (Join S₁ S₂) (BShift P) T (suc d) q r = Join≃′ refl≃′ (insertion-bd-1 S₂ P T (suc d) q r)

bd-κ-comm-1 : (S : Tree n)
                   → (P : Branch S l)
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height (bh P) T ⦄
                   → (d : ℕ)
                   → (d < lh P)
                   → (q : d ≤ trunk-height T)
                   → (r : lh P ≥ tree-dim T)
                   → (b : Bool)
                   → ap (tree-inc-label d S b) ●l (κ S P T ,, S⋆)
                     ≃lm
                     label-≃ (insertion-bd-1 S P T d q r) (ap (tree-inc-label d (S >>[ P ] T) b))
bd-κ-comm-1 S P T zero p q r false .get Z = κ-phere S P T
bd-κ-comm-1 S P T zero p q r true .get Z = κ-last-path S P T
bd-κ-comm-1 (Join S₁ S₂) (BHere ⦃ l ⦄) (Susp T) (suc d) P q r b .get (PExt Z) = begin
  < standard-label (Susp S₁) (Susp T) (PExt (tree-inc-label′ d S₁ b Z))
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
        ≈⟨ max-path-lin-tree (tree-bd d T) Z
             (≃′-to-≃ (sym≃′ (linear-tree-unique (tree-bd d S₁)
                                                 (tree-bd d T)
                                                 (trans (tree-dim-bd′ d S₁ (≤-pred (≤-pred (m≤n⇒m≤1+n P))))
                                                        (sym (tree-dim-bd′ d T (≤-trans (≤-pred q) (trunk-height-dim T)))))))) ⟩
      < Z >p
        ≈⟨ ppath-≃-≃p (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z ⟩
      < ppath-≃ (linear-tree-unique (tree-bd d S₁) (tree-bd d T) _) Z >p ∎
      where
        open Reasoning path-setoid
    open Reasoning stm-setoid

    lem2 : standard-label (Susp S₁) (Susp T) (PExt (tree-inc-label′ d S₁ b Z))
           ≃stm
           SPath (PExt (tree-inc-label′ d T b (is-linear-max-path (tree-bd d T))))
    lem2 = begin
      < standard-label (Susp S₁) (Susp T) (PExt (tree-inc-label′ d S₁ b Z)) >stm
        ≈⟨ standard-label-bd-< (Susp S₁) (Susp T) (suc d) b P (PExt Z) ⟩
      < standard-stm (suc d) (tree-bd (suc d) (Susp T)) >>= tree-inc-label (suc d) (Susp T) b >stm
        ≈⟨ >>=-≃ (standard-stm-linear (suc d)
                                       (tree-bd (suc d) (Susp T))
                                       (cong suc (sym (tree-dim-bd′ d T (≤-trans (≤-pred q) (trunk-height-dim T))))))
                 (refl≃l {L = ap (tree-inc-label (suc d) (Susp T) b)}) refl≃sty ⟩
      < SPath (is-linear-max-path (tree-bd (suc d) (Susp T))) >>= (tree-inc-label (suc d) (Susp T) b) >stm
        ≡⟨⟩
      < SPath (PExt (tree-inc-label′ d T b (is-linear-max-path (tree-bd d T)))) >stm ∎
bd-κ-comm-1 (Join S₁ S₂) BHere (Susp T) (suc d) p q r b .get (PShift Z) = refl≃stm
bd-κ-comm-1 (Join S₁ S₂) (BExt P) (Susp T) (suc d) p q r b .get (PExt Z)
  = compute-≃ (SExt≃ (bd-κ-comm-1 S₁ P T d (≤-pred p) (≤-pred q) (≤-pred r) b .get Z) refl≃)
bd-κ-comm-1 (Join S₁ S₂) (BExt P) (Susp T) (suc d) p q r b .get (PShift Z)
  = compute-≃ refl≃stm
bd-κ-comm-1 (Join S₁ S₂) (BShift P) T (suc d) p q r b .get (PExt Z)
  = compute-≃ refl≃stm
bd-κ-comm-1 (Join S₁ S₂) (BShift P) T (suc d) p q r b .get (PShift Z)
  = compute-≃ (SShift≃ refl≃ (bd-κ-comm-1 S₂ P T (suc d) p q r b .get Z))

data Condition (d : ℕ) (T : Tree n) (m : ℕ) : Set where
  Cond1 : d > (trunk-height T) → d ≤ m → Condition d T m
  Cond2 : d ≥ m → Condition d T m

cond-pred : Condition (suc d) (Susp T) (suc m) → Condition d T m
cond-pred (Cond1 x y) = Cond1 (≤-pred x) (≤-pred y)
cond-pred (Cond2 x) = Cond2 (≤-pred x)

bd-branch-lem : (P : Branch S l)
              → {T : Tree n}
              → .⦃ has-trunk-height (bh P) T ⦄
              → Condition d T (lh P)
              → d > bh P
bd-branch-lem P {T} (Cond1 x y) = ≤-<-trans (has-trunk-height-prop (bh P) T) x
bd-branch-lem P (Cond2 q) = <-≤-trans (bh-<-lh P) q

bd-branch : (S : Tree n)
          → (P : Branch S l)
          → (d : ℕ)
          → .(q : d > bh P)
          → Branch (tree-bd d S) l
bd-branch (Join S₁ S₂) BHere (suc d) q = BHere ⦃ is-linear-bd d S₁ ⦄
bd-branch (Join S₁ S₂) (BExt P) (suc d) q = BExt (bd-branch S₁ P d (≤-pred q))
bd-branch (Join S₁ S₂) (BShift P) (suc d) q = BShift (bd-branch S₂ P (suc d) q)

bd-branch-height : (S : Tree n)
                 → (P : Branch S l)
                 → (d : ℕ)
                 → .(q : d > bh P)
                 → lh (bd-branch S P d q) ≡ d ⊓ lh P
bd-branch-height (Join S₁ S₂) BHere (suc d) q = cong suc (tree-dim-bd d S₁)
bd-branch-height (Join S₁ S₂) (BExt P) (suc d) q = cong suc (bd-branch-height S₁ P d (≤-pred q))
bd-branch-height (Join S₁ S₂) (BShift P) (suc d) q = bd-branch-height S₂ P (suc d) q

bd-branch-lh : (S : Tree n)
             → (P : Branch S l)
             → (d : ℕ)
             → (q : d > bh P)
             → (T : Tree m)
             → (p : lh P ≥ tree-dim T)
             → tree-dim (tree-bd d T)
               ≤
               lh (bd-branch S P d q)
bd-branch-lh S P d q T p = begin
  tree-dim (tree-bd d T)
    ≡⟨ tree-dim-bd d T ⟩
  d ⊓ tree-dim T
    ≤⟨ ⊓-monoʳ-≤ d p ⟩
  d ⊓ lh P
    ≡˘⟨ bd-branch-height S P d q ⟩
  lh (bd-branch S P d q) ∎
    where
      open ≤-Reasoning

bd-has-trunk-height : (d : ℕ) → (m : ℕ)
                    → (T : Tree n) → .⦃ has-trunk-height m T ⦄
                    → .(d > m)
                    → has-trunk-height m (tree-bd d T)
bd-has-trunk-height d zero T q = tt
bd-has-trunk-height (suc d) (suc m) (Susp T) q = inst ⦃ bd-has-trunk-height d m T (≤-pred q) ⦄

insertion-bd-2 : (S : Tree n)
               → (P : Branch S l)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height (bh P) T ⦄
               → (d : ℕ)
               → .(q : d > bh P)
               → (tree-bd d S >>[ bd-branch S P d q ] tree-bd d T) ⦃ bd-has-trunk-height d l T q ⦄
                 ≃′
                 tree-bd d (S >>[ P ] T)
insertion-bd-2 (Join S₁ S₂) BHere T (suc d) q = ++t-bd d T S₂
insertion-bd-2 (Join S₁ S₂) (BExt P) (Susp T) (suc d) q
  = Join≃′ (insertion-bd-2 S₁ P T d (≤-pred q)) refl≃′
insertion-bd-2 (Join S₁ S₂) (BShift P) T (suc d) q
  = Join≃′ refl≃′ (insertion-bd-2 S₂ P T (suc d) q)

module _ where
  open Reasoning stm-setoid

  bd-κ-comm-2 : (S : Tree n)
                     → (P : Branch S l)
                     → (T : Tree m)
                     → .⦃ _ : has-trunk-height (bh P) T ⦄
                     → (d : ℕ)
                     → (b : Bool)
                     → lh P ≥ tree-dim T
                     → (c : Condition d T (lh P))
                     → ap (tree-inc-label d S b) ●l (κ S P T ,, S⋆)
                       ≃lm
                       κ (tree-bd d S)
                         (bd-branch S P d (bd-branch-lem P c))
                         (tree-bd d T)
                         ⦃ bd-has-trunk-height d l T (bd-branch-lem P c) ⦄
                         ●l (label-wt-≃ (insertion-bd-2 S P T d (bd-branch-lem P c)) (tree-inc-label d (S >>[ P ] T) b))
  bd-κ-comm-2 S P T zero b r (Cond1 () x)
  bd-κ-comm-2 S P T zero b r (Cond2 ())
  bd-κ-comm-2 (Join S₁ S₂) BHere T (suc d) b r c .get (PShift Z)
    = SPath≃ (tree-inc-inc-right d T S₂ b Z)
  bd-κ-comm-2 (Join S₁ S₂) BHere T (suc d) b r (Cond1 q r′) .get (PExt Z) = let
    instance _ = is-linear-bd d S₁
    in begin
    < standard-label (Susp S₁) T (PExt (tree-inc-label′ d S₁ b Z))
        >>= ++t-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (standard-label-bd->-trunk-height (Susp S₁) T (suc d) b r′ q r (PExt Z)) refl≃l refl≃sty ⟩
    < standard-coh′ (1 + d) (tree-bd (1 + d) T) >>= tree-inc-label (1 + d) T b >>= ++t-inc-left T S₂ >stm
      ≈˘⟨ reflexive≃stm (cong (λ - → standard-coh′ (1 + -) (tree-bd (1 + d) T) >>= tree-inc-label (1 + d) T b >>= ++t-inc-left T S₂)
                        (trans (tree-dim-bd d S₁) (m≤n⇒m⊓n≡m (≤-pred r′)))) ⟩
    < standard-coh′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T) >>= tree-inc-label (suc d) T b >>= ++t-inc-left T S₂ >stm
      ≈⟨ >>=-assoc (standard-coh′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)) (tree-inc-label (suc d) T b) (++t-inc-left T S₂) ⟩
    < standard-coh′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)
      >>= tree-inc-label (suc d) T b ●lt ++t-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (sym≃stm (standard-label-max (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)))
               [ (λ P → SPath≃ (tree-inc-inc-left d T S₂ b P)) ]
               refl≃sty ⟩
    < standard-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)
      >>= ++t-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
          ●lt (label-wt-≃ (++t-bd d T S₂) (tree-inc-label (suc d) (T ++t S₂) b)) >stm
      ≈˘⟨ >>=-assoc (standard-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)) _ _ ⟩
    < standard-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)
        >>=
        ++t-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
        >>=
        label-wt-≃ (++t-bd d T S₂) (tree-inc-label (suc d) (T ++t S₂) b) >stm ∎
  bd-κ-comm-2 (Join S₁ S₂) BHere T (suc d) b r (Cond2 q) .get (PExt Z) = let
    instance _ = is-linear-bd d S₁
    in begin
    < standard-label (Susp S₁) T (PExt (tree-inc-label′ d S₁ b Z))
        >>= ++t-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (standard-label-max (Susp S₁) T (PExt (tree-inc-label′ d S₁ b Z))
                                                ⦃ inst ⦃ tree-inc-full-preserve-max d S₁ b (≤-pred q) Z ⦄ ⦄)
               refl≃l
               refl≃sty ⟩
    < standard-coh′ (1 + tree-dim S₁) T >>= ++t-inc-left T S₂ >stm
      ≈˘⟨ >>=-≃′ (standard-coh′-≃ (cong suc (tree-dim-≃ (≃′-to-≃ (tree-bd-full d S₁ (≤-pred q)))))
                                    (≃′-to-≃ (tree-bd-full (suc d) T (≤-trans r q))))
                 ((tree-bd-full (suc d) T (≤-trans r q))
                   ,, [ (λ P → SPath≃ (ap′-≃ (++t-inc-left′ T S₂) (tree-inc-label-full (suc d) T b (≤-trans r q) .get P))) ])
                 refl≃sty ⟩
    < standard-coh′ (1 + tree-dim (tree-bd d S₁)) (tree-bd (suc d) T)
      >>= tree-inc-label (suc d) T b ●lt ++t-inc-left T S₂ >stm
      ≈⟨ >>=-≃ (sym≃stm (standard-label-max (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)))
               [ (λ P → SPath≃ (tree-inc-inc-left d T S₂ b P)) ]
               refl≃sty ⟩
    < standard-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)
      >>= ++t-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
          ●lt (label-wt-≃ (++t-bd d T S₂) (tree-inc-label (suc d) (T ++t S₂) b)) >stm
      ≈˘⟨ >>=-assoc (standard-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)) _ _ ⟩
    < standard-label (Susp (tree-bd d S₁)) (tree-bd (suc d) T) (PExt Z)
        >>=
        ++t-inc-left (tree-bd (suc d) T) (tree-bd (suc d) S₂)
        >>=
        label-wt-≃ (++t-bd d T S₂) (tree-inc-label (suc d) (T ++t S₂) b) >stm ∎

  bd-κ-comm-2 (Join S₁ S₂) (BExt P) (Susp T) (suc d) b r c .get (PExt Z) = let
    instance _ = bd-has-trunk-height d (bh P) T (bd-branch-lem P (cond-pred c))
    in begin
    < SExt (κ S₁ P T (tree-inc-label′ d S₁ b Z)) >stm
      ≈⟨ SExt≃ (bd-κ-comm-2 S₁ P T d b (≤-pred r) (cond-pred c) .get Z) refl≃ ⟩
    < SExt ((κ (tree-bd d S₁)
                               (bd-branch S₁ P d (bd-branch-lem P (cond-pred c)))
                               (tree-bd d T)
            ●l label-wt-≃ (insertion-bd-2 S₁ P T d (bd-branch-lem P (cond-pred c)))
                            (tree-inc-label d (S₁ >>[ P ] T) b)) Z) >stm
      ≈˘⟨ >>=-ext (κ (tree-bd d S₁) (bd-branch S₁ P d (bd-branch-lem P (cond-pred c))) (tree-bd d T) Z)
                  (label-wt-≃ (insertion-bd-2 S₁ P T d (bd-branch-lem P (cond-pred c))) (tree-inc-label d (S₁ >>[ P ] T) b)) ⟩
    < κ (tree-bd d S₁) (bd-branch S₁ P d (bd-branch-lem P (cond-pred c))) (tree-bd d T) Z
       >>= map-ext {T = S₂} (label-wt-≃ (insertion-bd-2 S₁ P T d (bd-branch-lem P (cond-pred c))) (tree-inc-label d (S₁ >>[ P ] T) b)) >stm
       ≈˘⟨ >>=-≃ (refl≃stm {a = κ (tree-bd d S₁) (bd-branch S₁ P d (bd-branch-lem P (cond-pred c))) (tree-bd d T) Z})
                 [ (λ P → compute-≃ refl≃stm) ]
                 (SArr≃ refl≃stm refl≃sty (compute-≃ (SShift≃ refl≃ (SPath≃ (tree-inc-label-phere d S₂ b))))) ⟩
    < κ (tree-bd d S₁) (bd-branch S₁ P d (bd-branch-lem P (cond-pred c))) (tree-bd d T) Z
       >>= label₁ (label-wt-≃ (Join≃′ (insertion-bd-2 S₁ P T d (bd-branch-lem P (cond-pred c))) refl≃′)
                              (tree-inc-label (suc d) (Join (S₁ >>[ P ] T) S₂) b)) >stm ∎
  bd-κ-comm-2 (Join S₁ S₂) (BExt P) (Susp T) (suc d) b r c .get (PShift Z)
    = compute-≃ refl≃stm
  bd-κ-comm-2 (Join S₁ S₂) (BShift P) T (suc d) b r c .get (PExt Z)
    = compute-≃ refl≃stm
  bd-κ-comm-2 (Join S₁ S₂) (BShift P) T (suc d) b r c .get (PShift Z) = let
    instance _ = bd-has-trunk-height (suc d) (bh P) T (bd-branch-lem P c)
    in begin
    < SShift (κ S₂ P T (tree-inc-label′ (suc d) S₂ b Z)) >stm
      ≈⟨ SShift≃ refl≃ (bd-κ-comm-2 S₂ P T (suc d) b r c .get Z) ⟩
    < SShift (κ (tree-bd (suc d) S₂) (bd-branch S₂ P (suc d) (bd-branch-lem P c)) (tree-bd (suc d) T) Z
        >>= label-wt-≃ (insertion-bd-2 S₂ P T (suc d) (bd-branch-lem P c)) (tree-inc-label (suc d) (S₂ >>[ P ] T) b)) >stm
      ≈˘⟨ >>=-shift (κ (tree-bd (suc d) S₂) (bd-branch S₂ P (suc d) (bd-branch-lem P c)) (tree-bd (suc d) T) Z)
                    (label-wt-≃ (insertion-bd-2 S₂ P T (suc d) (bd-branch-lem P c)) (tree-inc-label (suc d) (S₂ >>[ P ] T) b)) ⟩
    < κ (tree-bd (suc d) S₂) (bd-branch S₂ P (suc d) (bd-branch-lem P c)) (tree-bd (suc d) T) Z
       >>= map-shift (label-wt-≃ (insertion-bd-2 S₂ P T (suc d) (bd-branch-lem P c)) (tree-inc-label (suc d) (S₂ >>[ P ] T) b)) >stm
      ≈⟨ >>=-≃ (refl≃stm {a = κ (tree-bd (suc d) S₂) (bd-branch S₂ P (suc d) (bd-branch-lem P c)) (tree-bd (suc d) T) Z})
               [ (λ P → compute-≃ refl≃stm) ]
               refl≃sty ⟩
    < κ (tree-bd (suc d) S₂) (bd-branch S₂ P (suc d) (bd-branch-lem P c)) (tree-bd (suc d) T) Z
       >>= label₂ (label-wt-≃ (Join≃′ refl≃′ (insertion-bd-2 S₂ P T (suc d) (bd-branch-lem P c)))
                           (tree-inc-label (suc d) (Join S₁ (S₂ >>[ P ] T)) b)) >stm ∎

data Bd-Conditions (d : ℕ) {S : Tree n} (P : Branch S l) (T : Tree m) : Set where
  Bd-Cond1 : d < lh P → d ≤ trunk-height T → Bd-Conditions d P T
  Bd-Cond2 : Condition d T (lh P) → Bd-Conditions d P T

Bd-Conditions-one-of : (d : ℕ) → (P : Branch S l) → (T : Tree m) → Bd-Conditions d P T
Bd-Conditions-one-of d P T with <-cmp d (lh P)
... | tri≈ ¬a b ¬c = Bd-Cond2 (Cond2 (≤-reflexive (sym b)))
... | tri> ¬a ¬b c = Bd-Cond2 (Cond2 (<⇒≤ c))
... | tri< a ¬b ¬c with <-cmp d (trunk-height T)
... | tri< a₁ ¬b₁ ¬c₁ = Bd-Cond1 a (<⇒≤ a₁)
... | tri≈ ¬a b ¬c₁ = Bd-Cond1 a (≤-reflexive b)
... | tri> ¬a ¬b₁ c = Bd-Cond2 (Cond1 c (<⇒≤ a))

pruned-branch : (S : Tree n)
              → (P : Branch S l)
              → .(bh P < pred (lh P))
              → Branch (S //t P) l
pruned-branch (Join S T) (BExt P) q = BExt (pruned-branch S P (≤-pred q))
pruned-branch (Join S T) (BShift P) q = BShift (pruned-branch T P q)
pruned-branch (Join (Susp S) T) BHere q = BHere

insertion-tree-pruned-branch : (S : Tree n)
                             → (P : Branch S l)
                             → (T : Tree m)
                             → .⦃ _ : has-trunk-height (bh P) T ⦄
                             → .(q : bh P < pred (lh P))
                             →  (S //t P) >>[ pruned-branch S P q ] T ≃′ S >>[ P ] T
insertion-tree-pruned-branch (Join S₁ S₂) (BExt P) (Susp T) q = Join≃′ (insertion-tree-pruned-branch S₁ P T (≤-pred q)) refl≃′
insertion-tree-pruned-branch (Join S₁ S₂) (BShift P) T q = Join≃′ refl≃′ (insertion-tree-pruned-branch S₂ P T q)
insertion-tree-pruned-branch (Join (Susp S₁) S₂) BHere T q = refl≃′

pruned-branch-prop : (S : Tree n)
                   → (P : Branch S l)
                   → .(q : bh P < pred (lh P))
                   → SPath ⌊ pruned-branch S P q ⌋p
                     ≃stm
                     ι S P (n-disc (pred (lh P)))
                       ⦃ has-trunk-height-n-disc (≤-pred (bh-<-lh P)) ⦄
                       (is-linear-max-path (n-disc (pred (lh P))))
pruned-branch-prop (Join S T) (BExt P) q = compute-≃ (SExt≃ (pruned-branch-prop S P (≤-pred q)) refl≃)
pruned-branch-prop (Join S T) (BShift P) q = compute-≃ (SShift≃ refl≃ (pruned-branch-prop T P q))
pruned-branch-prop (Join (Susp S) T) BHere q = refl≃stm

label-from-pruned-branch : (L : Label X S)
                         → (P : Branch S l)
                         → {T : Tree n}
                         → (M : Label-WT X T)
                         → .⦃ _ : has-trunk-height l T ⦄
                         → .(q : bh P < pred (lh P))
                         → L ⌊ P ⌋p ≃stm standard-coh′ (lh P) T >>= M
                         → (L >>p[ P ] standard-label (n-disc (pred (lh P))) T ●l M) >>l[ pruned-branch S P q ] (ap M)
                           ≃lm
                           label-≃ (insertion-tree-pruned-branch S P T q)
                                   (L >>l[ P ] (ap M))
label-from-pruned-branch {S = Join S₁ S₂} L (BExt {n = n} P) {T = Susp T} M q pf .get (PExt Z) = begin
  < ((L ∘ PExt >>p[ P ] (standard-label (n-disc (lh P)) (Susp T) ●l M) ∘ PExt)
    >>l[ pruned-branch S₁ P _ ] ap M ∘ PExt) Z >stm
    ≈⟨ label-from-insertion-≃
         (label-from-prune-≃ refl≃l P
           (label-comp-≃ [ (λ Z → standard-label-susp-lem (n-disc (pred (lh P))) T .get (PExt Z)) ]
                         refl≃l
                         refl≃sty))
         (pruned-branch S₁ P _)
         refl≃l
         .get Z ⟩
  < ((L ∘ PExt >>p[ P ] (standard-label (n-disc (pred (lh P))) T ●l label₁ M))
    >>l[ (pruned-branch S₁ P _) ] (ap M ∘ PExt)) Z >stm
    ≈⟨ label-from-pruned-branch (L ∘ PExt) P (label₁ M) (≤-pred q) pf .get Z ⟩
  < label-≃ (insertion-tree-pruned-branch S₁ P T _)
            (L ∘ PExt >>l[ P ] ap (label₁ M)) Z >stm ∎
  where
    open Reasoning stm-setoid
label-from-pruned-branch {S = Join S₁ S₂} L (BExt {n = n} P) {T = Susp T} M q pf .get (PShift Z) = begin
  < replace-label
      ((L >>p[ BExt {n = n} P ] standard-label (Susp (n-disc (lh′ P))) (Susp T) ●l M) ∘ PShift)
      (ap M (PShift PHere)) Z >stm
    ≈⟨ replace-not-here _ (ap M (PShift PHere)) Z ⟩
  < (L >>p[ BExt P ] (standard-label (n-disc (lh P)) (Susp T) ●l M)) (PShift Z) >stm
    ≈⟨ replace-not-here (L ∘ PShift) _ Z ⟩
  < L (PShift Z) >stm
    ≈˘⟨ replace-not-here (L ∘ PShift) (ap M (PShift PHere)) Z ⟩
  < replace-label (L ∘ PShift) (ap M (PShift PHere)) Z >stm ∎
  where
    open Reasoning stm-setoid
label-from-pruned-branch {S = Join S₁ S₂} L (BShift P) M q pf .get (PExt Z) = refl≃stm
label-from-pruned-branch {S = Join S₁ S₂} L (BShift P) M q pf .get (PShift Z)
  = label-from-pruned-branch (L ∘ PShift) P M q pf .get Z
label-from-pruned-branch {S = Susp (Susp S)} L BHere M q pf = ≃l-to-≃lm (++l-sing (ap M) _ _)
label-from-pruned-branch {S = Join (Susp S₁) (Join S₂ S₃)} L BHere M q pf
  = ++l-≃m (refl≃lm {L = ap M}) (replace-join-≃lm (L ∘ PShift) _)

insertion-trunk-height : (S : Tree n)
                       → .⦃ non-linear S ⦄
                       → (P : Branch S l)
                       → (T : Tree m)
                       → .⦃ _ : has-trunk-height l T ⦄
                       → (d : ℕ)
                       → .⦃ has-trunk-height d S ⦄
                       → has-trunk-height d (S >>[ P ] T)
insertion-trunk-height S P T zero = tt
insertion-trunk-height (Susp S) BHere T (suc d) = ⊥-elim (linear-non-linear S)
insertion-trunk-height (Susp S) (BExt P) (Susp T) (suc d) = inst ⦃ insertion-trunk-height S P T d ⦄

inserted-branch : (S : Tree n)
                → (P : Branch S l)
                → (T : Tree m)
                → .⦃ _ : has-trunk-height l T ⦄
                → .⦃ _ : non-linear T ⦄
                → (Q : Branch T l′)
                → Branch (S >>[ P ] T) l′
inserted-branch (Join S₁ S₂) BHere T Q = wedge-branch-left T S₂ Q
inserted-branch (Join S₁ S₂) (BExt P) (Susp T) BHere = ⊥-elim (linear-non-linear T)
inserted-branch (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) = BExt (inserted-branch S₁ P T Q)
inserted-branch (Join S₁ S₂) (BShift P) T Q = BShift (inserted-branch S₂ P T Q)

inserted-branch-prop : (S : Tree n)
                     → (P : Branch S l)
                     → (T : Tree m)
                     → .⦃ _ : has-trunk-height l T ⦄
                     → .⦃ _ : non-linear T ⦄
                     → (Q : Branch T l′)
                     → SPath ⌊ inserted-branch S P T Q ⌋p
                       ≃stm
                       ι S P T ⌊ Q ⌋p
inserted-branch-prop (Join S₁ S₂) BHere T Q = wedge-branch-left-prop T S₂ Q
inserted-branch-prop (Join S₁ S₂) (BExt P) (Susp T) BHere = ⊥-elim (linear-non-linear T)
inserted-branch-prop (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) = compute-≃ (SExt≃ (inserted-branch-prop S₁ P T Q) refl≃)
inserted-branch-prop (Join S₁ S₂) (BShift P) T Q = compute-≃ (SShift≃ refl≃ (inserted-branch-prop S₂ P T Q))

insertion-tree-inserted-branch : (S : Tree n)
                               → (P : Branch S l)
                               → (T : Tree m)
                               → .⦃ _ : has-trunk-height l T ⦄
                               → .⦃ _ : non-linear T ⦄
                               → (Q : Branch T l′)
                               → (U : Tree m′)
                               → .⦃ _ : has-trunk-height l′ U ⦄
                               → (S >>[ P ] T) >>[ inserted-branch S P T Q ] U
                                 ≃′
                                 (S >>[ P ] (T >>[ Q ] U)) ⦃ insertion-trunk-height T Q U l ⦄
insertion-tree-inserted-branch (Join S₁ S₂) BHere T Q U = insertion-branch-left T S₂ Q U
insertion-tree-inserted-branch (Join S₁ S₂) (BExt P) (Susp T) BHere U = ⊥-elim (linear-non-linear T)
insertion-tree-inserted-branch (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Susp U) = Join≃′ (insertion-tree-inserted-branch S₁ P T Q U) refl≃′
insertion-tree-inserted-branch (Join S₁ S₂) (BShift P) T Q U = Join≃′ refl≃′ (insertion-tree-inserted-branch S₂ P T Q U)

label-from-inserted-branch : (L : Label X S)
                           → (P : Branch S l)
                           → {T : Tree n}
                           → (M : Label X T)
                           → .⦃ _ : has-trunk-height l T ⦄
                           → .⦃ _ : non-linear T ⦄
                           → (Q : Branch T l′)
                           → {U : Tree m}
                           → (N : Label X U)
                           → .⦃ _ : has-trunk-height l′ U ⦄
                           → (L >>l[ P ] M) >>l[ inserted-branch S P T Q ] N
                             ≃lm
                             label-≃ (insertion-tree-inserted-branch S P T Q U) ((L >>l[ P ] (M >>l[ Q ] N)) ⦃ insertion-trunk-height T Q U l ⦄)
label-from-inserted-branch L BHere M Q N = label-from-branch-left M (L ∘ PShift) Q N
label-from-inserted-branch L (BExt P) {Susp T} M BHere N = ⊥-elim (linear-non-linear T)
label-from-inserted-branch L (BExt P) {Susp T} M (BExt Q) {Susp U} N .get (PExt Z)
  = label-from-inserted-branch (L ∘ PExt) P (M ∘ PExt) Q (N ∘ PExt) .get Z
label-from-inserted-branch {S = Join S₁ .(Join _ _)} L (BExt P) {Susp T} M (BExt Q) {Susp U} N .get (PShift (PExt Z)) = refl≃stm
label-from-inserted-branch {S = Join S₁ .(Join _ _)} L (BExt P) {Susp T} M (BExt Q) {Susp U} N .get (PShift (PShift Z)) = refl≃stm
label-from-inserted-branch L (BShift P) M Q N .get (PExt Z) = refl≃stm
label-from-inserted-branch L (BShift P) M Q N .get (PShift Z) = label-from-inserted-branch (L ∘ PShift) P M Q N .get Z
