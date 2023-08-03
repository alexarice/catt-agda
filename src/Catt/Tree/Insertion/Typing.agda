open import Catt.Typing.Rule

module Catt.Tree.Insertion.Typing {index : Set}
                              (rule : index → Rule)
                              (lift-rule : ∀ i → LiftRule rule (rule i))
                              (susp-rule : ∀ i → SuspRule rule (rule i))
                              (sub-rule : ∀ i → SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties

open import Catt.Typing rule
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased.Typing rule lift-rule susp-rule sub-rule

interior-sub-label-Ty : (S : Tree n)
                      → (p : BranchingPoint S d)
                      → (T : Tree m)
                      → .⦃ _ : has-linear-height (bp-height p) T ⦄
                      → Typing-Label (tree-to-ctx (insertion-tree S p T)) (interior-sub-label S p T ,, S⋆)
interior-sub-label-Ty (Join S₁ S₂) BPHere T = connect-tree-inc-left-Ty T S₂
interior-sub-label-Ty (Join S₁ S₂) (BPExt p) (Join T Sing)
  = TyJoin (TySPath PHere)
           (map-pext-Ty (interior-sub-label-Ty S₁ p T))
           (TySing (TySShift (TySPath PHere)))
interior-sub-label-Ty (Join S₁ S₂) (BPShift p) T = map-pshift-Ty (interior-sub-label-Ty S₂ p T)

interior-sub-Ty : (S : Tree n)
                → (p : BranchingPoint S d)
                → (T : Tree m)
                → .⦃ _ : has-linear-height (bp-height p) T ⦄
                → Typing-Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S p T)) (interior-sub S p T)
interior-sub-Ty S p T = label-to-sub-Ty (interior-sub-label-Ty S p T) TySStar

exterior-sub-label-Ty : (S : Tree n)
                      → (p : BranchingPoint S d)
                      → (T : Tree m)
                      → .⦃ _ : has-linear-height (bp-height p) T ⦄
                      → (q : height-of-branching p ≥ tree-dim T)
                      → Typing-Label (tree-to-ctx (insertion-tree S p T)) (exterior-sub-label S p T ,, S⋆)
exterior-sub-label-Ty (Join S₁ S₂) BPHere T q
  = label-between-connect-trees-Ty (label-from-linear-tree-unbiased-Ty-0 (susp-tree S₁) T)
                                   (id-label-Ty S₂)
                                   refl≈stm
                                   refl≈stm
exterior-sub-label-Ty (Join S₁ S₂) (BPExt p) (Join T Sing) q
  = label-between-joins-Ty (exterior-sub-label-Ty S₁ p T (≤-pred q))
                           (id-label-Ty S₂)
                           refl≈stm
exterior-sub-label-Ty (Join S₁ S₂) (BPShift p) T q
  = label-between-joins-Ty (id-label-Ty S₁)
                           (exterior-sub-label-Ty S₂ p T q)
                           (reflexive≈stm (exterior-sub-label-phere S₂ p T) )

exterior-sub-Ty : (S : Tree n)
                → (p : BranchingPoint S d)
                → (T : Tree m)
                → .⦃ _ : has-linear-height (bp-height p) T ⦄
                → (height-of-branching p ≥ tree-dim T)
                → Typing-Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S p T)) (exterior-sub S p T)
exterior-sub-Ty S p T q = label-to-sub-Ty (exterior-sub-label-Ty S p T q) TySStar

sub-from-insertion-label-lem : (S₁ : Tree n)
                             → (S₂ : Tree m)
                             → (T : Tree l)
                             → (As : STy (someTree S₁))
                             → (L : Label X (Join S₁ S₂))
                             → (M : Label X T)
                             → (d : ℕ)
                             → .⦃ NonZero d ⦄
                             → label-on-sty (map-sty-pext As) (L ,, Bs) ≈[ Γ ]sty label-on-sty (unbiased-type d T) (M ,, Bs)
                             → label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (L ,, Bs)
                             ≈[ Γ ]sty
                             label-on-sty (SArr SHere S⋆ (SPath (last-path T))) (M ,, Bs)
sub-from-insertion-label-lem {Bs = Bs} S₁ S₂ T As L M d p = begin
  label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (L ,, Bs)
    ≈˘⟨ reflexive≈sty (label-on-sty-≃ (truncate-sty-1-map-pext As) refl≃l refl≃sty) ⟩
  label-on-sty (truncate-sty 1 (map-sty-pext As)) (L ,, Bs)
    ≈˘⟨ reflexive≈sty (truncate-sty-label 1 (map-sty-pext As) (L ,, Bs)) ⟩
  truncate-sty (1 + sty-dim Bs) (label-on-sty (map-sty-pext As) (L ,, Bs))
    ≈⟨ truncate-sty-≈ {d = 1 + sty-dim Bs} refl p ⟩
  truncate-sty (1 + sty-dim Bs) (label-on-sty (unbiased-type d T) (M ,, Bs))
    ≈⟨ reflexive≈sty (truncate-sty-label 1 (unbiased-type d T) (M ,, Bs)) ⟩
  label-on-sty (truncate-sty 1 (unbiased-type d T)) (M ,, Bs)
    ≈⟨ reflexive≈sty (label-on-sty-≃ (truncate-unbiased-sty d T) refl≃l refl≃sty) ⟩
  label-on-sty (SArr SHere S⋆ (SPath (last-path T))) (M ,, Bs) ∎
  where
    open Reasoning sty-setoid-≈

sub-from-insertion-label-phere : (S : Tree n)
                               → (P : BranchingPoint S l)
                               → (T : Tree m)
                               → .⦃ lh : has-linear-height (bp-height P) T ⦄
                               → (L : Label X S)
                               → (M : Label X T)
                               → (d : ℕ)
                               → .⦃ NonZero d ⦄
                               → label-on-sty (branching-path-to-type S P) (L ,, As) ≈[ Γ ]sty label-on-sty (unbiased-type d T) (M ,, As)
                               → sub-from-insertion-label S P T L M PHere ≈[ Γ ]stm L PHere
sub-from-insertion-label-phere (Join S₁ S₂) BPHere T L M d p = begin
  connect-label M (L ∘ PShift) PHere
    ≈⟨ reflexive≈stm (connect-label-phere M (L ∘ PShift)) ⟩
  M PHere
    ≈˘⟨ ≈SArr-proj₁ lem ⟩
  L PHere ∎
  where
    open Reasoning stm-setoid-≈

    lem : label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (L ,, _) ≈[ _ ]sty label-on-sty (SArr SHere S⋆ (SPath (last-path T))) (M ,, _)
    lem = sub-from-insertion-label-lem S₁ S₂ T (unbiased-type (tree-dim S₁) S₁) L M d p
sub-from-insertion-label-phere (Join S₁ S₂) (BPExt P) (Join T Sing) L M d p = sym≈stm (≈SArr-proj₁ lem)
  where
    lem : label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (L ,, _) ≈[ _ ]sty label-on-sty (SArr SHere S⋆ (SPath (last-path (Join T Sing))))
                                                                                   (M ,, _)
    lem = sub-from-insertion-label-lem S₁ S₂ (Join T Sing) (branching-path-to-type S₁ P) L M d p
sub-from-insertion-label-phere (Join S₁ S₂) (BPShift P) T L M d p = refl≈stm

sub-from-insertion-label-Ty : (S : Tree n)
                            → (P : BranchingPoint S l)
                            → (T : Tree m)
                            → .⦃ lh : has-linear-height (bp-height P) T ⦄
                            → {L : Label X S}
                            → Typing-Label Γ (L ,, As)
                            → {M : Label X T}
                            → Typing-Label Γ (M ,, As)
                            → label-on-sty (branching-path-to-type S P) (L ,, As) ≈[ Γ ]sty label-on-sty (unbiased-type (height-of-branching P) T) (M ,, As)
                            → Typing-Label Γ (sub-from-insertion-label S P T L M ,, As)
sub-from-insertion-label-Ty {As = As}(Join S₁ S₂) BPHere T {L} (TyJoin x Lty Lty′) {M} Mty p
  = connect-label-Ty Mty Lty′ (sym≈stm (≈SArr-proj₃ lem))
  where
    lem : label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (L ,, As) ≈[ _ ]sty label-on-sty (SArr SHere S⋆ (SPath (last-path T))) (M ,, As)
    lem = sub-from-insertion-label-lem S₁ S₂ T (unbiased-type (tree-dim S₁) S₁) L M (suc (tree-dim S₁)) p
sub-from-insertion-label-Ty {As = As} (Join S₁ S₂) (BPExt P) (Join T Sing) {L} (TyJoin x Lty Lty′) {M} (TyJoin y Mty (TySing z)) p
  = TyJoin y (sub-from-insertion-label-Ty S₁ P T (label-typing-conv Lty lem) Mty lem2) (replace-label-Ty Lty′ z (≈SArr-proj₃ lem))
  where
    lem : (label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (L ,, As)) ≈[ _ ]sty
            (label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (M ,, As))
    lem = sub-from-insertion-label-lem S₁ S₂ (Join T Sing) (branching-path-to-type S₁ P) L M (suc (height-of-branching P)) p

    open Reasoning sty-setoid-≈

    lem2 : label-on-sty (branching-path-to-type S₁ P)
             ((L ∘ PExt) ,, label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (M ,, As))
             ≈[ _ ]sty
           label-on-sty (unbiased-type (height-of-branching P) T)
             ((M ∘ PExt) ,, label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (M ,, As))
    lem2 = begin
      label-on-sty (branching-path-to-type S₁ P)
        (L ∘ PExt ,, label-on-sty (SArr SHere S⋆ (SPath (PShift PHere))) (M ,, As))
        ≈˘⟨ label-on-sty-≈ (branching-path-to-type S₁ P) refl≈l lem ⟩
      label-on-sty (branching-path-to-type S₁ P) (label₁ (L ,, As))
        ≈˘⟨ reflexive≈sty (map-sty-pext-label (branching-path-to-type S₁ P) (L ,, As)) ⟩
      label-on-sty (map-sty-pext (branching-path-to-type S₁ P)) (L ,, As)
        ≈⟨ p ⟩
      label-on-sty
        (unbiased-type (suc (height-of-branching P)) (Join T Sing))
        (M ,, As)
        ≈˘⟨ reflexive≈sty (label-on-sty-≃ (unbiased-type-susp-lem (height-of-branching P) T) refl≃l refl≃sty) ⟩
      label-on-sty (susp-sty (unbiased-type (height-of-branching P) T)) (M ,, As)
        ≈˘⟨ reflexive≈sty (label-on-sty-≃ (map-sty-pext-susp-compat (unbiased-type (height-of-branching P) T)) refl≃l refl≃sty) ⟩
      label-on-sty (map-sty-pext (unbiased-type (height-of-branching P) T)) (M ,, As)
        ≈⟨ reflexive≈sty (map-sty-pext-label (unbiased-type (height-of-branching P) T) (M ,, As)) ⟩
      label-on-sty (unbiased-type (height-of-branching P) T) (label₁ (M ,, As)) ∎

sub-from-insertion-label-Ty {As = As} (Join S₁ S₂) (BPShift P) T {L} (TyJoin x Lty Lty′) {M} Mty p
  = TyJoin x (label-typing-conv Lty (≈SArr refl≈stm
                                           refl≈sty
                                           (sym≈stm (sub-from-insertion-label-phere S₂ P T (L ∘ PShift) M (height-of-branching P) lem))))
             (sub-from-insertion-label-Ty S₂ P T Lty′ Mty lem)

  where
    open Reasoning sty-setoid-≈
    lem : label-on-sty (branching-path-to-type S₂ P) ((L ∘ PShift) ,, As)
          ≈[ _ ]sty
          label-on-sty (unbiased-type (height-of-branching P) T) (M ,, As)
    lem = begin
      label-on-sty (branching-path-to-type S₂ P) ((L ∘ PShift) ,, As)
        ≈˘⟨ reflexive≈sty (map-sty-pshift-label (branching-path-to-type S₂ P) (L ,, As)) ⟩
      label-on-sty (map-sty-pshift (branching-path-to-type S₂ P)) (L ,, As)
        ≈⟨ p ⟩
      label-on-sty (unbiased-type (height-of-branching P) T) (M ,, As) ∎


{-
branching-path-to-var-height : (S : Tree n)
                             → (p : BranchingPoint S)
                             → tm-height (tree-to-ctx S) (branching-path-to-var S p) ≡ height-of-branching p
branching-path-to-var-height (Join S₁ S₂) BPHere = begin
  tm-height (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
      (0V [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm)
    ≡˘⟨ sub-tm-height-0 0V (tree-to-ctx (susp-tree S₁)) (connect-susp-inc-left-Ty (tree-to-ctx S₂)) ⟩
  tm-height (tree-to-ctx (susp-tree S₁)) 0V
    ≡⟨ susp-tm-height 0V (tree-to-ctx S₁) ⟩
  suc (tm-height (tree-to-ctx S₁) 0V)
    ≡⟨ cong suc (linear-tree-dim S₁) ⟩
  suc (tree-dim S₁) ∎
  where
    open ≡-Reasoning
branching-path-to-var-height (Join S₁ S₂) (BPExt P) = begin
  tm-height (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
      (susp-tm (branching-path-to-var S₁ P)
        [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm)
    ≡˘⟨ sub-tm-height-0 (susp-tm (branching-path-to-var S₁ P)) (tree-to-ctx (susp-tree S₁)) (connect-susp-inc-left-Ty (tree-to-ctx S₂)) ⟩
  tm-height (tree-to-ctx (susp-tree S₁)) (susp-tm (branching-path-to-var S₁ P))
    ≡⟨ susp-tm-height (branching-path-to-var S₁ P) (tree-to-ctx S₁) ⟩
  suc (tm-height (tree-to-ctx S₁) (branching-path-to-var S₁ P))
    ≡⟨ cong suc (branching-path-to-var-height S₁ P) ⟩
  suc (height-of-branching P) ∎
  where
    open ≡-Reasoning
branching-path-to-var-height (Join S₁ S₂) (BPShift P) = begin
  tm-height (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
      (branching-path-to-var S₂ P [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
    ≡˘⟨ sub-tm-height-0 (branching-path-to-var S₂ P) (tree-to-ctx S₂) (connect-susp-inc-right-Ty (tree-to-ctx S₁)) ⟩
  tm-height (tree-to-ctx S₂) (branching-path-to-var S₂ P)
    ≡⟨ branching-path-to-var-height S₂ P ⟩
  height-of-branching P ∎
  where
    open ≡-Reasoning

branching-path-to-var-Ty : (T : Tree n) → (p : BranchingPoint T) → Typing-Tm (tree-to-ctx T) (branching-path-to-var T p) (branching-path-to-type T p)
branching-path-to-var-Ty (Join S T) BPHere = apply-sub-tm-typing (susp-tmTy (TyConv (TyVar 0F) (reflexive≈ty (linear-tree-unbiased-lem (tree-dim S) S refl)))) (connect-susp-inc-left-Ty (tree-to-ctx T))
branching-path-to-var-Ty (Join S T) (BPExt P) = apply-sub-tm-typing (susp-tmTy (branching-path-to-var-Ty S P)) (connect-susp-inc-left-Ty (tree-to-ctx T))
branching-path-to-var-Ty (Join S T) (BPShift P) = apply-sub-tm-typing (branching-path-to-var-Ty T P) (connect-susp-inc-right-Ty (tree-to-ctx S))

insertion-dim-lem : (S : Tree n)
                  → (p : BranchingPoint S)
                  → (T : Tree m)
                  → .⦃ lh : has-linear-height (bp-height p) T ⦄
                  → {σ : Sub (suc n) l A}
                  → {τ : Sub (suc m) l A}
                  → Typing-Sub (tree-to-ctx S) Γ σ
                  → Typing-Sub (tree-to-ctx T) Γ τ
                  → branching-path-to-var S p [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                  → height-of-branching p ≡ tree-dim T
insertion-dim-lem {A = A} S P T {σ} {τ} σty τty p = +-cancelʳ-≡ (height-of-branching P) (tree-dim T) (begin
  height-of-branching P + ty-dim A
    ≡˘⟨ cong (_+ ty-dim A) (branching-path-to-var-height S P) ⟩
  tm-height (tree-to-ctx S) (branching-path-to-var S P) + ty-dim A
    ≡⟨ sub-tm-height (branching-path-to-var S P) (tree-to-ctx S) σty ⟩
  tm-height _ (branching-path-to-var S P [ σ ]tm)
    ≡⟨ tm-height-≃ _ p ⟩
  tm-height _ (unbiased-comp (tree-dim T) T [ τ ]tm)
    ≡˘⟨ sub-tm-height (unbiased-comp (tree-dim T) T) (tree-to-ctx T) τty ⟩
  tm-height (tree-to-ctx T) (unbiased-comp (tree-dim T) T) + ty-dim A
    ≡⟨ cong (_+ ty-dim A) (unbiased-comp-dim (tree-dim T) T) ⟩
  tree-dim T + ty-dim A ∎)
  where
    open ≡-Reasoning

-- interior-sub-label-Ty : (S : Tree n)
--                       → (p : BranchingPoint S)
--                       → (T : Tree m)
--                       → .⦃ _ : has-linear-height (bp-height p) T ⦄
--                       → Typing-Label (incTree (insertion-tree S p T)) (interior-sub-label S p T) ⋆
-- interior-sub-label-Ty (Join S₁ S₂) BPHere T = connect-tree-inc-left-Ty T S₂
-- interior-sub-label-Ty (Join S₁ S₂) (BPExt p) (Join T Sing)
--   = TyJoin TyHere
--            (label-typing-conv (label-pext-Ty (interior-sub-label-Ty S₁ p T))
--                               (reflexive≈ty (Arr≃ (connect-inc-left-fst-var get-snd (tree-size S₂))
--                                             refl≃ty
--                                             (connect-inc-fst-var get-snd (tree-size S₂)))))
--            (TySing (TyShift TyHere))
-- interior-sub-label-Ty (Join S₁ S₂) (BPShift p) T = label-pshift-Ty (interior-sub-label-Ty S₂ p T)

-- interior-sub-Ty : (S : Tree n)
--                 → (p : BranchingPoint S)
--                 → (T : Tree m)
--                 → .⦃ _ : has-linear-height (bp-height p) T ⦄
--                 → Typing-Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S p T)) (interior-sub S p T)
-- interior-sub-Ty S p T = label-typing-to-sub (interior-sub-label-Ty S p T) TyStar

interior-sub-label-Ty : (S : Tree n)
                      → (p : BranchingPoint S)
                      → (T : Tree m)
                      → .⦃ _ : has-linear-height (bp-height p) T ⦄
                      → Typing-Label (incTree (insertion-tree S p T)) (interior-sub-label S p T)
interior-sub-label-Ty (Join S₁ S₂) BPHere T = connect-tree-inc-left-Ty T S₂
interior-sub-label-Ty (Join S₁ S₂) (BPExt p) (Join T Sing)
  = TyJoin TyHere
           (convert-type-Ty (map-pext-Ty (interior-sub-label-Ty S₁ p T))
                            (reflexive≈ty (Arr≃ (connect-inc-left-fst-var get-snd (tree-size S₂))
                                                refl≃ty
                                                (connect-inc-fst-var get-snd (tree-size S₂)))))
           (TySing (TyShift TyHere))
interior-sub-label-Ty (Join S₁ S₂) (BPShift p) T = map-pshift-Ty (interior-sub-label-Ty S₂ p T)

interior-sub-Ty : (S : Tree n)
                → (p : BranchingPoint S)
                → (T : Tree m)
                → .⦃ _ : has-linear-height (bp-height p) T ⦄
                → Typing-Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S p T)) (interior-sub S p T)
interior-sub-Ty S p T = label-to-sub-Ty (interior-sub-label-Ty S p T) TyStar

exterior-sub-label-Ty : (S : Tree n)
                      → (p : BranchingPoint S)
                      → (T : Tree m)
                      → .⦃ _ : has-linear-height (bp-height p) T ⦄
                      → .⦃ q : height-of-branching p ≡ tree-dim T ⦄
                      → Typing-Label (incTree (insertion-tree S p T)) (exterior-sub-label S p T)
exterior-sub-label-Ty (Join S₁ S₂) BPHere T
  = label-between-connect-trees-Ty (to-label-Ty (susp-tree S₁) (incTree T) (sub-from-linear-tree-unbiased-Ty-0 (susp-tree S₁) T ⦃ NonZero-subst it it ⦄ (sym it)))
                                   (id-label-Ty S₂)
                                   (reflexive≈tm (unrestrict-snd (sub-from-linear-tree-unbiased S₁ T 1)))
                                   refl≈tm
exterior-sub-label-Ty (Join S₁ S₂) (BPExt p) (Join T Sing)
  = label-between-joins-Ty (exterior-sub-label-Ty S₁ p T ⦃ q = cong pred it ⦄)
                           (id-label-Ty S₂)
                           refl≈tm
exterior-sub-label-Ty (Join S₁ S₂) (BPShift p) T
  = label-between-joins-Ty (id-label-Ty S₁)
                           (exterior-sub-label-Ty S₂ p T)
                           (reflexive≈tm (exterior-sub-pphere S₂ p T))

exterior-sub-Ty : (S : Tree n)
                → (p : BranchingPoint S)
                → (T : Tree m)
                → .⦃ _ : has-linear-height (bp-height p) T ⦄
                → .⦃ q : height-of-branching p ≡ tree-dim T ⦄
                → Typing-Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S p T)) (exterior-sub S p T)
exterior-sub-Ty S p T = label-to-sub-Ty (exterior-sub-label-Ty S p T) TyStar

{-
sub-from-insertion-lem : (S₁ : Tree n)
                       → (S₂ : Tree m)
                       → (T : Tree l)
                       → (t : Tm (suc n))
                       → .⦃ isVar t ⦄
                       → {σ : Sub (suc (m + (2 + n))) o A}
                       → {τ : Sub (suc l) o A}
                       → Typing-Sub (tree-to-ctx (Join S₁ S₂)) Γ σ
                       → Typing-Sub (tree-to-ctx T) Γ τ
                       → susp-tm t [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                       → (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
                         ≈[ Γ ]ty
                         (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty
sub-from-insertion-lem {A = A} {Γ = Γ} S₁ S₂ T t {σ} {τ} σty τty p = ty-trunc-eq
  where
    T-dim-lem : suc (tm-height (tree-to-ctx S₁) t) ≡ tree-dim T
    T-dim-lem = +-cancelʳ-≡ (suc (tm-height (tree-to-ctx S₁) t)) (tree-dim T) (begin
      suc (tm-height (tree-to-ctx S₁) t) + ty-dim A
        ≡˘⟨ cong (_+ ty-dim A) (susp-tm-height t (tree-to-ctx S₁)) ⟩
      tm-height (susp-ctx (tree-to-ctx S₁)) (susp-tm t) + ty-dim A
        ≡⟨ cong (_+ ty-dim A) (sub-tm-height-0 (susp-tm t) (susp-ctx (tree-to-ctx S₁)) (connect-susp-inc-left-Ty (tree-to-ctx S₂))) ⟩
      tm-height (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
        (susp-tm t [ connect-susp-inc-left _ _ ]tm) + ty-dim A
        ≡⟨ sub-tm-height (susp-tm t [ connect-susp-inc-left _ _ ]tm) (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂)) σty ⟩
      tm-height Γ ((susp-tm t [ connect-susp-inc-left _ _ ]tm) [ σ ]tm)
        ≡⟨ tm-height-≃ Γ p ⟩
      tm-height Γ (unbiased-comp (tree-dim T) T [ τ ]tm)
        ≡˘⟨ sub-tm-height (unbiased-comp (tree-dim T) T) (tree-to-ctx T) τty ⟩
      tm-height (tree-to-ctx T) (unbiased-comp (tree-dim T) T) + ty-dim A
        ≡⟨ cong (_+ ty-dim A) (unbiased-comp-dim (tree-dim T) T) ⟩
      tree-dim T + ty-dim A ∎)
      where
        open ≡-Reasoning

    instance x : NonZero (tree-dim T)
             x = NonZero-subst T-dim-lem it

    ty-eq : susp-ty (tree-to-ctx S₁ ‼ getVarFin t)
                   [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
            ≈[ Γ ]ty
            unbiased-type (tree-dim T) T [ τ ]ty
    ty-eq = Ty-unique-≃ (trans≃tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (susp-tm t)) p)
                        (apply-sub-tm-typing (susp-tmTy (isVar-Ty t))
                                             (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx S₂)) σty))
                        (apply-sub-tm-typing (unbiased-comp-Ty (tree-dim T) T refl) τty)

    ty-trunc-eq : (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
                  ≈[ Γ ]ty
                  (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty
    ty-trunc-eq = begin
      (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (susp-ty-truncate (tree-to-ctx S₁ ‼ getVarFin t)) refl≃s) ⟩
      truncate 1 (susp-ty (tree-to-ctx S₁ ‼ getVarFin t))
        [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
        ≈˘⟨ reflexive≈ty (truncate-sub 1 (susp-ty (tree-to-ctx S₁ ‼ getVarFin t)) (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))) ⟩
      truncate (suc (ty-dim (sub-type σ))) (susp-ty (tree-to-ctx S₁ ‼ getVarFin t)
        [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty)
        ≈⟨ truncate-≈ {d = suc (ty-dim (sub-type σ))} refl ty-eq ⟩
      truncate (suc (ty-dim (sub-type σ)))
        (unbiased-type (tree-dim T) T [ τ ]ty)
        ≈⟨ reflexive≈ty (truncate-sub 1 (unbiased-type (tree-dim T) T) τ) ⟩
      truncate 1 (unbiased-type (tree-dim T) T) [ τ ]ty
        ≈⟨ reflexive≈ty (sub-action-≃-ty (unbiased-type-truncate-1′ (tree-dim T) T) refl≃s) ⟩
      (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty ∎
       where
        open Reasoning (ty-setoid-≈ Γ)

sub-from-insertion-fst-var : (S : Tree n)
                           → (P : Path S)
                           → .⦃ bp : is-branching-path P ⦄
                           → (T : Tree m)
                           → .⦃ lh : has-linear-height (path-length P) T ⦄
                           → {σ : Sub (suc n) l A}
                           → {τ : Sub (suc m) l A}
                           → Typing-Sub (tree-to-ctx S) Γ σ
                           → Typing-Sub (tree-to-ctx T) Γ τ
                           → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                           → Var (fromℕ _) [ sub-from-insertion S P T σ τ ]tm ≈[ Γ ]tm Var (fromℕ _) [ σ ]tm
sub-from-insertion-fst-var {Γ = Γ} (Join S₁ S₂) PHere T {σ} {τ} σty τty p = begin
  Var (fromℕ _)
    [ sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ∘ idSub≃ (connect-tree-to-ctx T S₂) ]tm
    ≈⟨ reflexive≈tm (assoc-tm _ (idSub≃ (connect-tree-to-ctx T S₂)) (Var (fromℕ _))) ⟩
  Var (fromℕ (connect-tree-length T S₂)) [ idSub≃ (connect-tree-to-ctx T S₂) ]tm
    [ sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (idSub≃-fst-var (connect-tree-to-ctx T S₂)) refl≃s) ⟩
  Var (fromℕ _) [ sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ]tm
    ≈⟨ reflexive≈tm (sub-from-connect-fst-var τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  Var (fromℕ _) [ τ ]tm
    ≈˘⟨ src-eq (sub-from-insertion-lem S₁ S₂ T 0V σty τty p) ⟩
  get-fst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-fst) ⟩
  get-fst [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-left-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
  Var (fromℕ _) [ σ ]tm ∎
  where
    open Reasoning (tm-setoid-≈ Γ)
sub-from-insertion-fst-var {Γ = Γ} (Join S₁ S₂) (PExt P) (Join T Sing) {σ} {τ} σty τty p = begin
  Var (fromℕ _) [
       sub-from-connect
       (unrestrict
        (sub-from-insertion S₁ P T
         (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
          (get-fst [ τ ]tm) (get-snd [ τ ]tm))
         (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm))))
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
       ]tm
    ≈⟨ reflexive≈tm (sub-from-connect-fst-var _ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))) ⟩
  Var (fromℕ _)
    [ unrestrict (sub-from-insertion S₁ P T
     (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (get-fst [ τ ]tm) (get-snd [ τ ]tm))
     (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))
    ]tm
    ≈⟨ reflexive≈tm (unrestrict-fst (sub-from-insertion S₁ P T _ _)) ⟩
  get-fst [ τ ]tm
    ≈˘⟨ src-eq (sub-from-insertion-lem S₁ S₂ (susp-tree T)
                                             (branching-path-to-var S₁ P)
                                             ⦃ branching-path-to-var-is-var S₁ P ⦄
                                             σty τty p) ⟩
  get-fst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-fst) ⟩
  get-fst [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-left-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
  Var (fromℕ _) [ σ ]tm ∎
  where
    open Reasoning (tm-setoid-≈ Γ)
sub-from-insertion-fst-var {Γ = Γ} (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p = reflexive≈tm (begin
  < Var (fromℕ _) [
       sub-from-connect
       (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
       (sub-from-insertion S₂ P T
        (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
       ]tm >tm
    ≈⟨ sub-from-connect-fst-var (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sub-from-insertion S₂ P T
        (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) ⟩
  < Var (fromℕ _) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm
    ≈⟨ assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm >tm
    ≈⟨ sub-action-≃-tm (connect-inc-left-fst-var get-snd (tree-size S₂)) refl≃s ⟩
  < Var (fromℕ _) [ σ ]tm >tm ∎)
  where
    open Reasoning tm-setoid

sub-from-insertion-Ty : (S : Tree n)
                      → (P : Path S)
                      → .⦃ bp : is-branching-path P ⦄
                      → (T : Tree m)
                      → .⦃ lh : has-linear-height (path-length P) T ⦄
                      → {σ : Sub (suc n) l A}
                      → {τ : Sub (suc m) l A}
                      → Typing-Sub (tree-to-ctx S) Γ σ
                      → Typing-Sub (tree-to-ctx T) Γ τ
                      → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                      → Typing-Sub (tree-to-ctx (insertion-tree S P T)) Γ (sub-from-insertion S P T σ τ)
sub-from-insertion-Ty {Γ = Γ} (Join S₁ S₂) PHere T {σ} {τ} σty τty p = apply-sub-sub-typing (idSub≃-Ty (connect-tree-to-ctx T S₂)) (sub-from-connect-Ty τty (tree-last-var-Ty T) (apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁)) σty) lem2)
  where
    lem : ((get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty)
            ≈[ Γ ]ty ((Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty)
    lem = sub-from-insertion-lem S₁ S₂ T 0V σty τty p

    lem2 : (tree-last-var T [ τ ]tm) ≈[ Γ ]tm
             (Var (fromℕ _) [ σ ∘ connect-inc-right get-snd _ ]tm)
    lem2 = begin
      tree-last-var T [ τ ]tm
        ≈˘⟨ tgt-eq lem ⟩
      get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-snd) ⟩
      get-snd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var {n = tree-size (susp-tree S₁)} get-snd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ (tree-size S₂)) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

sub-from-insertion-Ty {Γ = Γ} (Join S₁ S₂) (PExt P) (Join T Sing) {σ} {τ} σty τty p
  = sub-from-connect-Ty
      (unrestrictTy (sub-from-insertion-Ty S₁ P T
                       (restrictTy (apply-sub-sub-typing (connect-inc-left-Ty get-sndTy (tree-to-ctx S₂)) σty)
                                   (tree-to-ctx-Ty S₁)
                                   (apply-sub-tm-typing get-fstTy τty)
                                   (apply-sub-tm-typing get-sndTy τty)
                                   (sym≈tm tm-eq-1)
                                   (sym≈tm tm-eq-2))
                       (restrictTy τty
                                   (tree-to-ctx-Ty T)
                                   (apply-sub-tm-typing get-fstTy τty)
                                   (apply-sub-tm-typing get-sndTy τty)
                                   refl≈tm
                                   refl≈tm)
                       lem))
      get-sndTy
      (apply-sub-sub-typing (connect-inc-right-Ty get-sndTy) σty)
      l2
  where
    lem : branching-path-to-var S₁ P
          [ restrict (σ ∘ connect-inc-left get-snd _) (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm
          ≃tm
          unbiased-comp (tree-dim T) T
          [ restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm
    lem = begin
      < branching-path-to-var S₁ P [
        restrict (σ ∘ connect-inc-left get-snd _) (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm >tm
        ≈˘⟨ restrict-susp (branching-path-to-var S₁ P) ⦃ branching-path-to-var-is-var S₁ P ⦄ (σ ∘ connect-inc-left get-snd _) ⟩
      < susp-tm (branching-path-to-var S₁ P) [ σ ∘ connect-inc-left get-snd _ ]tm >tm
        ≈⟨ assoc-tm σ (connect-inc-left get-snd _) (susp-tm (branching-path-to-var S₁ P)) ⟩
      < susp-tm (branching-path-to-var S₁ P) [ connect-inc-left get-snd _ ]tm [ σ ]tm >tm
        ≈⟨ p ⟩
      < unbiased-comp (suc (tree-dim T)) (susp-tree T) [ τ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (unbiased-comp-susp-lem (tree-dim T) T) (refl≃s {σ = τ}) ⟩
      < susp-tm (unbiased-comp (tree-dim T) T) [ τ ]tm >tm
        ≈⟨ restrict-susp-full (unbiased-comp (tree-dim T) T) τ refl≃tm refl≃tm ⟩
      < unbiased-comp (tree-dim T) T
        [ restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm >tm ∎
      where
        open Reasoning tm-setoid

    instance _ = branching-path-to-var-is-var S₁ P

    tm-eq-1 : get-fst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              get-fst [ τ ]tm
    tm-eq-1 = src-eq (sub-from-insertion-lem S₁ S₂ (susp-tree T) (branching-path-to-var S₁ P) σty τty p)

    tm-eq-2 : get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              get-snd [ τ ]tm
    tm-eq-2 = tgt-eq (sub-from-insertion-lem S₁ S₂ (susp-tree T) (branching-path-to-var S₁ P) σty τty p)

    l2 : get-snd [ unrestrict (sub-from-insertion S₁ P T
             (restrict (σ ∘ connect-inc-left get-snd _) (get-fst [ τ ]tm)
              (get-snd [ τ ]tm))
             (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))
            ]tm
         ≈[ Γ ]tm
         (Var (fromℕ _) [ σ ∘ connect-inc-right get-snd _ ]tm)
    l2 = begin
      get-snd [ unrestrict (sub-from-insertion S₁ P T _ _) ]tm
        ≈⟨ reflexive≈tm (unrestrict-snd (sub-from-insertion S₁ P T _ _)) ⟩
      get-snd [ τ ]tm
        ≈˘⟨ tm-eq-2 ⟩
      get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-snd) ⟩
      get-snd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

sub-from-insertion-Ty {Γ = Γ} (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p
  = sub-from-connect-Ty
      (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx S₂)) σty)
      get-sndTy
      (sub-from-insertion-Ty S₂ P T σcty τty p′)
      lem
    where
      σcty = apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁)) σty
      p′ = trans≃tm (assoc-tm _ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (branching-path-to-var S₂ P)) p
      open Reasoning (tm-setoid-≈ Γ)
      lem : get-snd [ σ ∘ connect-susp-inc-left _ _ ]tm
            ≈[ Γ ]tm
            Var (fromℕ _) [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm
      lem = begin
        get-snd [ σ ∘ connect-susp-inc-left _ _ ]tm
          ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left _ _) get-snd) ⟩
        get-snd [ connect-susp-inc-left _ _ ]tm [ σ ]tm
          ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
        Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
          ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
        Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
          ≈˘⟨ sub-from-insertion-fst-var S₂ P T σcty τty p′ ⟩
        Var (fromℕ (insertion-tree-size S₂ P T))
          [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm ∎
-}

sub-from-insertion-label-lem : (S₁ : Tree n)
                             → (S₂ : Tree m)
                             → (T : Tree l)
                             → (A : Ty (suc n))
                             → (σ : Sub (suc (m + (2 + n))) o B)
                             → (τ : Sub (suc l) o B)
                             → susp-ty A [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty [ σ ]ty ≈[ Γ ]ty unbiased-type (tree-dim T) T [ τ ]ty
                             → (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
                             ≈[ Γ ]ty
                             (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty
sub-from-insertion-label-lem {B = B} S₁ S₂ T A σ τ p = begin
  (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [
    σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
    ≈˘⟨ reflexive≈ty (sub-action-≃-ty (susp-ty-truncate A) refl≃s) ⟩
  truncate 1 (susp-ty A) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
    ≈⟨ reflexive≈ty (assoc-ty _ _ (truncate 1 (susp-ty A))) ⟩
  truncate 1 (susp-ty A) [ connect-susp-inc-left _ _ ]ty [ σ ]ty
    ≈˘⟨ reflexive≈ty (sub-action-≃-ty (truncate-sub 1 (susp-ty A) (connect-susp-inc-left _ _)) refl≃s) ⟩
  truncate 1 (susp-ty A [ connect-susp-inc-left _ _ ]ty) [ σ ]ty
    ≈˘⟨ reflexive≈ty (truncate-sub 1 (susp-ty A [ connect-susp-inc-left _ _ ]ty) σ) ⟩
  truncate (1 + ty-dim (sub-type σ)) ((susp-ty A [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty) [ σ ]ty)
    ≈⟨ truncate-≈ {d = 1 + ty-dim (sub-type σ)} refl p ⟩
  truncate (1 + ty-dim (sub-type σ)) (unbiased-type (tree-dim T) T [ τ ]ty)
    ≈⟨ reflexive≈ty (truncate-sub 1 (unbiased-type (tree-dim T) T) τ) ⟩
  truncate 1 (unbiased-type (tree-dim T) T) [ τ ]ty
    ≈⟨ reflexive≈ty (sub-action-≃-ty (unbiased-type-truncate-1′ (tree-dim T) T) refl≃s) ⟩
  (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty ∎
  where
    lem : suc (ty-dim A) ≡ tree-dim T
    lem = +-cancelʳ-≡ (suc (ty-dim A)) (tree-dim T) (begin
      suc (ty-dim A) + ty-dim B
        ≡˘⟨ cong (_+ ty-dim B) (susp-dim A) ⟩
      ty-dim (susp-ty A) + ty-dim B
        ≡⟨ cong (_+ ty-dim B) (sub-dim (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (susp-ty A)) ⟩
      ty-dim (susp-ty A [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty) + ty-dim B
        ≡⟨ sub-dim′ σ (susp-ty A [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty) ⟩
      ty-dim ((susp-ty A [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty) [ σ ]ty)
        ≡⟨ ty-dim-≈ p ⟩
      ty-dim (unbiased-type (tree-dim T) T [ τ ]ty)
        ≡˘⟨ sub-dim′ τ (unbiased-type (tree-dim T) T) ⟩
      ty-dim (unbiased-type (tree-dim T) T) + ty-dim B
        ≡⟨ cong (_+ ty-dim B) (unbiased-type-dim (tree-dim T) T) ⟩
      tree-dim T + ty-dim B ∎)
      where
        open ≡-Reasoning
    instance x : NonZero (tree-dim T)
             x = NonZero-subst lem it
    open Reasoning (ty-setoid-≈ _)

sub-from-insertion-pphere : (S : Tree n)
                          → (p : BranchingPoint S)
                          → (T : Tree m)
                          → .⦃ lh : has-linear-height (bp-height p) T ⦄
                          → (L : Label X S A)
                          → (M : Label X T A)
                          → branching-path-to-type S p [ label-to-sub L ]ty ≈[ Γ ]ty unbiased-type (tree-dim T) T [ label-to-sub M ]ty
                          → apt (sub-from-insertion-label S p T L M) PPHere ≈[ Γ ]tm apt L PPHere
sub-from-insertion-pphere (Join S₁ S₂) BPHere T L M p = begin
  apt (connect-label M (label₂ L)) PPHere
    ≈⟨ reflexive≈tm (path-to-term-≃ (connect-label-pphere M (label₂ L))) ⟩
  apt M PPHere
    ≈˘⟨ reflexive≈tm (label-to-sub-ppath M PPHere) ⟩
  Var (fromℕ _) [ label-to-sub M ]tm
    ≈˘⟨ src-eq lem ⟩
  get-fst [ label-to-sub L
         ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    ≈⟨ reflexive≈tm (assoc-tm (label-to-sub L) (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-fst) ⟩
  get-fst [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
         [ label-to-sub L ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-left-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
  Var (fromℕ (tree-size S₂ + suc (suc _))) [ label-to-sub L ]tm
    ≈⟨ reflexive≈tm (label-to-sub-ppath L PPHere) ⟩
  apt L PPHere ∎
  where
    open Reasoning (tm-setoid-≈ _)
    lem : ((get-fst ─⟨ ⋆ ⟩⟶ get-snd) [
             label-to-sub L ∘
             connect-susp-inc-left (tree-size S₁) (tree-size S₂)
             ]ty)
            ≈[ _ ]ty
            ((Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ label-to-sub M ]ty)
    lem = sub-from-insertion-label-lem S₁ S₂ T (unbiased-type (tree-dim S₁) S₁) (label-to-sub L) (label-to-sub M) p
sub-from-insertion-pphere (Join S₁ S₂) (BPExt P) (Join T Sing) L M p = begin
  apt M PPHere
    ≈˘⟨ reflexive≈tm (label-to-sub-ppath M PPHere) ⟩
  Var (fromℕ (0 + (2 + _))) [ label-to-sub M ]tm
    ≈˘⟨ src-eq lem ⟩
  get-fst [ label-to-sub L
         ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
    ≈⟨ reflexive≈tm (assoc-tm (label-to-sub L) (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-fst) ⟩
  get-fst [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
         [ label-to-sub L ]tm
    ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-left-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
  Var (fromℕ (tree-size S₂ + suc (suc _))) [ label-to-sub L ]tm
    ≈⟨ reflexive≈tm (label-to-sub-ppath L PPHere) ⟩
  apt L PPHere ∎
  where
    open Reasoning (tm-setoid-≈ _)
    lem : ((get-fst ─⟨ ⋆ ⟩⟶ get-snd) [
             label-to-sub L ∘
             connect-susp-inc-left (tree-size S₁) (tree-size S₂)
             ]ty)
            ≈[ _ ]ty
            ((Var (fromℕ (0 + (2 + _))) ─⟨ ⋆ ⟩⟶ tree-last-var (Join T Sing)) [
             label-to-sub M ]ty)
    lem = sub-from-insertion-label-lem S₁ S₂ (Join T Sing) (branching-path-to-type S₁ P) (label-to-sub L) (label-to-sub M) p
sub-from-insertion-pphere (Join S₁ S₂) (BPShift P) T L M p = refl≈tm

sub-from-insertion-label-Ty : (S : Tree n)
                            → (p : BranchingPoint S)
                            → (T : Tree m)
                            → .⦃ lh : has-linear-height (bp-height p) T ⦄
                            → {L : Label (COT-to-MT ΓS) S A}
                            → Typing-Label ΓS L
                            → {M : Label (COT-to-MT ΓS) T A}
                            → Typing-Label ΓS M
                            → branching-path-to-type S p [ label-to-sub L ]ty ≈[ COT-to-Ctx ΓS ]ty unbiased-type (tree-dim T) T [ label-to-sub M ]ty
                            → Typing-Label ΓS (sub-from-insertion-label S p T L M)
sub-from-insertion-label-Ty {A = A} (Join S₁ S₂) BPHere T {L} (TyJoin tty Lty Lty′) {M} Mty p
  = connect-label-Ty Mty Lty′ l2
  where
    lem : (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ label-to-sub L ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
            ≈[ _ ]ty
          (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ label-to-sub M ]ty
    lem = sub-from-insertion-label-lem S₁ S₂ T (unbiased-type (tree-dim S₁) S₁) (label-to-sub L) (label-to-sub M) p

    l2 : apt M (last-path T) ≈[ _ ]tm apt L ⟦ PShift PHere ⟧
    l2 = begin
      apt M (last-path T)
        ≈˘⟨ reflexive≈tm (label-to-sub-ppath M (last-path T)) ⟩
      path-to-term (carrier (last-path T)) [ label-to-sub M ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (last-path-to-term T) refl≃s) ⟩
      tree-last-var T [ label-to-sub M ]tm
        ≈˘⟨ tgt-eq lem ⟩
      get-snd [ label-to-sub L
             ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm (label-to-sub L) (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-snd) ⟩
      get-snd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
             [ label-to-sub L ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var get-snd (tree-size S₂)) (refl≃s {σ = label-to-sub L})) ⟩
      Var (fromℕ (tree-size S₂)) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
                                 [ label-to-sub L ]tm
        ≈⟨ reflexive≈tm (label-to-sub-ppath L (PPShift PPHere)) ⟩
      apt L ⟦ PShift PHere ⟧ ∎
        where
        open Reasoning (tm-setoid-≈ _)
sub-from-insertion-label-Ty {A = A} (Join S₁ S₂) (BPExt P) (Join T Sing) {L} (TyJoin sty Lty Lty′) {M} (TyJoin tty Mty (TySing uty)) p
  = TyJoin tty
           (sub-from-insertion-label-Ty S₁ P T (convert-type-Ty Lty (Arr≈ l1 refl≈ty l2)) Mty lem)
           (replace-label-Ty Lty′ uty l2)
  where
    eq : (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ unrestrict (label-to-sub (label₁ L)) ]ty
           ≈[ _ ]ty
         (Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var (Join T Sing)) [ unrestrict (label-to-sub (label₁ M)) ]ty
    eq = begin
      (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ unrestrict (label-to-sub (label₁ L)) ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (refl≃ty {A = get-fst ─⟨ ⋆ ⟩⟶ get-snd}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) get-snd (label-to-sub (label₂ L)))) ⟩
      (get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ label-to-sub L ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
        ≈⟨ sub-from-insertion-label-lem S₁ S₂ (Join T Sing) (branching-path-to-type S₁ P) (label-to-sub L) (unrestrict (label-to-sub (label₁ M))) p ⟩
      (Var (fromℕ (0 + (2 + _))) ─⟨ ⋆ ⟩⟶ tree-last-var (Join T Sing)) [ unrestrict (label-to-sub (label₁ M)) ]ty ∎
      where
        open Reasoning (ty-setoid-≈ _)

    l1 : apt L PPHere ≈[ _ ]tm apt M PPHere
    l1 = begin
      apt L PPHere
        ≈˘⟨ reflexive≈tm (unrestrict-fst (label-to-sub (label₁ L))) ⟩
      get-fst [ unrestrict (label-to-sub (label₁ L)) ]tm
        ≈⟨ src-eq eq ⟩
      get-fst [ unrestrict (label-to-sub (label₁ M)) ]tm
        ≈⟨ reflexive≈tm (unrestrict-fst (label-to-sub (label₁ M))) ⟩
      apt M PPHere ∎
      where
        open Reasoning (tm-setoid-≈ _)

    l2 : apt L (PPShift PPHere) ≈[ _ ]tm apt M (PPShift PPHere)
    l2 = begin
      apt L (PPShift PPHere)
        ≈˘⟨ reflexive≈tm (unrestrict-snd (label-to-sub (label₁ L))) ⟩
      get-snd [ unrestrict (label-to-sub (label₁ L)) ]tm
        ≈⟨ tgt-eq eq ⟩
      get-snd [ unrestrict (label-to-sub (label₁ M)) ]tm
        ≈⟨ reflexive≈tm (unrestrict-snd (label-to-sub (label₁ M))) ⟩
      apt M (PPShift PPHere) ∎
      where
        open Reasoning (tm-setoid-≈ _)

    lem : (branching-path-to-type S₁ P [ label-to-sub (convert-type (label₁ L) (apt M ⟦ PHere ⟧ ─⟨ A ⟩⟶ apt M ⟦ PShift PHere ⟧)) ]ty)
            ≈[ _ ]ty
          (unbiased-type (tree-dim T) T [ label-to-sub (label₁ M) ]ty)
    lem = begin
      branching-path-to-type S₁ P [ label-to-sub (convert-type (label₁ L) (apt M ⟦ PHere ⟧ ─⟨ A ⟩⟶ apt M ⟦ PShift PHere ⟧)) ]ty
        ≈⟨ apply-sub-eq-ty (branching-path-to-type S₁ P) (label-to-sub-convert-type (label₁ L) (sym≈ty (Arr≈ l1 refl≈ty l2))) ⟩
      branching-path-to-type S₁ P [ label-to-sub (label₁ L) ]ty
        ≈˘⟨ reflexive≈ty (unrestrict-comp-ty (branching-path-to-type S₁ P) (label-to-sub (label₁ L))) ⟩
      susp-ty (branching-path-to-type S₁ P) [ unrestrict (label-to-sub (label₁ L)) ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (refl≃ty {A = susp-ty (branching-path-to-type S₁ P)}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) get-snd (label-to-sub (label₂ L)))) ⟩
      susp-ty (branching-path-to-type S₁ P)
        [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))
        ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
        ≈⟨ reflexive≈ty (assoc-ty _ _ (susp-ty (branching-path-to-type S₁ P))) ⟩
      susp-ty (branching-path-to-type S₁ P)
        [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty
        [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]ty
        ≈⟨ p ⟩
      unbiased-type (tree-dim (Join T Sing)) (Join T Sing) [ unrestrict (label-to-sub (label₁ M)) ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (unbiased-type-susp-lem (tree-dim T) T) refl≃s) ⟩
      susp-ty (unbiased-type (tree-dim T) T) [ unrestrict (label-to-sub (label₁ M)) ]ty
        ≈⟨ reflexive≈ty (unrestrict-comp-ty (unbiased-type (tree-dim T) T) (label-to-sub (label₁ M))) ⟩
      unbiased-type (tree-dim T) T [ label-to-sub (label₁ M) ]ty ∎
      where
        open Reasoning (ty-setoid-≈ _)

sub-from-insertion-label-Ty {A = A} (Join S₁ S₂) (BPShift P) T {L} (TyJoin tty Lty Lty′) {M} Mty p
  = TyJoin tty (convert-type-Ty Lty (Arr≈ refl≈tm refl≈ty (sym≈tm (sub-from-insertion-pphere S₂ P T (label₂ L) M lem)))) (sub-from-insertion-label-Ty S₂ P T Lty′ Mty lem)
  where
    open Reasoning (ty-setoid-≈ _)

    lem : branching-path-to-type S₂ P [ label-to-sub (label₂ L) ]ty
          ≈[ _ ]ty unbiased-type (tree-dim T) T [ label-to-sub M ]ty
    lem = begin
      branching-path-to-type S₂ P [ label-to-sub (label₂ L) ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (refl≃ty {A = branching-path-to-type S₂ P})
                                         (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) get-snd (label-to-sub (label₂ L)) (label-to-sub-lem L))) ⟩
      branching-path-to-type S₂ P [
        sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                         (label-to-sub (label₂ L))
        ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]ty
        ≈⟨ reflexive≈ty (assoc-ty _ _ (branching-path-to-type S₂ P)) ⟩
      branching-path-to-type S₂ P
        [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]ty
        [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                           (label-to-sub (label₂ L)) ]ty
        ≈⟨ p ⟩
      unbiased-type (tree-dim T) T [ label-to-sub M ]ty ∎

sub-from-insertion-Ty : (S : Tree n)
                      → (p : BranchingPoint S)
                      → (T : Tree m)
                      → .⦃ lh : has-linear-height (bp-height p) T ⦄
                      → {σ : Sub (suc n) l A}
                      → {τ : Sub (suc m) l A}
                      → Typing-Sub (tree-to-ctx S) Γ σ
                      → Typing-Sub (tree-to-ctx T) Γ τ
                      → branching-path-to-var S p [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                      → Typing-Sub (tree-to-ctx (insertion-tree S p T)) Γ (sub-from-insertion S p T σ τ)
sub-from-insertion-Ty {A = A} S P T {σ} {τ} σty τty p
  = label-to-sub-Ty (sub-from-insertion-label-Ty S P T
                                                 (to-label-Ty S (incCtx _) σty)
                                                 (to-label-Ty T (incCtx _) τty)
                                                 lem)
                    (sub-typing-implies-ty-typing σty)
    where
      open Reasoning tm-setoid
      lem-≃ : branching-path-to-var S P [ label-to-sub (to-label S σ (Other _)) ]tm
          ≃tm unbiased-comp (tree-dim T) T [ label-to-sub (to-label T τ (Other _)) ]tm
      lem-≃ = begin
        < branching-path-to-var S P [ label-to-sub (to-label S σ (Other _)) ]tm >tm
          ≈⟨ sub-action-≃-tm (refl≃tm {s = branching-path-to-var S P}) (sub-to-label-to-sub S σ (Other _)) ⟩
        < branching-path-to-var S P [ σ ]tm >tm
          ≈⟨ p ⟩
        < unbiased-comp (tree-dim T) T [ τ ]tm >tm
          ≈˘⟨ sub-action-≃-tm (refl≃tm {s = unbiased-comp (tree-dim T) T}) (sub-to-label-to-sub T τ (Other _)) ⟩
        < unbiased-comp (tree-dim T) T [ label-to-sub (to-label T τ (Other _)) ]tm >tm ∎

      lem : (branching-path-to-type S P [ label-to-sub (to-label S σ _) ]ty)
              ≈[ _ ]ty
            (unbiased-type (tree-dim T) T [ label-to-sub (to-label T τ (Other _)) ]ty)
      lem = Ty-unique-≃ lem-≃
                        (apply-sub-tm-typing (branching-path-to-var-Ty S P)
                                             (transport-typing-sub σty refl≃c refl≃c (sym≃s (sub-to-label-to-sub S σ (Other _)))))
                        (apply-sub-tm-typing (unbiased-comp-Ty (tree-dim T)
                                                               ⦃ NonZero-subst (insertion-dim-lem S P T σty τty p)
                                                                               (height-of-branching-non-zero S P) ⦄
                                                               T
                                                               refl)
                                             (transport-typing-sub τty refl≃c refl≃c (sym≃s (sub-to-label-to-sub T τ (Other _)))))

interior-sub-label-comm : (S : Tree n)
                        → (P : BranchingPoint S)
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (bp-height P) T ⦄
                        → (L : Label (COT-to-MT ΓS) S A)
                        → (M : Label (COT-to-MT ΓS) T A)
                        → label-comp (interior-sub-label S P T) (sub-from-insertion-label S P T L M) ≃lm M
interior-sub-label-comm (Join S₁ S₂) BPHere T L M ⟦ Q ⟧ = connect-label-inc-left M (label₂ L) ⟦ Q ⟧
interior-sub-label-comm (Join S₁ S₂) (BPExt P) (Join T Sing) L M ⟦ PExt Q ⟧ = interior-sub-label-comm S₁ P T (convert-type (label₁ L) (apt M PPHere ─⟨ _ ⟩⟶ apt M (PPShift PPHere))) (label₁ M) ⟦ Q ⟧
interior-sub-label-comm (Join S₁ S₂) (BPExt P) (Join T Sing) L M ⟦ PShift PHere ⟧ = ⊥-elim (proj₁ it)
interior-sub-label-comm (Join S₁ S₂) (BPExt P) (Join T Sing) L M ⟦ PShift (POther x) ⟧ = ⊥-elim (proj₂ it)
interior-sub-label-comm (Join S₁ S₂) (BPShift P) T L M ⟦ Q ⟧ = interior-sub-label-comm S₂ P T (label₂ L) M ⟦ Q ⟧

exterior-sub-label-comm : (S : Tree n)
                        → (P : BranchingPoint S)
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (bp-height P) T ⦄
                        → (L : Label (COT-to-MT ΓS) S A)
                        → (M : Label (COT-to-MT ΓS) T A)
                        → label-comp (exterior-sub-label S P T) (sub-from-insertion-label S P T L M) ≃lm L
exterior-sub-label-comm (Join S₁ S₂) BPHere T L M ⟦ PExt Q ⟧ = {!!}
exterior-sub-label-comm (Join S₁ S₂) BPHere T L M ⟦ PShift Q ⟧ = {!!}
exterior-sub-label-comm (Join S₁ S₂) (BPExt P) (Join T Sing) L M ⟦ PExt Q ⟧ = exterior-sub-label-comm S₁ P T (convert-type (label₁ L) (apt M PPHere ─⟨ _ ⟩⟶ apt M (PPShift PPHere))) (label₁ M) ⟦ Q ⟧
exterior-sub-label-comm (Join S₁ S₂) (BPExt P) (Join T Sing) L M ⟦ PShift Q ⟧ = trans≃tm (path-to-term-≃ {!extend-ppath ⟦ Q ⟧ (label₂ (sub-from-insertion-label (Join S₁ S₂) (BPExt P) (Join T Sing) L M))!}) {!!}
exterior-sub-label-comm (Join S₁ S₂) (BPShift P) T L M ⟦ PExt Q ⟧ = path-to-term-≃ (extend-ppath ⟦ Q ⟧ (label₁ (sub-from-insertion-label (Join S₁ S₂) (BPShift P) T L M)))
exterior-sub-label-comm (Join S₁ S₂) (BPShift P) T L M ⟦ PShift Q ⟧ = exterior-sub-label-comm S₂ P T (label₂ L) M ⟦ Q ⟧ ⦃ proj₂ it ⦄

{-
-- interior-sub-label-comm : (S : Tree n)
--                         → (P : BranchingPoint S)
--                         → (T : Tree m)
--                         → .⦃ lh : has-linear-height (bp-height P) T ⦄
--                         → (L : Label (COT-to-MT ΓS) S)
--                         → (M : Label (COT-to-MT ΓS) T)
--                         → (Q : PPath T) → .⦃ is-Maximal Q ⦄ → path-to-term ((sub-from-insertion-label S P T L M ‼< A > (interior-sub-func S P T Q))) ≃tm path-to-term (M ‼< A > carrier Q)
-- interior-sub-label-comm (Join S₁ S₂) BPHere T (LJoin P L L′) M ⟦ Z ⟧ = connect-label-inc-left M L′ ⟦ Z ⟧
-- interior-sub-label-comm (Join S₁ S₂) (BPExt p) (Join T Sing) (LJoin P L L′) (LJoin Q M (LSing R)) ⟦ PExt Z ⟧ = trans≃tm (path-to-term-≃ (‼<>-≃ refl≃l (Arr≃ refl≃tm refl≃ty (replace-first-label L′ R)) (refl≃p {P = interior-sub-func S₁ p T ⟦ Z ⟧}))) (interior-sub-label-comm S₁ p T L M ⟦ Z ⟧)
-- interior-sub-label-comm (Join S₁ S₂) (BPExt p) (Join T Sing) (LJoin P L L′) (LJoin Q M (LSing R)) ⟦ PShift PHere ⟧ = ⊥-elim (proj₁ it)
-- interior-sub-label-comm (Join S₁ S₂) (BPExt p) (Join T Sing) (LJoin P L L′) (LJoin Q M (LSing R)) ⟦ PShift (POther x) ⟧ = ⊥-elim (proj₂ it)
-- interior-sub-label-comm (Join S₁ S₂) (BPShift p) T (LJoin P L L′) M Z = interior-sub-label-comm S₂ p T L′ M Z


-- interior-sub-comm : (S : Tree n)
--                   → (P : BranchingPoint S)
--                   → (T : Tree m)
--                   → .⦃ lh : has-linear-height (bp-height P) T ⦄
--                   → {σ : Sub (suc n) l A}
--                   → {τ : Sub (suc m) l A}
--                   → Typing-Sub (tree-to-ctx S) Γ σ
--                   → Typing-Sub (tree-to-ctx T) Γ τ
--                   → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
--                   → sub-from-insertion S P T σ τ ∘ interior-sub S P T ≈[ Γ ]s τ
-- interior-sub-comm S P T σty τty p = {!!}

-- exterior-sub-label-comm : (S : Tree n)
--                         → (P : BranchingPoint S)
--                         → (T : Tree m)
--                         → .⦃ _ : has-linear-height (bp-height P) T ⦄
--                         → (L : Label (COT-to-MT ΓS) S)
--                         → (M : Label (COT-to-MT ΓS) T)
--                         → path-to-term (L ‼< A > carrier (branching-path-to-path S P)) ≃tm unbiased-comp (tree-dim T) T [ label-to-sub M A ]tm
--                         → (Q : PPath S) → .⦃ is-Maximal Q ⦄ → path-to-term (sub-from-insertion-label S P T L M ‼< A > exterior-sub-func S P T Q) ≃tm path-to-term (L ‼< A > carrier Q)
-- exterior-sub-label-comm (Join S₁ S₂) BPHere T (LJoin R L L′) M p ⟦ PExt Z ⟧ = {!!}
-- exterior-sub-label-comm (Join S₁ S₂) BPHere T (LJoin R L L′) M p ⟦ PShift Z ⟧ = {!!}
-- exterior-sub-label-comm (Join S₁ S₂) (BPExt P) (Join T Sing) (LJoin Q L L′) (LJoin R M (LSing R′)) p ⟦ PExt Z ⟧ = trans≃tm (exterior-sub-label-comm S₁ P T L M {!!} ⟦ Z ⟧) (path-to-term-≃ (‼-ppath L ⟦ Z ⟧))
-- exterior-sub-label-comm (Join S₁ S₂) (BPExt P) (Join T Sing) (LJoin Q L L′) (LJoin R M (LSing R′)) p ⟦ PShift Z ⟧ = path-to-term-≃ (replace-not-here L′ R′ ⟦ Z ⟧ ⦃ proj₁ it ⦄)
-- exterior-sub-label-comm (Join S₁ S₂) (BPShift P) T (LJoin Q L L′) M p ⟦ PExt Z ⟧ = path-to-term-≃ (‼-ppath L ⟦ Z ⟧)
-- exterior-sub-label-comm (Join S₁ S₂) (BPShift P) T (LJoin Q L L′) M p ⟦ PShift Z ⟧ = exterior-sub-label-comm S₂ P T L′ M p ⟦ Z ⟧ ⦃ proj₂ it ⦄



{-
interior-sub-comm : (S : Tree n)
                   → (P : Path S)
                   → .⦃ bp : is-branching-path P ⦄
                   → (T : Tree m)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → {σ : Sub (suc n) l A}
                   → {τ : Sub (suc m) l A}
                   → Typing-Sub (tree-to-ctx S) Γ σ
                   → Typing-Sub (tree-to-ctx T) Γ τ
                   → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                   → sub-from-insertion S P T σ τ ∘ interior-sub S P T ≈[ Γ ]s τ
interior-sub-comm {Γ = Γ} (Join S₁ S₂) PHere T {σ} {τ} σty τty p = reflexive≈s (begin
  < sub-from-insertion (Join S₁ S₂) PHere T σ τ ∘ interior-sub (Join S₁ S₂) PHere T >s ≡⟨⟩
  < sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ idSub≃ (connect-tree-to-ctx T S₂)
    ∘ (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) (tree-size S₂)) >s
    ≈⟨ sub-action-≃-sub (idSub≃-on-sub (sym≃c (connect-tree-to-ctx T S₂)) (connect-inc-left (tree-last-var T) _)) (idSub≃-right-unit (connect-tree-to-ctx T S₂) _) ⟩
  < sub-from-connect τ (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ connect-inc-left (tree-last-var T) (tree-size S₂) >s
    ≈⟨ sub-from-connect-inc-left τ (tree-last-var T) (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ⟩
  < τ >s ∎)
  where
    open Reasoning sub-setoid

interior-sub-comm {Γ = Γ} (Join S₁ S₂) (PExt P) (Join T Sing) {σ} {τ} σty τty p = begin
  < sub-from-connect (unrestrict (sub-from-insertion S₁ P T
    (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (get-fst [ τ ]tm) (get-snd [ τ ]tm))
    (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm))))
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
  ∘ (connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)
    ∘ susp-sub (interior-sub S₁ P T)) >s′
    ≈˘⟨ reflexive≈s (∘-assoc _ _ _) ⟩
  < sub-from-connect (unrestrict (sub-from-insertion S₁ P T
    (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (get-fst [ τ ]tm) (get-snd [ τ ]tm))
    (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm))))
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂)
    ∘ susp-sub (interior-sub S₁ P T) >s′
    ≈⟨ reflexive≈s (sub-action-≃-sub refl≃s (sub-from-connect-inc-left (unrestrict (sub-from-insertion S₁ P T
    (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (get-fst [ τ ]tm) (get-snd [ τ ]tm))
    (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))) get-snd (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < unrestrict (sub-from-insertion S₁ P T
      (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                (get-fst [ τ ]tm)
                (get-snd [ τ ]tm))
      (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))
    ∘ susp-sub (interior-sub S₁ P T) >s′
    ≈˘⟨ reflexive≈s (unrestrict-comp _ _) ⟩
  < unrestrict (sub-from-insertion S₁ P T
       (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                 (get-fst [ τ ]tm)
                 (get-snd [ τ ]tm))
       (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm))
     ∘ interior-sub S₁ P T) >s′
    ≈⟨ unrestrictEq (interior-sub-comm S₁ P T
                      (restrictTy (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx S₂)) σty)
                                  (tree-to-ctx-Ty S₁)
                                  (apply-sub-tm-typing get-fstTy τty)
                                  (apply-sub-tm-typing get-sndTy τty)
                                  (sym≈tm tm-eq-1)
                                  (sym≈tm tm-eq-2))
                      (restrictTy τty
                                  (tree-to-ctx-Ty T)
                                  (apply-sub-tm-typing get-fstTy τty)
                                  (apply-sub-tm-typing get-sndTy τty)
                                  refl≈tm
                                  refl≈tm)
                      lem) ⟩
  < unrestrict (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)) >s′
    ≈⟨ reflexive≈s (unrestrict-restrict-≃ τ refl≃tm refl≃tm) ⟩
  < τ >s′ ∎
  where
    lem : branching-path-to-var S₁ P
          [ restrict (σ ∘ connect-inc-left get-snd _) (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm
          ≃tm
          unbiased-comp (tree-dim T) T
          [ restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm
    lem = begin
      < branching-path-to-var S₁ P [
        restrict (σ ∘ connect-inc-left get-snd _) (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm >tm
        ≈˘⟨ restrict-susp (branching-path-to-var S₁ P) ⦃ branching-path-to-var-is-var S₁ P ⦄ (σ ∘ connect-inc-left get-snd _) ⟩
      < susp-tm (branching-path-to-var S₁ P) [ σ ∘ connect-inc-left get-snd _ ]tm >tm
        ≈⟨ assoc-tm σ (connect-inc-left get-snd _) (susp-tm (branching-path-to-var S₁ P)) ⟩
      < susp-tm (branching-path-to-var S₁ P) [ connect-inc-left get-snd _ ]tm [ σ ]tm >tm
        ≈⟨ p ⟩
      < unbiased-comp (tree-dim (susp-tree T)) (susp-tree T) [ τ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (unbiased-comp-susp-lem (tree-dim T) T) (refl≃s {σ = τ}) ⟩
      < susp-tm (unbiased-comp (tree-dim T) T) [ τ ]tm >tm
        ≈⟨ restrict-susp-full (unbiased-comp (tree-dim T) T) τ refl≃tm refl≃tm ⟩
      < unbiased-comp (tree-dim T) T
        [ restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm >tm ∎
      where
        open Reasoning tm-setoid
    instance _ = branching-path-to-var-is-var S₁ P
    tm-eq-1 : get-fst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              get-fst [ τ ]tm
    tm-eq-1 = src-eq (sub-from-insertion-lem S₁ S₂ (susp-tree T) (branching-path-to-var S₁ P) σty τty p)

    tm-eq-2 : get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              get-snd [ τ ]tm
    tm-eq-2 = tgt-eq (sub-from-insertion-lem S₁ S₂ (susp-tree T) (branching-path-to-var S₁ P) σty τty p)

    open Reasoning (sub-setoid-≈ (suc (tree-size (susp-tree T))) Γ)

interior-sub-comm {Γ = Γ} (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p = begin
  < sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
    ∘ (connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ∘ interior-sub S₂ P T) >s′
    ≈˘⟨ reflexive≈s (∘-assoc _ _ _) ⟩
  < sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)
    ∘ connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T)
    ∘ interior-sub S₂ P T >s′
    ≈⟨ apply-sub-eq-sub (interior-sub S₂ P T) (sub-from-connect-inc-right-≈ _ _ _ lem) ⟩
  < sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ∘ interior-sub S₂ P T >s′
    ≈⟨ interior-sub-comm S₂ P T (apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁)) σty) τty (trans≃tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (branching-path-to-var S₂ P)) p) ⟩
  < τ >s′ ∎
  where
    lem : get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
          ≈[ Γ ]tm
          Var (fromℕ _) [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm
    lem = begin
      get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-snd) ⟩
      get-snd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
        ≈˘⟨ sub-from-insertion-fst-var S₂ P T (apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁)) σty) τty (trans≃tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (branching-path-to-var S₂ P)) p) ⟩
      Var (fromℕ _) [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    open Reasoning (sub-setoid-≈ (suc (tree-size T)) Γ)

exterior-sub-comm : (S : Tree n)
                  → (P : Path S)
                  → .⦃ _ : is-branching-path P ⦄
                  → (T : Tree m)
                  → .⦃ _ : has-linear-height (path-length P) T ⦄
                  → {σ : Sub (suc n) l A}
                  → {τ : Sub (suc m) l A}
                  → Typing-Sub (tree-to-ctx S) Γ σ
                  → Typing-Sub (tree-to-ctx T) Γ τ
                  → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
                  → sub-from-insertion S P T σ τ ∘ exterior-sub S P T ≈[ Γ ]s σ
exterior-sub-comm {Γ = Γ} (Join S₁ S₂) PHere T {σ} {τ} σty τty p = begin
  < sub-from-connect τ
       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
       ∘ idSub≃ (connect-tree-to-ctx T S₂)
       ∘ (idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘
         sub-between-connects
         (sub-from-linear-tree-unbiased (susp-tree S₁) T 0)
         idSub (tree-last-var T)) >s′
    ≈⟨ reflexive≈s (sub-action-≃-sub (idSub≃-on-sub _ _) (idSub≃-right-unit _ _)) ⟩
  < sub-from-connect τ
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
      ∘ sub-between-connects
         (sub-from-linear-tree-unbiased (susp-tree S₁) T 0)
         idSub (tree-last-var T) >s′
    ≈⟨ between-connect-from-connect-≈ (sub-from-linear-tree-unbiased (susp-tree S₁) T 0)
                                      idSub
                                      (tree-last-var T)
                                      τ
                                      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                                      lem2 ⟩
  < sub-from-connect
      (τ ∘ sub-from-linear-tree-unbiased (susp-tree S₁) T 0)
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ∘ idSub) >s′
    ≈⟨ sub-from-connect-≈ l1 (reflexive≈s (id-right-unit (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < sub-from-connect
      (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s′
    ≈⟨ reflexive≈s (sub-from-connect-prop′ get-snd (tree-size S₂) σ) ⟩
  < σ >s′ ∎

  where
    lem : ((get-fst ─⟨ ⋆ ⟩⟶ get-snd) [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]ty)
            ≈[ Γ ]ty ((Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T) [ τ ]ty)
    lem = sub-from-insertion-lem S₁ S₂ T 0V σty τty p

    lem2 : (tree-last-var T [ τ ]tm) ≈[ Γ ]tm
             (Var (fromℕ _) [ σ ∘ connect-inc-right get-snd _ ]tm)
    lem2 = begin
      tree-last-var T [ τ ]tm
        ≈˘⟨ tgt-eq lem ⟩
      get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-snd) ⟩
      get-snd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var {n = tree-size (susp-tree S₁)} get-snd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ (tree-size S₂)) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    dim-lem : tree-dim (susp-tree S₁) ≡ tree-dim T
    dim-lem = insertion-dim-lem (Join S₁ S₂) PHere T σty τty p

    l2 : (0V [ τ ∘ sub-from-linear-tree-unbiased (susp-tree S₁) T 0 ]tm)
           ≃tm (0V [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm)
    l2 = begin
      < 0V [ τ ∘ sub-from-linear-tree-unbiased (susp-tree S₁) T 0 ]tm >tm
        ≈⟨ assoc-tm τ (sub-from-linear-tree-unbiased (susp-tree S₁) T 0) 0V ⟩
      < 0V [ sub-from-linear-tree-unbiased (susp-tree S₁) T 0 ]tm
           [ τ ]tm >tm
        ≈⟨ sub-action-≃-tm (sub-from-linear-tree-unbiased-0V (susp-tree S₁) T 0) refl≃s ⟩
      < unbiased-comp (tree-dim (susp-tree S₁)) T [ τ ]tm >tm
        ≈⟨ sub-action-≃-tm (unbiased-comp-≃ dim-lem (refl≃ {T = T})) (refl≃s {σ = τ}) ⟩
      < unbiased-comp (tree-dim T) T [ τ ]tm >tm
        ≈˘⟨ p ⟩
      < 0V [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
           [ σ ]tm >tm
        ≈˘⟨ assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) 0V ⟩
      < 0V [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l1 : τ ∘ (sub-from-linear-tree-unbiased (susp-tree S₁) T 0)
         ≈[ Γ ]s σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)
    l1 = begin
      < τ ∘ sub-from-linear-tree-unbiased (susp-tree S₁) T 0 >s′
        ≈⟨ sub-from-linear-Eq (susp-tree S₁)
                              (apply-sub-sub-typing (sub-from-linear-tree-unbiased-Ty-0 (susp-tree S₁) T ⦃ NonZero-subst dim-lem it ⦄ (sym dim-lem)) τty)
                              (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx S₂)) σty)
                              l2 ⟩
      < σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) >s′ ∎
      where
        open Reasoning (sub-setoid-≈ (suc (tree-size (susp-tree S₁))) Γ)

    open Reasoning (sub-setoid-≈ (suc (tree-size (Join S₁ S₂))) Γ)

exterior-sub-comm {Γ = Γ} (Join S₁ S₂) (PExt P) (Join T Sing) {σ = σ} {τ} σty τty p = begin
  < sub-from-connect
    (unrestrict
      (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (get-fst [ τ ]tm)
                  (get-snd [ τ ]tm))
        (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm))))
    (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
    ∘ sub-between-connect-susps (exterior-sub S₁ P T) idSub >s′
    ≈⟨ between-connect-from-connect-≈ (susp-sub (exterior-sub S₁ P T)) idSub get-snd (unrestrict
      (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (get-fst [ τ ]tm)
                  (get-snd [ τ ]tm))
        (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))) (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) l2 ⟩
  < sub-from-connect
    (unrestrict
      (sub-from-insertion S₁ P T
        (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                  (get-fst [ τ ]tm)
                  (get-snd [ τ ]tm))
        (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))
      ∘ susp-sub (exterior-sub S₁ P T))
    (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ∘ idSub) >s′
    ≈⟨ sub-from-connect-≈ l3 (reflexive≈s (id-right-unit (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)))) ⟩
  < sub-from-connect
    (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s′
    ≈⟨ reflexive≈s (sub-from-connect-prop′ get-snd (tree-size S₂) σ) ⟩
  < σ >s′ ∎
  where
    lem : branching-path-to-var S₁ P
          [ restrict (σ ∘ connect-inc-left get-snd _) (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm
          ≃tm
          unbiased-comp (tree-dim T) T
          [ restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm
    lem = begin
      < branching-path-to-var S₁ P [
        restrict (σ ∘ connect-inc-left get-snd _) (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm >tm
        ≈˘⟨ restrict-susp (branching-path-to-var S₁ P) ⦃ branching-path-to-var-is-var S₁ P ⦄ (σ ∘ connect-inc-left get-snd _) ⟩
      < susp-tm (branching-path-to-var S₁ P) [ σ ∘ connect-inc-left get-snd _ ]tm >tm
        ≈⟨ assoc-tm σ (connect-inc-left get-snd _) (susp-tm (branching-path-to-var S₁ P)) ⟩
      < susp-tm (branching-path-to-var S₁ P) [ connect-inc-left get-snd _ ]tm [ σ ]tm >tm
        ≈⟨ p ⟩
      < unbiased-comp (tree-dim (susp-tree T)) (susp-tree T) [ τ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (Coh≃ refl≃c (unbiased-type-susp-lem (tree-dim T) T) susp-functorial-id) (refl≃s {σ = τ}) ⟩
      < susp-tm (unbiased-comp (tree-dim T) T) [ τ ]tm >tm
        ≈⟨ restrict-susp-full (unbiased-comp (tree-dim T) T) τ refl≃tm refl≃tm ⟩
      < unbiased-comp (tree-dim T) T
        [ restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm) ]tm >tm ∎
      where
        open Reasoning tm-setoid

    instance _ = branching-path-to-var-is-var S₁ P

    tm-eq-1 : get-fst [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              get-fst [ τ ]tm
    tm-eq-1 = src-eq (sub-from-insertion-lem S₁ S₂ (susp-tree T) (branching-path-to-var S₁ P) σty τty p)

    tm-eq-2 : get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
              ≈[ Γ ]tm
              get-snd [ τ ]tm
    tm-eq-2 = tgt-eq (sub-from-insertion-lem S₁ S₂ (susp-tree T) (branching-path-to-var S₁ P) σty τty p)

    l2 : get-snd [ unrestrict (sub-from-insertion S₁ P T
             (restrict (σ ∘ connect-inc-left get-snd _) (get-fst [ τ ]tm)
              (get-snd [ τ ]tm))
             (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))
            ]tm
         ≈[ Γ ]tm
         (Var (fromℕ _) [ σ ∘ connect-inc-right get-snd _ ]tm)
    l2 = begin
      get-snd [ unrestrict (sub-from-insertion S₁ P T _ _) ]tm
        ≈⟨ reflexive≈tm (unrestrict-snd (sub-from-insertion S₁ P T _ _)) ⟩
      get-snd [ τ ]tm
        ≈˘⟨ tm-eq-2 ⟩
      get-snd [ σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left (tree-size S₁) (tree-size S₂)) get-snd) ⟩
      get-snd [ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    l3 : (unrestrict
            (sub-from-insertion S₁ P T
             (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
              (get-fst [ τ ]tm) (get-snd [ τ ]tm))
             (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))
            ∘ susp-sub (exterior-sub S₁ P T))
           ≈[ Γ ]s (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    l3 = begin
      < unrestrict
        (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (get-fst [ τ ]tm)
                    (get-snd [ τ ]tm))
          (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm)))
        ∘ susp-sub (exterior-sub S₁ P T) >s′
        ≈˘⟨ reflexive≈s (unrestrict-comp _ _) ⟩
      < unrestrict
        (sub-from-insertion S₁ P T
          (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                    (get-fst [ τ ]tm)
                    (get-snd [ τ ]tm))
          (restrict τ (get-fst [ τ ]tm) (get-snd [ τ ]tm))
         ∘ exterior-sub S₁ P T) >s′
        ≈⟨ unrestrictEq (exterior-sub-comm S₁ P T
             (restrictTy (apply-sub-sub-typing (connect-susp-inc-left-Ty (tree-to-ctx S₂)) σty)
                         (tree-to-ctx-Ty S₁)
                         (apply-sub-tm-typing get-fstTy τty)
                         (apply-sub-tm-typing get-sndTy τty)
                         (sym≈tm tm-eq-1)
                         (sym≈tm tm-eq-2))
             (restrictTy τty
                         (tree-to-ctx-Ty T)
                         (apply-sub-tm-typing get-fstTy τty)
                         (apply-sub-tm-typing get-sndTy τty)
                         refl≈tm
                         refl≈tm)
             lem) ⟩
      < unrestrict (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (get-fst [ τ ]tm) (get-snd [ τ ]tm)) >s′
        ≈⟨ unrestrict-restrict-≈ (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sym≈tm tm-eq-1) (sym≈tm tm-eq-2) ⟩
      < σ ∘ connect-inc-left get-snd _ >s′ ∎
      where
        open Reasoning (sub-setoid-≈ (suc (tree-size (susp-tree S₁))) Γ)

    open Reasoning (sub-setoid-≈ (suc (tree-size (Join S₁ S₂))) Γ)

exterior-sub-comm {Γ = Γ} (Join S₁ S₂) (PShift P) T {σ} {τ} σty τty p = begin
  < sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (sub-from-insertion S₂ P T
                       (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
                       τ)
    ∘ sub-between-connect-susps idSub (exterior-sub S₂ P T) >s′
    ≈⟨ between-connect-from-connect-≈ (susp-sub idSub) (exterior-sub S₂ P T) get-snd (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ) lem ⟩
  < sub-from-connect
    (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ∘ susp-sub idSub)
    (sub-from-insertion S₂ P T
      (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ
    ∘ exterior-sub S₂ P T) >s′
    ≈⟨ sub-from-connect-≈ (reflexive≈s l1) (exterior-sub-comm S₂ P T σcty τty p′) ⟩
  < sub-from-connect
    (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) >s′
    ≈⟨ reflexive≈s (sub-from-connect-prop′ get-snd (tree-size S₂) σ) ⟩
  < σ >s′ ∎
  where
    σcty = apply-sub-sub-typing (connect-susp-inc-right-Ty (tree-to-ctx S₁)) σty
    p′ = trans≃tm (assoc-tm _ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (branching-path-to-var S₂ P)) p

    lem : get-snd [ σ ∘ connect-susp-inc-left _ _ ]tm
            ≈[ Γ ]tm
            Var (fromℕ _) [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm
    lem = begin
      get-snd [ σ ∘ connect-susp-inc-left _ _ ]tm
        ≈⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-left _ _) get-snd) ⟩
      get-snd [ connect-susp-inc-left _ _ ]tm [ σ ]tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (connect-inc-fst-var get-snd (tree-size S₂)) refl≃s) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm [ σ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm σ (connect-susp-inc-right (tree-size S₁) (tree-size S₂)) (Var (fromℕ _))) ⟩
      Var (fromℕ _) [ σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm
        ≈˘⟨ sub-from-insertion-fst-var S₂ P T σcty τty p′ ⟩
      Var (fromℕ (insertion-tree-size S₂ P T))
        [ sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ ]tm ∎
        where
          open Reasoning (tm-setoid-≈ Γ)

    l1 : (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ∘
            susp-sub idSub)
      ≃s (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
    l1 = begin
      < σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ∘ susp-sub idSub >s
        ≈⟨ sub-action-≃-sub susp-functorial-id refl≃s ⟩
      < σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) ∘ idSub >s
        ≈⟨ id-right-unit (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) ⟩
      < σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂) >s ∎
      where
        open Reasoning sub-setoid

    open Reasoning (sub-setoid-≈ (suc (tree-size (Join S₁ S₂))) Γ)

exterior-sub-label-Ty : (S : Tree n)
                      → (P : Path S)
                      → .⦃ _ : is-branching-path P ⦄
                      → (T : Tree m)
                      → .⦃ _ : has-linear-height (path-length P) T ⦄
                      → .⦃ p : height-of-branching P ≡ tree-dim T ⦄
                      → Typing-Label (tree-to-ctx (insertion-tree S P T)) (exterior-sub-label S P T) ⋆
exterior-sub-label-Ty (Join S₁ S₂) PHere T
  = label-between-connect-trees-Ty T
                                   S₂
                                   (to-label-Ty (susp-tree S₁) (sub-from-linear-tree-unbiased-Ty-0 (susp-tree S₁) T ⦃ NonZero-subst it it ⦄ (sym it)))
                                   (id-label-Ty S₂)
                                   (reflexive≈tm (unrestrict-snd (sub-from-linear-tree-unbiased S₁ T 1)))
                                   (reflexive≈tm (id-first-label S₂))
exterior-sub-label-Ty (Join S₁ S₂) (PExt P) (Join T Sing)
  = label-between-joins-Ty (insertion-tree S₁ P T)
                           S₂
                           (exterior-sub-label-Ty S₁ P T ⦃ p = cong pred it ⦄)
                           (id-label-Ty S₂)
                           (reflexive≈tm (id-first-label S₂))
exterior-sub-label-Ty (Join S₁ S₂) (PShift P) T
  = label-between-joins-Ty S₁
                           (insertion-tree S₂ P T)
                           (id-label-Ty S₁)
                           (exterior-sub-label-Ty S₂ P T)
                           (reflexive≈tm (exterior-sub-first-label S₂ P T))

-- exterior-sub-label-comm-lem : (S : Tree n)
--                             → (P : Path S)
--                             → .⦃ _ : is-branching-path P ⦄
--                             → (T : Tree m)
--                             → .⦃ _ : has-linear-height (path-length P) T ⦄
--                             → {σ : Label l S}
--                             → {τ : Label l T}
--                             → Typing-Label Γ σ A
--                             → Typing-Label Γ τ A
--                             → branching-path-to-var S P [ label-to-sub σ A ]tm ≃tm unbiased-comp (tree-dim T) T [ label-to-sub τ A ]tm
--                             → Same-Leaves (exterior-sub-label S P T [ label-to-sub (sub-from-insertion-label-helper S P T σ τ) A ]l) σ
-- exterior-sub-label-comm-lem S P T {σ} σty τty p Q = begin
--   < (exterior-sub-label S P T [ label-to-sub (sub-from-insertion-label-helper S P T _ _) _ ]l) ‼l Q >tm
--     ≈⟨ ‼l-comp (exterior-sub-label S P T) Q (label-to-sub (sub-from-insertion-label-helper S P T _ _) _) ⟩
--   < exterior-sub-label S P T ‼l Q [ label-to-sub (sub-from-insertion-label-helper S P T _ _) _ ]tm >tm
--     ≈⟨ lem S P T σty τty p Q ⟩
--   < σ ‼l Q >tm ∎
--   where
--     open Reasoning tm-setoid

--     lem : (S : Tree n)
--         → (P : Path S)
--         → .⦃ _ : is-branching-path P ⦄
--         → (T : Tree m)
--         → .⦃ _ : has-linear-height (path-length P) T ⦄
--         → {σ : Label l S}
--         → {τ : Label l T}
--         → Typing-Label Γ σ A
--         → Typing-Label Γ τ A
--         → branching-path-to-var S P [ label-to-sub σ A ]tm ≃tm unbiased-comp (tree-dim T) T [ label-to-sub τ A ]tm
--         → (Q : Path S)
--         → .⦃ is-Maximal Q ⦄
--         → exterior-sub-label S P T ‼l Q [ label-to-sub (sub-from-insertion-label-helper S P T σ τ) A ]tm ≃tm σ ‼l Q
--     lem (Join S₁ S₂) PHere T {σ = LJoin x σ σ′} {τ} (TyJoin xty σty σty′) τty p Q = {!!}
--     lem (Join S₁ S₂) (PExt P) (Join T Sing) {LJoin x σ σ′} {LJoin y τ (LSing z)} (TyJoin xty σty σty′) (TyJoin yty τty (TySing zty)) p (PExt Q) = {!!}
--     lem (Join S₁ S₂) (PExt P) (Join T Sing) {LJoin x σ σ′} {LJoin y τ (LSing z)} (TyJoin xty σty σty′) (TyJoin yty τty (TySing zty)) p (PShift Q) = {!!}
--       where
--         l1 : exterior-sub-label (Join S₁ S₂) (PExt P) (Join T Sing) ‼l PShift Q ≃tm {!!}
--         l1 = begin
--           {!!}
--             ≈⟨ {!!} ⟩
--           {!!} ∎

--     lem (Join S₁ S₂) (PShift P) T {σ = LJoin x σ σ′} {τ} (TyJoin xty σty σty′) τty p Q = {!!}

-- exterior-sub-label-comm : (S : Tree n)
--                         → (P : Path S)
--                         → .⦃ _ : is-branching-path P ⦄
--                         → (T : Tree m)
--                         → .⦃ _ : has-linear-height (path-length P) T ⦄
--                         → {σ : Sub (suc n) l A}
--                         → {τ : Sub (suc m) l A}
--                         → Typing-Sub (tree-to-ctx S) Γ σ
--                         → Typing-Sub (tree-to-ctx T) Γ τ
--                         → branching-path-to-var S P [ σ ]tm ≃tm unbiased-comp (tree-dim T) T [ τ ]tm
--                         → sub-from-insertion-label S P T σ τ ∘ label-to-sub (exterior-sub-label S P T) ⋆ ≈[ Γ ]s σ
-- exterior-sub-label-comm {A = A} S P T {σ} {τ} σty τty p = begin
--   < sub-from-insertion-label S P T σ τ ∘ label-to-sub (exterior-sub-label S P T) ⋆ >s′
--     ≈˘⟨ reflexive≈s (label-comp-to-sub-comp (exterior-sub-label S P T) (sub-from-insertion-label S P T σ τ) ⋆) ⟩
--   < label-to-sub (exterior-sub-label S P T [ sub-from-insertion-label S P T σ τ ]l) A >s′
--     ≈⟨ label-maximal-equality (label-comp-Ty (exterior-sub-label-Ty S P T ⦃ p = insertion-dim-lem S P T σty τty p ⦄) (sub-from-insertion-label-Ty S P T σty τty p))
--                               (to-label-Ty S σty)
--                               (exterior-sub-label-comm-lem S P T (to-label-Ty S σty) (to-label-Ty T τty) lem) ⟩
--   < label-to-sub (to-label S σ) A >s′
--     ≈⟨ reflexive≈s (sub-to-label-to-sub S σ) ⟩
--   < σ >s′ ∎
--   where
--     lem : branching-path-to-var S P [ label-to-sub (to-label S σ) (sub-type σ) ]tm
--             ≃tm
--           unbiased-comp (tree-dim T) T [ label-to-sub (to-label T τ) (sub-type σ) ]tm
--     lem = begin
--       < branching-path-to-var S P [ label-to-sub (to-label S σ) (sub-type σ) ]tm >tm
--         ≈⟨ sub-action-≃-tm (refl≃tm {s = branching-path-to-var S P}) (sub-to-label-to-sub S σ) ⟩
--       < branching-path-to-var S P [ σ ]tm >tm
--         ≈⟨ p ⟩
--       < unbiased-comp (tree-dim T) T [ τ ]tm >tm
--         ≈˘⟨ sub-action-≃-tm (refl≃tm {s = unbiased-comp (tree-dim T) T}) (sub-to-label-to-sub T τ) ⟩
--       < unbiased-comp (tree-dim T) T [ label-to-sub (to-label T τ) (sub-type σ) ]tm >tm ∎
--       where
--         open Reasoning tm-setoid
--     open Reasoning (sub-setoid-≈ _ _)
-}
-}
-}
