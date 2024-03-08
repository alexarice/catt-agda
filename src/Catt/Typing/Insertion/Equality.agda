open import Catt.Typing.Rule

module Catt.Typing.Insertion.Equality (ops : Op)
                                      (rules : RuleSet)
                                      (tame : Tame ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties

open import Catt.Ops.Tree ops
open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Suspension.Typing ops susp-op rules wk-cond susp-cond
open import Catt.Wedge.Typing ops rules tame
open import Catt.Tree.Typing ops rules tame
open import Catt.Tree.Boundary.Typing ops rules tame
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame
open import Catt.Tree.Standard.Typing ops rules tame
open import Catt.Tree.Insertion.Typing ops rules tame
open import Catt.Typing.DiscRemoval ops rules
open import Catt.Typing.EndoCoherenceRemoval ops rules
open import Catt.Typing.Insertion ops rules

open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Standard.Support


module _ (ecr : HasEndoCoherenceRemoval) (dr : HasDiscRemoval) where
  open import Catt.Typing.DiscRemoval.Properties ops rules tame dr
  open import Catt.Typing.EndoCoherenceRemoval.Properties ops rules tame ecr

  standard-ecr : (d : ℕ)
               → (T : Tree n)
               → (tree-dim T < d)
               → (1 < d)
               → standard-coh d T
                 ≈[ ⌊ T ⌋ ]stm
                 identity-stm (n-disc (pred d)) >>= (standard-label (n-disc (pred d)) T ,, S⋆)
  standard-ecr (suc d) T p q = begin
    SCoh T
         (SArr (standard-stm d (tree-bd d T) >>=
                               (tree-inc-label d T false))
               (standard-sty d T)
               (standard-stm d (tree-bd d T) >>=
                               (tree-inc-label d T true)))
         (id-label-wt T)
      ≈⟨ reflexive≈stm (SCoh≃ T (SArr≃ (standard-stm-full-lem d T false (≤-pred p))
                                       refl≃sty
                                       (standard-stm-full-lem d T true (≤-pred p)))
                                refl≃l
                                refl≃sty) ⟩
    SCoh T (SArr (standard-stm d T)
                 (standard-sty d T)
                 (standard-stm d T))
           (id-label-wt T)
      ≈⟨ ecr-stm T (standard-stm d T)
                   (standard-stm-full d T (≤-pred p))
                   (standard-sty d T)
                   (subst₂ (ops-s T)
                           (sym (supp-lem false))
                           (sym (supp-lem true))
                           (standard-op-s standard-op T d (≤-trans (n≤1+n (tree-dim T)) p)))
                   (id-label T)
                   (standard-stm-Ty d T (≤-pred p))
                   (standard-sty-Ty d T)
                   (id-label-Ty T) ⟩
    identity-stm (n-disc (sty-dim (standard-sty d T)))
      >>=
      (stm-to-label (n-disc (sty-dim (standard-sty d T)))
                    (standard-stm d T)
                    (standard-sty d T) ,, S⋆)
      ●lt id-label-wt T
      ≈⟨ reflexive≈stm (>>=-≃ (refl≃stm {a = identity-stm (n-disc (sty-dim (standard-sty d T)))})
                              (comp-right-unit (stm-to-label (n-disc (sty-dim (standard-sty d T)))
                                                             (standard-stm d T)
                                                             (standard-sty d T)))
                              refl≃sty) ⟩
    identity-stm (n-disc (sty-dim (standard-sty d T)))
      >>= (stm-to-label (n-disc (sty-dim (standard-sty d T)))
                        (standard-stm d T)
                        (standard-sty d T) ,, S⋆)
      ≈⟨ >>=-≈ (identity-stm (n-disc (sty-dim (standard-sty d T))))
               (stm-to-label-≈ (n-disc (sty-dim (standard-sty d T)))
                               (trans≈stm (standard-stm-is-comp′ d ⦃ NonZero-≤ (≤-pred q) it ⦄ T)
                                          (reflexive≈stm (standard-coh′-≃ (sym (≃n-to-≡ tree-dim-n-disc)) refl≃)))
                               (reflexive≈sty (standard-sty-≃ (sym (≃n-to-≡ tree-dim-n-disc)) refl≃)))
               refl≈sty ⟩
    identity-stm (n-disc (sty-dim (standard-sty d T)))
      >>= (stm-to-label (n-disc (sty-dim (standard-sty d T)))
                        (standard-coh′ (tree-dim (n-disc d)) T)
                        (standard-sty (tree-dim (n-disc d)) T)
                        ⦃ l1 (standard-sty-dim d T) ⦄ ,, S⋆)
      ≈⟨ reflexive≈stm (lem (sty-dim (standard-sty d T)) d (standard-sty-dim d T)) ⟩
    identity-stm (n-disc d) >>= (standard-label (n-disc d) T ,, S⋆) ∎
    where
      supp-lem : (b : Bool) → DCT (FVSTm (standard-stm d T)) ≡ supp-tree-bd d T b
      supp-lem b = begin
        DCT (FVSTm (standard-stm d T))
          ≡⟨ standard-stm-full d T (≤-pred p) ⟩
        tFull
          ≡˘⟨ supp-tree-bd-full d T b (≤-pred p) ⟩
        supp-tree-bd d T b ∎
        where
          open ≡-Reasoning

      open Reasoning stm-setoid-≈

      l1 : n ≡ m → has-dim (tree-dim (n-disc n)) (standard-sty (tree-dim (n-disc m)) T)
      l1 {m = m} refl = ≡-to-≃n (sym (standard-sty-dim (tree-dim (n-disc m)) T))

      lem : (n m : ℕ) → (q : n ≡ m)
          → identity-stm (n-disc n)
              >>= (stm-to-label (n-disc n)
                                (standard-coh′ (tree-dim (n-disc m)) T)
                                (standard-sty (tree-dim (n-disc m)) T) ⦃ l1 q ⦄ ,, S⋆)
            ≃stm
            identity-stm (n-disc m) >>= (standard-label (n-disc m) T ,, S⋆)
      lem _ _ refl = refl≃stm

  pruned-branch-κ : (S : Tree n)
                  → (P : Branch S l)
                  → (T : Tree m)
                  → .⦃ _ : has-trunk-height l T ⦄
                  → .(q : bh P < pred (lh P))
                  → (x : tree-dim T < lh P)
                  → πt P ●l (κ (S //t P) (pruned-branch S P q) T ,, S⋆)
                    ≈[ ⌊ (S //t P) >>[ pruned-branch S P q ] T ⌋ ]lm
                    ≃-label (sym≃′ (insertion-tree-pruned-branch S P T q)) (κ S P T)
  pruned-branch-κ (Join S₁ S₂) (BExt P) (Susp T) q x .get (PExt Z) = begin
    πt P Z >>=
          (SExt ∘ κ (S₁ //t P) (pruned-branch S₁ P _) T
          ,, SArr (SPath PHere) S⋆ (SShift (SPath PHere)))
      ≈⟨ reflexive≈stm (>>=-≃ (refl≃stm {a = πt P Z}) refl≃l (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm))) ⟩
    (πt P Z >>=
          (map-ext (κ (S₁ //t P) (pruned-branch S₁ P _) T ,, S⋆)))
      ≈⟨ reflexive≈stm (>>=-ext (πt P Z) (κ (S₁ //t P) (pruned-branch S₁ P _) T ,, S⋆)) ⟩
    SExt (πt P Z
         >>= (κ (S₁ //t P) (pruned-branch S₁ P _) T ,, S⋆))
      ≈⟨ ≈SExt (pruned-branch-κ S₁ P T (≤-pred q) (≤-pred x) .get Z) ⟩
    SExt (≃-label (sym≃′ (insertion-tree-pruned-branch S₁ P T _)) (κ S₁ P T) Z) ∎
    where
      open Reasoning stm-setoid-≈
  pruned-branch-κ (Join S₁ S₂) (BExt P) (Susp T) q x .get (PShift Z) = refl≈stm
  pruned-branch-κ (Join S₁ S₂) (BShift P) T q x .get (PExt Z) = refl≈stm
  pruned-branch-κ (Join S₁ S₂) (BShift P) T q x .get (PShift Z) = begin
    (πt P Z
      >>= map-shift (κ (S₂ //t P)
                                        (pruned-branch S₂ P _) T ,, S⋆))
      ≈⟨ reflexive≈stm (>>=-shift (πt P Z) (κ (S₂ //t P)
                                        (pruned-branch S₂ P _) T ,, S⋆)) ⟩
    SShift (πt P Z
      >>= (κ (S₂ //t P)
                              (pruned-branch S₂ P _) T ,, S⋆))
      ≈⟨ ≈SShift (pruned-branch-κ S₂ P T q x .get Z) ⟩
    SShift (≃-label (sym≃′ (insertion-tree-pruned-branch S₂ P T _))
                    (κ S₂ P T) Z) ∎
    where
      open Reasoning stm-setoid-≈
  pruned-branch-κ (Join (Susp S₁) S₂) BHere T q x .get (PExt Z) = begin
    standard-label (Susp (Susp S₁)) (n-disc (suc (tree-dim S₁))) (PExt Z)
      >>= ++t-inc-left (Join (n-disc (tree-dim S₁)) Sing) S₂
      >>= (replace-label (standard-label (n-disc (suc (tree-dim S₁))) T) SHere
                            ●l (++t-inc-left T S₂)
           ++l′ ap (++t-inc-right T S₂) ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-≃ (>>=-≃ l1 refl≃l refl≃sty) refl≃l refl≃sty) ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= ++t-inc-left (Susp (n-disc (tree-dim S₁))) S₂
      >>= (replace-label (standard-label (n-disc (suc (tree-dim S₁))) T) SHere
                            ●l (++t-inc-left T S₂)
           ++l′ ap (++t-inc-right T S₂) ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-assoc (identity-stm (n-disc (suc (tree-dim S₁))))
                                  (++t-inc-left (Susp (n-disc (tree-dim S₁))) S₂)
                                  (replace-label (standard-label (n-disc (suc (tree-dim S₁))) T) SHere
                                                    ●l (++t-inc-left T S₂)
                                   ++l′ ap (++t-inc-right T S₂) ,, S⋆)) ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= ++t-inc-left (Susp (n-disc (tree-dim S₁))) S₂
          ●lt (replace-label (standard-label (n-disc (suc (tree-dim S₁))) T) SHere
                                ●l (++t-inc-left T S₂)
               ++l′ ap (++t-inc-right T S₂) ,, S⋆)
      ≈⟨ >>=-≈ (identity-stm (n-disc (suc (tree-dim S₁))))
               (++l′-inc-left (replace-label (standard-label (n-disc (suc (tree-dim S₁))) T) SHere
                                          ●l (++t-inc-left T S₂))
                                        (ap (++t-inc-right T S₂))
                                        S⋆
                                        (reflexive≈stm l2))
               refl≈sty ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= (replace-label (standard-label (n-disc (suc (tree-dim S₁))) T) SHere
          ●l (++t-inc-left T S₂) ,, S⋆)
      ≈⟨ >>=-≈ (identity-stm (n-disc (suc (tree-dim S₁))))
               (≈-label-comp (replace-label-eq (standard-label (n-disc (suc (tree-dim S₁))) T)
                                               SHere
                                               (reflexive≈stm (sym≃stm (standard-label-fst (n-disc (suc (tree-dim S₁))) T))))
                             (++t-inc-left-Ty T S₂)
                             TySStar)
               refl≈sty ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= (standard-label (n-disc (suc (tree-dim S₁))) T ●l (++t-inc-left T S₂) ,, S⋆)
      ≈˘⟨ reflexive≈stm (>>=-assoc (identity-stm (n-disc (suc (tree-dim S₁))))
                                   (standard-label (n-disc (suc (tree-dim S₁))) T ,, S⋆) _) ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= (standard-label (n-disc (suc (tree-dim S₁))) T ,, S⋆)
      >>= ++t-inc-left T S₂
      ≈˘⟨ ≈->>= (standard-ecr (2+ (tree-dim S₁)) T x (s≤s (s≤s z≤n))) (++t-inc-left-Ty T S₂) TySStar ⟩
    standard-coh (2+ (tree-dim S₁)) T >>= ++t-inc-left T S₂
      ≈˘⟨ reflexive≈stm (>>=-≃ (standard-coh′-compat (2+ (tree-dim S₁)) T) refl≃l refl≃sty) ⟩
    standard-coh′ (2+ (tree-dim S₁)) T >>= ++t-inc-left T S₂
      ≈˘⟨ reflexive≈stm (>>=-≃ (standard-label-max (Susp (Susp S₁)) T (PExt Z)) refl≃l refl≃sty) ⟩
    standard-label (Susp (Susp S₁)) T (PExt Z) >>= ++t-inc-left T S₂ ∎
    where
      l1 : standard-label (Susp (Susp S₁)) (n-disc (suc (tree-dim S₁))) (PExt Z)
           ≃stm
           identity-stm (n-disc (suc (tree-dim S₁)))
      l1 = begin
        < standard-label (Susp (Susp S₁)) (n-disc (suc (tree-dim S₁))) (PExt Z) >stm
          ≈⟨ standard-label-max (Susp (Susp S₁)) (n-disc (suc (tree-dim S₁))) (PExt Z) ⟩
        < standard-coh′ (tree-dim (Susp (Susp S₁))) (n-disc (suc (tree-dim S₁))) >stm
          ≈⟨ standard-coh′-compat (2+ (tree-dim S₁)) (n-disc (suc (tree-dim S₁))) ⟩
        < standard-coh (2+ (tree-dim S₁)) (n-disc (suc (tree-dim S₁))) >stm
          ≈˘⟨ standard-coh-≃ (≃n-to-≡ (tree-dim-n-disc {suc (suc (tree-dim S₁))})) refl≃ ⟩
        < standard-coh (suc (tree-dim (n-disc (suc (tree-dim S₁))))) (n-disc (suc (tree-dim S₁))) >stm
          ≈˘⟨ identity-stm-is-standard (n-disc (suc (tree-dim S₁))) ⟩
        < identity-stm (n-disc (suc (tree-dim S₁))) >stm ∎
        where
          open Reasoning stm-setoid

      l2 : standard-label (n-disc (suc (tree-dim S₁))) T (PShift PHere) >>= ++t-inc-left T S₂
           ≃stm
           ap (++t-inc-right T S₂) PHere
      l2 = begin
        < standard-label (n-disc (suc (tree-dim S₁))) T (PShift PHere) >>= ++t-inc-left T S₂ >stm
          ≈⟨ >>=-≃ (standard-label-last (n-disc (suc (tree-dim S₁))) T) refl≃l refl≃sty ⟩
        < ap (++t-inc-left T S₂) (last-path T) >stm
          ≈⟨ SPath≃ (++t-inc-phere T S₂) ⟩
        < ap (++t-inc-right T S₂) PHere >stm ∎
        where
          open Reasoning stm-setoid
      open Reasoning stm-setoid-≈
  pruned-branch-κ (Join (Join S₁ Sing) S₂) BHere T q x .get (PShift Z) = refl≈stm

module _ (disc-rem : HasDiscRemoval) where
  open import Catt.Typing.DiscRemoval.Properties ops rules tame disc-rem

  κ-disc : (S : Tree n)
         → (P : Branch S l)
         → κ S P (n-disc (lh P)) ⦃ has-trunk-height-n-disc (<⇒≤ (bh-<-lh P)) ⦄
           ≈[ ⌊ (S >>[ P ] (n-disc (lh P))) ⦃ _ ⦄ ⌋ ]lm
           ≃-label (sym≃′ (insertion-disc S P)) (id-label S)
  κ-disc (Join S T) BHere .get (PExt Z) = begin
    standard-label (Susp S) (n-disc (suc (tree-dim S))) (PExt Z)
      >>= ++t-inc-left (n-disc (suc (tree-dim S))) T
      ≈⟨ reflexive≈stm (>>=-≃ (standard-label-max (Susp S) (n-disc (suc (tree-dim S))) (PExt Z))
                              refl≃l
                              refl≃sty) ⟩
    standard-coh′ (tree-dim (Susp S)) (n-disc (suc (tree-dim S)))
      >>= ++t-inc-left (n-disc (suc (tree-dim S))) T
      ≈˘⟨ reflexive≈stm (>>=-≃ (standard-coh′-≃ (≃n-to-≡ (tree-dim-n-disc {n = suc (tree-dim S)}))
                                                  (refl≃ {T = n-disc (suc (tree-dim S))}))
                               (refl≃l {L = ap (++t-inc-left (n-disc (suc (tree-dim S))) T)})
                               refl≃sty) ⟩
    standard-coh′ (tree-dim (n-disc (suc (tree-dim S)))) (n-disc (suc (tree-dim S)))
      >>= ++t-inc-left (n-disc (suc (tree-dim S))) T
      ≈⟨ reflexive≈stm (>>=-≃ (standard-coh′-compat (tree-dim (n-disc (suc (tree-dim S))))
                                                      (n-disc (suc (tree-dim S))))
                              (refl≃l {L = ap (++t-inc-left (n-disc (suc (tree-dim S))) T)})
                              refl≃sty) ⟩
    standard-coh (tree-dim (n-disc (suc (tree-dim S)))) (n-disc (suc (tree-dim S)))
      >>= ++t-inc-left (n-disc (suc (tree-dim S))) T
      ≈˘⟨ reflexive≈stm (>>=-≃ (disc-stm-is-standard (n-disc (suc (tree-dim S))))
                               (refl≃l {L = ap (++t-inc-left (n-disc (suc (tree-dim S))) T)})
                               refl≃sty) ⟩
    disc-stm (n-disc (suc (tree-dim S))) >>= ++t-inc-left (Susp (n-disc (tree-dim S))) T
      ≈⟨ disc-rem-stm (n-disc (suc (tree-dim S)))
                      (ap (++t-inc-left (Susp (n-disc (tree-dim S))) T))
                      (++t-inc-left-Ty (n-disc (suc (tree-dim S))) T) ⟩
    ap (++t-inc-left (Susp (n-disc (tree-dim S))) T) (is-linear-max-path (n-disc (suc (tree-dim S))))
      ≡⟨⟩
    SPath (PExt (is-linear-max-path (n-disc (tree-dim S))))
      ≈⟨ reflexive≈stm (SPath≃ (Ext≃ (trans≃p (max-path-lin-tree (n-disc (tree-dim S))
                                                                 Z
                                                                 (≃′-to-≃ (linear-tree-unique (n-disc (tree-dim S)) S (≃n-to-≡ tree-dim-n-disc))))
                                              (ppath-≃-≃p (sym≃′ (linear-tree-unique (n-disc (tree-dim S)) S _)) Z)) refl≃)) ⟩
    SPath (PExt (ppath-≃ (sym≃′ (linear-tree-unique (n-disc (tree-dim S)) S _)) Z)) ∎
    where
      open Reasoning stm-setoid-≈
  κ-disc (Join S T) BHere .get (PShift Z) = refl≈stm
  κ-disc (Join S T) (BExt P) .get (PExt Z)
    = compute-≈ (≈SExt (trans≈stm (κ-disc S P .get Z) (reflexive≈stm (stm-≃-spath (sym≃′ (insertion-disc S P)) Z))))
  κ-disc (Join S T) (BExt P) .get (PShift Z) = compute-≈ refl≈stm
  κ-disc (Join S T) (BShift P) .get (PExt Z) = compute-≈ refl≈stm
  κ-disc (Join S T) (BShift P) .get (PShift Z)
    = compute-≈ (≈SShift (trans≈stm (κ-disc T P .get Z) (reflexive≈stm (stm-≃-spath (sym≃′ (insertion-disc T P)) Z))))

module _ (dr : HasDiscRemoval) (insert : HasInsertion) where
  open import Catt.Typing.DiscRemoval.Properties ops rules tame dr

  κ-standard-sty : (S : Tree n)
                 → (P : Branch S l)
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height l T ⦄
                 → (d : ℕ)
                 → (tree-dim T ≤ lh P)
                 → standard-sty d S >>=′ (κ S P T ,, S⋆)
                   ≈[ ⌊ S >>[ P ] T ⌋ ]sty
                   standard-sty d (S >>[ P ] T)
  κ-standard-coh : (S : Tree n)
                 → (P : Branch S l)
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height l T ⦄
                 → (d : ℕ)
                 → d ≥ tree-dim S
                 → (tree-dim T ≤ lh P)
                 → standard-coh d S >>= (κ S P T ,, S⋆)
                   ≈[ ⌊ S >>[ P ] T ⌋ ]stm
                   standard-coh d (S >>[ P ] T)
  κ-standard-coh′ : (S : Tree n)
                  → (P : Branch S l)
                  → (T : Tree m)
                  → .⦃ _ : has-trunk-height l T ⦄
                  → (d : ℕ)
                  → d ≥ tree-dim S
                  → (tree-dim T ≤ lh P)
                  → standard-coh′ d S >>= (κ S P T ,, S⋆)
                    ≈[ ⌊ S >>[ P ] T ⌋ ]stm
                    standard-coh′ d (S >>[ P ] T)
  κ-standard-stm : (S : Tree n)
                 → (P : Branch S l)
                 → (T : Tree m)
                 → .⦃ _ : has-trunk-height l T ⦄
                 → (d : ℕ)
                 → d ≥ tree-dim S
                 → tree-dim T ≤ lh P
                 → standard-stm d S >>= (κ S P T ,, S⋆)
                   ≈[ ⌊ S >>[ P ] T ⌋ ]stm
                   standard-stm d (S >>[ P ] T)

  κ-standard-sty S P T zero q = refl≈sty
  κ-standard-sty S P T (suc d) q
    = ≈SArr (lem false)
            (κ-standard-sty S P T d q)
            (lem true)
    where

      open Reasoning stm-setoid-≈

      lem2 : (b : Bool)
           → Bd-Conditions d P T
           → standard-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆)
             ≈[ ⌊ S >>[ P ] T ⌋ ]stm
             standard-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b
      lem2 b (Bd-Cond1 x y) = begin
        standard-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆)
          ≈⟨ >>=-≈ (standard-stm d (tree-bd d S))
                   (label-max-equality-to-equality (bd-κ-comm-1 S P T d x y q b)
                                                   (label-comp-Ty (tree-inc-Ty d S b) (κ-Ty S P T q) TySStar)
                                                   (label-≃-Ty (insertion-bd-1 S P T d y q) (tree-inc-Ty d (S >>[ P ] T) b)))
                   refl≈sty ⟩
        standard-stm d (tree-bd d S) >>=
          label-wt-≃ (insertion-bd-1 S P T d y q) (tree-inc-label d (S >>[ P ] T) b)
          ≈˘⟨ reflexive≈stm (>>=-assoc (standard-stm d (tree-bd d S)) _ _) ⟩
        standard-stm d (tree-bd d S) >>= (SPath ∘ ppath-≃ (insertion-bd-1 S P T d y q) ,, S⋆) >>= tree-inc-label d (S >>[ P ] T) b
          ≈⟨ reflexive≈stm (>>=-≃ (standard-stm-≃-prop d (insertion-bd-1 S P T d y q)) refl≃l refl≃sty) ⟩
        standard-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b ∎
      lem2 b (Bd-Cond2 x) = begin
        standard-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆)
          ≈⟨ >>=-≈ (standard-stm d (tree-bd d S))
                   (label-max-equality-to-equality
                     (bd-κ-comm-2 S P T d b q x)
                     (label-comp-Ty (tree-inc-Ty d S b) (κ-Ty S P T q) TySStar)
                     (label-comp-Ty (κ-Ty (tree-bd d S)
                                          (bd-branch S P d _)
                                          (tree-bd d T)
                                          ⦃ _ ⦄
                                          (bd-branch-lh S P d (bd-branch-lem P x) T q))
                                    (label-≃-Ty (insertion-bd-2 S P T d _) (tree-inc-Ty d (S >>[ P ] T) b)) TySStar))
                   refl≈sty ⟩
        standard-stm d (tree-bd d S)
          >>= (κ (tree-bd d S)
                              (bd-branch S P d _)
                              (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
          ●lt (label-wt-≃ (insertion-bd-2 S P T d _)
                          (tree-inc-label d (S >>[ P ] T) b))
          ≈˘⟨ reflexive≈stm (>>=-assoc (standard-stm d (tree-bd d S))
                                       (κ (tree-bd d S)
                                                       (bd-branch S P d _)
                                                       (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
                                       (_ ,, S⋆)) ⟩
        standard-stm d (tree-bd d S)
          >>= (κ (tree-bd d S) (bd-branch S P d _) (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
          >>= label-wt-≃ (insertion-bd-2 S P T d _) (tree-inc-label d (S >>[ P ] T) b)
          ≈⟨ ≈->>= (κ-standard-stm (tree-bd d S)
                                           (bd-branch S P d (bd-branch-lem P x))
                                           (tree-bd d T)
                                           ⦃ _ ⦄
                                           d
                                           (tree-dim-bd″ d S)
                                           (bd-branch-lh S P d (bd-branch-lem P x) T q))
                   (label-≃-Ty (insertion-bd-2 S P T d _) (tree-inc-Ty d (S >>[ P ] T) b))
                   TySStar ⟩
        standard-stm d ((tree-bd d S >>[ bd-branch S P d _ ] tree-bd d T) ⦃ _ ⦄)
          >>= label-wt-≃ (insertion-bd-2 S P T d _)
                         (tree-inc-label d (S >>[ P ] T) b)
          ≈˘⟨ reflexive≈stm (>>=-assoc (standard-stm d ((tree-bd d S >>[ bd-branch S P d _ ] tree-bd d T) ⦃ _ ⦄))
                            (SPath ∘ ppath-≃ (insertion-bd-2 S P T d _) ,, S⋆)
                            (tree-inc-label d (S >>[ P ] T) b)) ⟩
        standard-stm d ((tree-bd d S >>[ bd-branch S P d _ ] tree-bd d T) ⦃ _ ⦄)
          >>= ((SPath ∘ ppath-≃ (insertion-bd-2 S P T d _)) ,, S⋆)
          >>= tree-inc-label d (S >>[ P ] T) b
          ≈⟨ reflexive≈stm (>>=-≃ (standard-stm-≃-prop d (insertion-bd-2 S P T d _)) refl≃l refl≃sty) ⟩
        standard-stm d (tree-bd d (S >>[ P ] T))
          >>= tree-inc-label d (S >>[ P ] T) b ∎

      lem : (b : Bool)
          → standard-stm d (tree-bd d S) >>= tree-inc-label d S b >>= (κ S P T ,, S⋆)
            ≈[ ⌊ S >>[ P ] T ⌋ ]stm
            standard-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b
      lem b = begin
        standard-stm d (tree-bd d S) >>= tree-inc-label d S b >>= (κ S P T ,, S⋆)
          ≈⟨ reflexive≈stm (>>=-assoc (standard-stm d (tree-bd d S)) _ _) ⟩
        standard-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆)
          ≈⟨ lem2 b (Bd-Conditions-one-of d P T) ⟩
        standard-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b ∎

  κ-standard-coh S@(Join _ _) P T d q p = begin
    SCoh S (standard-sty d S) (κ S P T ,, S⋆)
      ≈⟨ insert (standard-sty d S)
                (κ S P T)
                P
                p
                (ι S P T)
                (κ-branch-path S P T)
                (>>=-Ty (standard-coh-Ty d ⦃ NonZero-≤ q it ⦄ S q) (κ-Ty S P T p) TySStar) ⟩
    SCoh (S >>[ P ] T)
         (standard-sty d S >>=′ (κ S P T ,, S⋆))
         (κ S P T >>l[ P ] ι S P T ,, S⋆)
      ≈⟨ ≈SCoh (S >>[ P ] T)
               (κ-standard-sty S P T d p)
               (reflexive≈l (κ-ι-prop S P T)) refl≈sty ⟩
    SCoh (S >>[ P ] T) (standard-sty d (S >>[ P ] T)) (id-label-wt _) ∎
    where
      open Reasoning stm-setoid-≈

  κ-standard-coh′ S P T d q p = begin
    standard-coh′ d S >>= (κ S P T ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-≃ (standard-coh′-compat d S) refl≃l refl≃sty) ⟩
    standard-coh d S >>= (κ S P T ,, S⋆)
      ≈⟨ κ-standard-coh S P T d q p ⟩
    standard-coh d (S >>[ P ] T)
      ≈˘⟨ reflexive≈stm (standard-coh′-compat d (S >>[ P ] T)) ⟩
    standard-coh′ d (S >>[ P ] T) ∎
    where
      open Reasoning stm-setoid-≈

  κ-standard-stm S@(Join _ _) P T d q p = begin
    standard-stm d S >>= (κ S P T ,, S⋆)
      ≈⟨ ≈->>= (standard-stm-is-comp d ⦃ NonZero-≤ q it ⦄ S) (κ-Ty S P T p) TySStar ⟩
    standard-coh d S >>= (κ S P T ,, S⋆)
      ≈⟨ κ-standard-coh S P T d q p ⟩
    standard-coh d (S >>[ P ] T)
      ≈˘⟨ standard-stm-is-comp d ⦃ NonZero-≤ q it ⦄ (S >>[ P ] T) ⟩
    standard-stm d (S >>[ P ] T) ∎
    where
      open Reasoning stm-setoid-≈


  κ-inserted-branch : (S : Tree n)
                    → (P : Branch S l)
                    → (T : Tree m)
                    → .⦃ _ : has-trunk-height l T ⦄
                    → .⦃ _ : non-linear T ⦄
                    → (lh P ≥ tree-dim T)
                    → (Q : Branch T l′)
                    → (U : Tree m′)
                    → .⦃ _ : has-trunk-height l′ U ⦄
                    → tree-dim U ≤ lh Q
                    → κ S P T ●l (κ (S >>[ P ] T) (inserted-branch S P T Q) U ,, S⋆)
                      ≈[ ⌊ (S >>[ P ] T) >>[ inserted-branch S P T Q ] U ⌋ ]lm
                      ≃-label (sym≃′ (insertion-tree-inserted-branch S P T Q U))
                              (κ S P (T >>[ Q ] U) ⦃ insertion-trunk-height T Q U l ⦄)
  κ-inserted-branch (Join S₁ S₂) BHere T p Q U q .get (PExt Z) = begin
    standard-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂
      >>= (κ (T ++t S₂) (wedge-branch-left T S₂ Q) U ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-assoc (standard-label (Susp S₁) T (PExt Z)) _ _) ⟩
    standard-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂ ●lt (κ (T ++t S₂) (wedge-branch-left T S₂ Q) U ,, S⋆)
      ≈⟨ fixup-reflexive≈stm (>>=-≃ (standard-label-max (Susp S₁) T (PExt Z))
                                    (κ-branch-left-inc-left T S₂ Q U)
                                    (S⋆-≃ (≃′-to-≃ (insertion-branch-left T S₂ Q U))))
                             (insertion-branch-left T S₂ Q U) ⟩
    stm-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
      (standard-coh′ (1 + tree-dim S₁) T
        >>= (κ T Q U ,, S⋆) ●lt (++t-inc-left (T >>[ Q ] U) S₂))
      ≈˘⟨ reflexive≈stm (stm-≃-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
                                 (>>=-assoc (standard-coh′ (1 + tree-dim S₁) T) (κ T Q U ,, S⋆) _)) ⟩
    stm-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
      (standard-coh′ (1 + tree-dim S₁) T >>= (κ T Q U ,, S⋆)
                                           >>= ++t-inc-left (T >>[ Q ] U) S₂)
      ≈⟨ stm-≃-≈ ((sym≃′ (insertion-branch-left T S₂ Q U)))
                 (≈->>= (κ-standard-coh′ T Q U (1 + tree-dim S₁) p q)
                        (++t-inc-left-Ty (T >>[ Q ] U) S₂)
                        TySStar) ⟩
    stm-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
      (standard-coh′ (1 + tree-dim S₁) (T >>[ Q ] U)
        >>= ++t-inc-left (T >>[ Q ] U) S₂)
      ≈˘⟨ stm-≃-≈ (sym≃′ (insertion-branch-left T S₂ Q U))
                  (reflexive≈stm (>>=-≃ (standard-label-max (Susp S₁) (T >>[ Q ] U) (PExt Z)) refl≃l refl≃sty)) ⟩
    stm-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
         (standard-label (Susp S₁) (T >>[ Q ] U) (PExt Z)
           >>= ++t-inc-left (T >>[ Q ] U) S₂) ∎
    where
      open Reasoning stm-setoid-≈
  κ-inserted-branch (Join S₁ S₂) BHere T p Q U q .get (PShift Z)
    = fixup-reflexive≈stm (κ-branch-left-inc-right T S₂ Q U .get Z) (insertion-branch-left T S₂ Q U)
  κ-inserted-branch (Join S₁ S₂) (BExt P) (Susp T) p BHere U q = ⊥-elim (linear-non-linear T)
  κ-inserted-branch (Join S₁ S₂) (BExt P) (Susp T) p (BExt Q) (Join U Sing) q .get (PExt Z) = begin
    (κ S₁ P T Z >>= map-ext (κ (S₁ >>[ P ] T) (inserted-branch S₁ P T Q) U ,, S⋆))
      ≈⟨ reflexive≈stm (>>=-ext (κ S₁ P T Z) (κ (S₁ >>[ P ] T) (inserted-branch S₁ P T Q) U ,, S⋆)) ⟩
    SExt (κ S₁ P T Z >>= (κ (S₁ >>[ P ] T) (inserted-branch S₁ P T Q) U ,, S⋆))
      ≈⟨ ≈SExt (κ-inserted-branch S₁ P T (≤-pred p) Q U (≤-pred q) .get Z) ⟩
    SExt (stm-≃ (sym≃′ (insertion-tree-inserted-branch S₁ P T Q U)) (κ S₁ P (T >>[ Q ] U) ⦃ insertion-trunk-height T Q U (bh P) ⦄ Z)) ∎
    where
      open Reasoning stm-setoid-≈
  κ-inserted-branch (Join S₁ S₂) (BExt P) (Susp T) p (BExt Q) (Join U Sing) q .get (PShift Z) = ≈SShift refl≈stm
  κ-inserted-branch (Join S₁ S₂) (BShift P) T p Q U q .get (PExt Z) = ≈SExt refl≈stm
  κ-inserted-branch (Join S₁ S₂) (BShift P) T p Q U q .get (PShift Z) = begin
    (κ S₂ P T Z
      >>= map-shift (κ (S₂ >>[ P ] T) (inserted-branch S₂ P T Q) U ,, S⋆))
      ≈⟨ reflexive≈stm (>>=-shift (κ S₂ P T Z) _) ⟩
    SShift (κ S₂ P T Z >>= (κ (S₂ >>[ P ] T) (inserted-branch S₂ P T Q) U ,, S⋆))
      ≈⟨ ≈SShift (κ-inserted-branch S₂ P T p Q U q .get Z) ⟩
    SShift (stm-≃ (sym≃′ (insertion-tree-inserted-branch S₂ P T Q U)) (κ S₂ P (T >>[ Q ] U) ⦃ insertion-trunk-height T Q U (bh P) ⦄ Z)) ∎
    where
      open Reasoning stm-setoid-≈
