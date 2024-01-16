open import Catt.Typing.Rule

module Catt.Typing.Insertion.Equality (rules : RuleSet)
                                      (tame : Tame rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
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
open import Catt.Tree.Canonical
open import Catt.Tree.Canonical.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties

open import Catt.Typing rules
open import Catt.Typing.Properties rules tame
open import Catt.Suspension.Typing rules lift-cond susp-cond
open import Catt.Connection.Typing rules tame
open import Catt.Tree.Typing rules tame
open import Catt.Tree.Boundary.Typing rules tame
open import Catt.Tree.Structured.Typing rules
open import Catt.Tree.Structured.Typing.Properties rules tame
open import Catt.Tree.Canonical.Typing rules tame
open import Catt.Tree.Insertion.Typing rules tame
open import Catt.Typing.DiscRemoval rules
open import Catt.Typing.EndoCoherenceRemoval rules
open import Catt.Typing.Insertion rules


module _ (ecr : HasEndoCoherenceRemoval) (dr : HasDiscRemoval) where
  open import Catt.Typing.DiscRemoval.Properties rules tame dr
  open import Catt.Typing.EndoCoherenceRemoval.Properties rules tame ecr

  canonical-ecr : (d : ℕ)
                → (T : Tree n)
                → (tree-dim T < d)
                → (1 < d)
                → canonical-comp d T
                  ≈[ ⌊ T ⌋ ]stm
                  identity-stm (n-disc (pred d)) >>= (canonical-label (n-disc (pred d)) T ,, S⋆)
  canonical-ecr (suc d) T p q = begin
    SCoh T
         (SArr (canonical-stm d (tree-bd d T) >>=
                               (tree-inc-label d T false))
               (canonical-type d T)
               (canonical-stm d (tree-bd d T) >>=
                               (tree-inc-label d T true)))
         (id-label-wt T)
      ≈⟨ reflexive≈stm (SCoh≃ T (SArr≃ (canonical-stm-full-lem d T false (≤-pred p))
                                       refl≃sty
                                       (canonical-stm-full-lem d T true (≤-pred p)))
                                refl≃l
                                refl≃sty) ⟩
    SCoh T (SArr (canonical-stm d T)
                 (canonical-type d T)
                 (canonical-stm d T))
           (id-label-wt T)
      ≈⟨ ecr-stm T (canonical-stm d T)
                   (canonical-type d T)
                   (id-label T)
                   (canonical-stm-Ty d T)
                   (canonical-type-Ty d T)
                   (id-label-Ty T) ⟩
    identity-stm (n-disc (sty-dim (canonical-type d T)))
      >>=
      (stm-to-label (n-disc (sty-dim (canonical-type d T)))
                    (canonical-stm d T)
                    (canonical-type d T) ,, S⋆)
      ●lt id-label-wt T
      ≈⟨ reflexive≈stm (>>=-≃ (refl≃stm {a = identity-stm (n-disc (sty-dim (canonical-type d T)))})
                              (comp-right-unit (stm-to-label (n-disc (sty-dim (canonical-type d T)))
                                                             (canonical-stm d T)
                                                             (canonical-type d T)))
                              refl≃sty) ⟩
    identity-stm (n-disc (sty-dim (canonical-type d T)))
      >>= (stm-to-label (n-disc (sty-dim (canonical-type d T)))
                        (canonical-stm d T)
                        (canonical-type d T) ,, S⋆)
      ≈⟨ >>=-≈ (identity-stm (n-disc (sty-dim (canonical-type d T))))
               (stm-to-label-≈ (n-disc (sty-dim (canonical-type d T)))
                               (trans≈stm (canonical-stm-is-comp′ d ⦃ NonZero-≤ (≤-pred q) it ⦄ T)
                                          (reflexive≈stm (canonical-comp′-≃ (sym (≃n-to-≡ tree-dim-n-disc)) refl≃)))
                               (reflexive≈sty (canonical-type-≃ (sym (≃n-to-≡ tree-dim-n-disc)) refl≃)))
               refl≈sty ⟩
    identity-stm (n-disc (sty-dim (canonical-type d T)))
      >>= (stm-to-label (n-disc (sty-dim (canonical-type d T)))
                        (canonical-comp′ (tree-dim (n-disc d)) T)
                        (canonical-type (tree-dim (n-disc d)) T)
                        ⦃ l1 (canonical-type-dim d T) ⦄ ,, S⋆)
      ≈⟨ reflexive≈stm (lem (sty-dim (canonical-type d T)) d (canonical-type-dim d T)) ⟩
    identity-stm (n-disc d) >>= (canonical-label (n-disc d) T ,, S⋆) ∎
    where
      open Reasoning stm-setoid-≈

      l1 : n ≡ m → has-dim (tree-dim (n-disc n)) (canonical-type (tree-dim (n-disc m)) T)
      l1 {m = m} refl = ≡-to-≃n (sym (canonical-type-dim (tree-dim (n-disc m)) T))

      lem : (n m : ℕ) → (q : n ≡ m)
          → identity-stm (n-disc n)
              >>= (stm-to-label (n-disc n)
                                (canonical-comp′ (tree-dim (n-disc m)) T)
                                (canonical-type (tree-dim (n-disc m)) T) ⦃ l1 q ⦄ ,, S⋆)
            ≃stm
            identity-stm (n-disc m) >>= (canonical-label (n-disc m) T ,, S⋆)
      lem _ _ refl = refl≃stm

  pruned-branch-κ : (S : Tree n)
                  → (P : Branch S l)
                  → (T : Tree m)
                  → .⦃ _ : has-trunk-height l T ⦄
                  → .(q : bh P < pred (ih P))
                  → (x : tree-dim T < ih P)
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
    canonical-label (Susp (Susp S₁)) (n-disc (suc (tree-dim S₁))) (PExt Z)
      >>= ++t-inc-left (Join (n-disc (tree-dim S₁)) Sing) S₂
      >>= (replace-label (canonical-label (n-disc (suc (tree-dim S₁))) T) SHere
                            ●l (++t-inc-left T S₂)
           ++l′ ap (++t-inc-right T S₂) ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-≃ (>>=-≃ l1 refl≃l refl≃sty) refl≃l refl≃sty) ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= ++t-inc-left (Susp (n-disc (tree-dim S₁))) S₂
      >>= (replace-label (canonical-label (n-disc (suc (tree-dim S₁))) T) SHere
                            ●l (++t-inc-left T S₂)
           ++l′ ap (++t-inc-right T S₂) ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-assoc (identity-stm (n-disc (suc (tree-dim S₁))))
                                  (++t-inc-left (Susp (n-disc (tree-dim S₁))) S₂)
                                  (replace-label (canonical-label (n-disc (suc (tree-dim S₁))) T) SHere
                                                    ●l (++t-inc-left T S₂)
                                   ++l′ ap (++t-inc-right T S₂) ,, S⋆)) ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= ++t-inc-left (Susp (n-disc (tree-dim S₁))) S₂
          ●lt (replace-label (canonical-label (n-disc (suc (tree-dim S₁))) T) SHere
                                ●l (++t-inc-left T S₂)
               ++l′ ap (++t-inc-right T S₂) ,, S⋆)
      ≈⟨ >>=-≈ (identity-stm (n-disc (suc (tree-dim S₁))))
               (++l′-inc-left (replace-label (canonical-label (n-disc (suc (tree-dim S₁))) T) SHere
                                          ●l (++t-inc-left T S₂))
                                        (ap (++t-inc-right T S₂))
                                        S⋆
                                        (reflexive≈stm l2))
               refl≈sty ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= (replace-label (canonical-label (n-disc (suc (tree-dim S₁))) T) SHere
          ●l (++t-inc-left T S₂) ,, S⋆)
      ≈⟨ >>=-≈ (identity-stm (n-disc (suc (tree-dim S₁))))
               (≈-label-comp (replace-label-eq (canonical-label (n-disc (suc (tree-dim S₁))) T)
                                               SHere
                                               (reflexive≈stm (sym≃stm (canonical-label-fst (n-disc (suc (tree-dim S₁))) T))))
                             (++t-inc-left-Ty T S₂)
                             TySStar)
               refl≈sty ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= (canonical-label (n-disc (suc (tree-dim S₁))) T ●l (++t-inc-left T S₂) ,, S⋆)
      ≈˘⟨ reflexive≈stm (>>=-assoc (identity-stm (n-disc (suc (tree-dim S₁))))
                                   (canonical-label (n-disc (suc (tree-dim S₁))) T ,, S⋆) _) ⟩
    identity-stm (n-disc (suc (tree-dim S₁)))
      >>= (canonical-label (n-disc (suc (tree-dim S₁))) T ,, S⋆)
      >>= ++t-inc-left T S₂
      ≈˘⟨ ≈->>= (canonical-ecr (2+ (tree-dim S₁)) T x (s≤s (s≤s z≤n))) (++t-inc-left-Ty T S₂) TySStar ⟩
    canonical-comp (2+ (tree-dim S₁)) T >>= ++t-inc-left T S₂
      ≈˘⟨ reflexive≈stm (>>=-≃ (canonical-comp′-compat (2+ (tree-dim S₁)) T) refl≃l refl≃sty) ⟩
    canonical-comp′ (2+ (tree-dim S₁)) T >>= ++t-inc-left T S₂
      ≈˘⟨ reflexive≈stm (>>=-≃ (canonical-label-max (Susp (Susp S₁)) T (PExt Z)) refl≃l refl≃sty) ⟩
    canonical-label (Susp (Susp S₁)) T (PExt Z) >>= ++t-inc-left T S₂ ∎
    where
      l1 : canonical-label (Susp (Susp S₁)) (n-disc (suc (tree-dim S₁))) (PExt Z)
           ≃stm
           identity-stm (n-disc (suc (tree-dim S₁)))
      l1 = begin
        < canonical-label (Susp (Susp S₁)) (n-disc (suc (tree-dim S₁))) (PExt Z) >stm
          ≈⟨ canonical-label-max (Susp (Susp S₁)) (n-disc (suc (tree-dim S₁))) (PExt Z) ⟩
        < canonical-comp′ (tree-dim (Susp (Susp S₁))) (n-disc (suc (tree-dim S₁))) >stm
          ≈⟨ canonical-comp′-compat (2+ (tree-dim S₁)) (n-disc (suc (tree-dim S₁))) ⟩
        < canonical-comp (2+ (tree-dim S₁)) (n-disc (suc (tree-dim S₁))) >stm
          ≈˘⟨ canonical-comp-≃ (≃n-to-≡ (tree-dim-n-disc {suc (suc (tree-dim S₁))})) refl≃ ⟩
        < canonical-comp (suc (tree-dim (n-disc (suc (tree-dim S₁))))) (n-disc (suc (tree-dim S₁))) >stm
          ≈˘⟨ identity-stm-is-canonical (n-disc (suc (tree-dim S₁))) ⟩
        < identity-stm (n-disc (suc (tree-dim S₁))) >stm ∎
        where
          open Reasoning stm-setoid

      l2 : canonical-label (n-disc (suc (tree-dim S₁))) T (PShift PHere) >>= ++t-inc-left T S₂
           ≃stm
           ap (++t-inc-right T S₂) PHere
      l2 = begin
        < canonical-label (n-disc (suc (tree-dim S₁))) T (PShift PHere) >>= ++t-inc-left T S₂ >stm
          ≈⟨ >>=-≃ (canonical-label-last (n-disc (suc (tree-dim S₁))) T) refl≃l refl≃sty ⟩
        < ap (++t-inc-left T S₂) (last-path T) >stm
          ≈⟨ SPath≃ (++t-inc-phere T S₂) ⟩
        < ap (++t-inc-right T S₂) PHere >stm ∎
        where
          open Reasoning stm-setoid
      open Reasoning stm-setoid-≈
  pruned-branch-κ (Join (Join S₁ Sing) S₂) BHere T q x .get (PShift Z) = refl≈stm

module _ (disc-rem : HasDiscRemoval) where
  open import Catt.Typing.DiscRemoval.Properties rules tame disc-rem

  κ-disc : (S : Tree n)
         → (P : Branch S l)
         → κ S P (n-disc (ih P)) ⦃ has-trunk-height-n-disc (<⇒≤ (bh-<-ih P)) ⦄
           ≈[ ⌊ (S >>[ P ] (n-disc (ih P))) ⦃ _ ⦄ ⌋ ]lm
           ≃-label (sym≃′ (insertion-disc S P)) (id-label S)
  κ-disc (Join S T) BHere .get (PExt Z) = begin
    canonical-label (Susp S) (n-disc (suc (tree-dim S))) (PExt Z)
      >>= ++t-inc-left (n-disc (suc (tree-dim S))) T
      ≈⟨ reflexive≈stm (>>=-≃ (canonical-label-max (Susp S) (n-disc (suc (tree-dim S))) (PExt Z))
                              refl≃l
                              refl≃sty) ⟩
    canonical-comp′ (tree-dim (Susp S)) (n-disc (suc (tree-dim S)))
      >>= ++t-inc-left (n-disc (suc (tree-dim S))) T
      ≈˘⟨ reflexive≈stm (>>=-≃ (canonical-comp′-≃ (≃n-to-≡ (tree-dim-n-disc {n = suc (tree-dim S)}))
                                                  (refl≃ {T = n-disc (suc (tree-dim S))}))
                               (refl≃l {L = ap (++t-inc-left (n-disc (suc (tree-dim S))) T)})
                               refl≃sty) ⟩
    canonical-comp′ (tree-dim (n-disc (suc (tree-dim S)))) (n-disc (suc (tree-dim S)))
      >>= ++t-inc-left (n-disc (suc (tree-dim S))) T
      ≈⟨ reflexive≈stm (>>=-≃ (canonical-comp′-compat (tree-dim (n-disc (suc (tree-dim S))))
                                                      (n-disc (suc (tree-dim S))))
                              (refl≃l {L = ap (++t-inc-left (n-disc (suc (tree-dim S))) T)})
                              refl≃sty) ⟩
    canonical-comp (tree-dim (n-disc (suc (tree-dim S)))) (n-disc (suc (tree-dim S)))
      >>= ++t-inc-left (n-disc (suc (tree-dim S))) T
      ≈˘⟨ reflexive≈stm (>>=-≃ (disc-stm-is-canonical (n-disc (suc (tree-dim S))))
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
  open import Catt.Typing.DiscRemoval.Properties rules tame dr

  κ-canonical-type : (S : Tree n)
                   → (P : Branch S l)
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height l T ⦄
                   → (d : ℕ)
                   → (tree-dim T ≤ ih P)
                   → canonical-type d S >>=′ (κ S P T ,, S⋆)
                     ≈[ ⌊ S >>[ P ] T ⌋ ]sty
                     canonical-type d (S >>[ P ] T)
  κ-canonical-comp : (S : Tree n)
                   → (P : Branch S l)
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height l T ⦄
                   → (d : ℕ)
                   → (tree-dim T ≤ ih P)
                   → canonical-comp d S >>= (κ S P T ,, S⋆)
                     ≈[ ⌊ S >>[ P ] T ⌋ ]stm
                     canonical-comp d (S >>[ P ] T)
  κ-canonical-comp′ : (S : Tree n)
                    → (P : Branch S l)
                    → (T : Tree m)
                    → .⦃ _ : has-trunk-height l T ⦄
                    → (d : ℕ)
                    → (tree-dim T ≤ ih P)
                    → canonical-comp′ d S >>= (κ S P T ,, S⋆)
                      ≈[ ⌊ S >>[ P ] T ⌋ ]stm
                      canonical-comp′ d (S >>[ P ] T)
  κ-canonical-stm : (S : Tree n)
                  → (P : Branch S l)
                  → (T : Tree m)
                  → .⦃ _ : has-trunk-height l T ⦄
                  → (d : ℕ)
                  → d ≥ tree-dim S
                  → tree-dim T ≤ ih P
                  → canonical-stm d S >>= (κ S P T ,, S⋆)
                    ≈[ ⌊ S >>[ P ] T ⌋ ]stm
                    canonical-stm d (S >>[ P ] T)

  κ-canonical-type S P T zero q = refl≈sty
  κ-canonical-type S P T (suc d) q
    = ≈SArr (lem false)
            (κ-canonical-type S P T d q)
            (lem true)
    where
      open Reasoning stm-setoid-≈

      lem3 : (x : Condition d T (ih P)) → tree-dim (tree-bd d T) ≤
               ih (bd-branch S P d (bd-branch-lem P x))
      lem3 x = (≤-trans (≤-reflexive (tree-dim-bd d T))
                        (≤-trans (⊓-monoʳ-≤ d q)
                                 (≤-reflexive (sym (bd-branch-height S P d (bd-branch-lem P x))))))

      lem2 : (b : Bool)
           → Bd-Conditions d P T
           → canonical-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆)
             ≈[ ⌊ S >>[ P ] T ⌋ ]stm
             canonical-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b
      lem2 b (Bd-Cond1 x y) = begin
        canonical-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆)
          ≈⟨ >>=-≈ (canonical-stm d (tree-bd d S))
                   (label-max-equality-to-equality (canonical-κ-comm-1 S P T d x y q b)
                                                   (label-comp-Ty (tree-inc-Ty d S b) (κ-Ty S P T) TySStar)
                                                   (label-≃-Ty (insertion-bd-1 S P T d y q) (tree-inc-Ty d (S >>[ P ] T) b)))
                   refl≈sty ⟩
        canonical-stm d (tree-bd d S) >>=
          label-wt-≃ (insertion-bd-1 S P T d y q) (tree-inc-label d (S >>[ P ] T) b)
          ≈˘⟨ reflexive≈stm (>>=-assoc (canonical-stm d (tree-bd d S)) _ _) ⟩
        canonical-stm d (tree-bd d S) >>= (SPath ∘ ppath-≃ (insertion-bd-1 S P T d y q) ,, S⋆) >>= tree-inc-label d (S >>[ P ] T) b
          ≈⟨ reflexive≈stm (>>=-≃ (canonical-stm-≃-prop d (insertion-bd-1 S P T d y q)) refl≃l refl≃sty) ⟩
        canonical-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b ∎
      lem2 b (Bd-Cond2 x) = begin
        canonical-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆)
          ≈⟨ >>=-≈ (canonical-stm d (tree-bd d S))
                   (label-max-equality-to-equality
                     (canonical-κ-comm-2 S P T d b q x)
                     (label-comp-Ty (tree-inc-Ty d S b) (κ-Ty S P T) TySStar)
                     (label-comp-Ty (κ-Ty (tree-bd d S)
                                                       (bd-branch S P d _)
                                                       (tree-bd d T)
                                                       ⦃ _ ⦄)
                                    (label-≃-Ty (insertion-bd-2 S P T d _) (tree-inc-Ty d (S >>[ P ] T) b)) TySStar))
                   refl≈sty ⟩
        canonical-stm d (tree-bd d S)
          >>= (κ (tree-bd d S)
                              (bd-branch S P d _)
                              (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
          ●lt (label-wt-≃ (insertion-bd-2 S P T d _)
                          (tree-inc-label d (S >>[ P ] T) b))
          ≈˘⟨ reflexive≈stm (>>=-assoc (canonical-stm d (tree-bd d S))
                                       (κ (tree-bd d S)
                                                       (bd-branch S P d _)
                                                       (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
                                       (_ ,, S⋆)) ⟩
        canonical-stm d (tree-bd d S)
          >>= (κ (tree-bd d S) (bd-branch S P d _) (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
          >>= label-wt-≃ (insertion-bd-2 S P T d _) (tree-inc-label d (S >>[ P ] T) b)
          ≈⟨ ≈->>= (κ-canonical-stm (tree-bd d S)
                                           (bd-branch S P d (bd-branch-lem P x))
                                           (tree-bd d T)
                                           ⦃ _ ⦄
                                           d
                                           (tree-dim-bd″ d S)
                                           (lem3 x))
                   (label-≃-Ty (insertion-bd-2 S P T d _) (tree-inc-Ty d (S >>[ P ] T) b))
                   TySStar ⟩
        canonical-stm d ((tree-bd d S >>[ bd-branch S P d _ ] tree-bd d T) ⦃ _ ⦄)
          >>= label-wt-≃ (insertion-bd-2 S P T d _)
                         (tree-inc-label d (S >>[ P ] T) b)
          ≈˘⟨ reflexive≈stm (>>=-assoc (canonical-stm d ((tree-bd d S >>[ bd-branch S P d _ ] tree-bd d T) ⦃ _ ⦄))
                            (SPath ∘ ppath-≃ (insertion-bd-2 S P T d _) ,, S⋆)
                            (tree-inc-label d (S >>[ P ] T) b)) ⟩
        canonical-stm d ((tree-bd d S >>[ bd-branch S P d _ ] tree-bd d T) ⦃ _ ⦄)
          >>= ((SPath ∘ ppath-≃ (insertion-bd-2 S P T d _)) ,, S⋆)
          >>= tree-inc-label d (S >>[ P ] T) b
          ≈⟨ reflexive≈stm (>>=-≃ (canonical-stm-≃-prop d (insertion-bd-2 S P T d _)) refl≃l refl≃sty) ⟩
        canonical-stm d (tree-bd d (S >>[ P ] T))
          >>= tree-inc-label d (S >>[ P ] T) b ∎

      lem : (b : Bool)
          → canonical-stm d (tree-bd d S) >>= tree-inc-label d S b >>= (κ S P T ,, S⋆)
            ≈[ ⌊ S >>[ P ] T ⌋ ]stm
            canonical-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b
      lem b = begin
        canonical-stm d (tree-bd d S) >>= tree-inc-label d S b >>= (κ S P T ,, S⋆)
          ≈⟨ reflexive≈stm (>>=-assoc (canonical-stm d (tree-bd d S)) _ _) ⟩
        canonical-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆)
          ≈⟨ lem2 b (Bd-Conditions-one-of d P T) ⟩
        canonical-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b ∎

  κ-canonical-comp S P T d p = begin
    SCoh S (canonical-type d S) (κ S P T ,, S⋆)
      ≈⟨ insert (canonical-type d S)
                (κ S P T)
                P
                (ι S P T)
                (κ-branch-path S P T)
                (TySCoh S (canonical-type-Ty d S) (κ-Ty S P T) TySStar) ⟩
    SCoh (S >>[ P ] T)
         (canonical-type d S >>=′ (κ S P T ,, S⋆))
         (κ S P T >>l[ P ] ι S P T ,, S⋆)
      ≈⟨ ≈SCoh (S >>[ P ] T)
               (κ-canonical-type S P T d p)
               (reflexive≈l (κ-ι-prop S P T)) refl≈sty ⟩
    SCoh (S >>[ P ] T) (canonical-type d (S >>[ P ] T)) (id-label-wt _) ∎
    where
      open Reasoning stm-setoid-≈

  κ-canonical-comp′ S P T d p = begin
    canonical-comp′ d S >>= (κ S P T ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-≃ (canonical-comp′-compat d S) refl≃l refl≃sty) ⟩
    canonical-comp d S >>= (κ S P T ,, S⋆)
      ≈⟨ κ-canonical-comp S P T d p ⟩
    canonical-comp d (S >>[ P ] T)
      ≈˘⟨ reflexive≈stm (canonical-comp′-compat d (S >>[ P ] T)) ⟩
    canonical-comp′ d (S >>[ P ] T) ∎
    where
      open Reasoning stm-setoid-≈

  κ-canonical-stm S@(Join _ _) P T d q p = begin
    canonical-stm d S >>= (κ S P T ,, S⋆)
      ≈⟨ ≈->>= (canonical-stm-is-comp d ⦃ NonZero-≤ q it ⦄ S) (κ-Ty S P T) TySStar ⟩
    canonical-comp d S >>= (κ S P T ,, S⋆)
      ≈⟨ κ-canonical-comp S P T d p ⟩
    canonical-comp d (S >>[ P ] T)
      ≈˘⟨ canonical-stm-is-comp d ⦃ NonZero-≤ q it ⦄ (S >>[ P ] T) ⟩
    canonical-stm d (S >>[ P ] T) ∎
    where
      open Reasoning stm-setoid-≈


  κ-inserted-branch : (S : Tree n)
                    → (P : Branch S l)
                    → (T : Tree m)
                    → .⦃ _ : has-trunk-height l T ⦄
                    → .⦃ _ : non-linear T ⦄
                    → (Q : Branch T l′)
                    → (U : Tree m′)
                    → .⦃ _ : has-trunk-height l′ U ⦄
                    → tree-dim U ≤ ih Q
                    → κ S P T ●l (κ (S >>[ P ] T) (inserted-branch S P T Q) U ,, S⋆)
                      ≈[ ⌊ (S >>[ P ] T) >>[ inserted-branch S P T Q ] U ⌋ ]lm
                      ≃-label (sym≃′ (insertion-tree-inserted-branch S P T Q U)) (κ S P (T >>[ Q ] U) ⦃ insertion-trunk-height T Q U l ⦄)
  κ-inserted-branch (Join S₁ S₂) BHere T Q U q .get (PExt Z) = begin
    canonical-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂
      >>= (κ (T ++t S₂) (connect-branch-left T S₂ Q) U ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-assoc (canonical-label (Susp S₁) T (PExt Z)) _ _) ⟩
    canonical-label (Susp S₁) T (PExt Z)
      >>= ++t-inc-left T S₂ ●lt (κ (T ++t S₂) (connect-branch-left T S₂ Q) U ,, S⋆)
      ≈⟨ fixup-reflexive≈stm (>>=-≃ (canonical-label-max (Susp S₁) T (PExt Z))
                                    (κ-branch-left-inc-left T S₂ Q U)
                                    (S⋆-≃ (≃′-to-≃ (insertion-branch-left T S₂ Q U))))
                             (insertion-branch-left T S₂ Q U) ⟩
    stm-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
      (canonical-comp′ (1 + tree-dim S₁) T
        >>= (κ T Q U ,, S⋆) ●lt (++t-inc-left (T >>[ Q ] U) S₂))
      ≈˘⟨ reflexive≈stm (stm-≃-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
                                 (>>=-assoc (canonical-comp′ (1 + tree-dim S₁) T) (κ T Q U ,, S⋆) _)) ⟩
    stm-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
      (canonical-comp′ (1 + tree-dim S₁) T >>= (κ T Q U ,, S⋆)
                                           >>= ++t-inc-left (T >>[ Q ] U) S₂)
      ≈⟨ stm-≃-≈ ((sym≃′ (insertion-branch-left T S₂ Q U)))
                 (≈->>= (κ-canonical-comp′ T Q U (1 + tree-dim S₁) q)
                        (++t-inc-left-Ty (T >>[ Q ] U) S₂)
                        TySStar) ⟩
    stm-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
      (canonical-comp′ (1 + tree-dim S₁) (T >>[ Q ] U)
        >>= ++t-inc-left (T >>[ Q ] U) S₂)
      ≈˘⟨ stm-≃-≈ (sym≃′ (insertion-branch-left T S₂ Q U))
                  (reflexive≈stm (>>=-≃ (canonical-label-max (Susp S₁) (T >>[ Q ] U) (PExt Z)) refl≃l refl≃sty)) ⟩
    stm-≃ (sym≃′ (insertion-branch-left T S₂ Q U))
         (canonical-label (Susp S₁) (T >>[ Q ] U) (PExt Z)
           >>= ++t-inc-left (T >>[ Q ] U) S₂) ∎
    where
      open Reasoning stm-setoid-≈
  κ-inserted-branch (Join S₁ S₂) BHere T Q U q .get (PShift Z)
    = fixup-reflexive≈stm (κ-branch-left-inc-right T S₂ Q U .get Z) (insertion-branch-left T S₂ Q U)
  κ-inserted-branch (Join S₁ S₂) (BExt P) (Susp T) BHere U q = ⊥-elim (linear-non-linear T)
  κ-inserted-branch (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Join U Sing) q .get (PExt Z) = begin
    (κ S₁ P T Z >>= map-ext (κ (S₁ >>[ P ] T) (inserted-branch S₁ P T Q) U ,, S⋆))
      ≈⟨ reflexive≈stm (>>=-ext (κ S₁ P T Z) (κ (S₁ >>[ P ] T) (inserted-branch S₁ P T Q) U ,, S⋆)) ⟩
    SExt (κ S₁ P T Z >>= (κ (S₁ >>[ P ] T) (inserted-branch S₁ P T Q) U ,, S⋆))
      ≈⟨ ≈SExt (κ-inserted-branch S₁ P T Q U (≤-pred q) .get Z) ⟩
    SExt (stm-≃ (sym≃′ (insertion-tree-inserted-branch S₁ P T Q U)) (κ S₁ P (T >>[ Q ] U) ⦃ insertion-trunk-height T Q U (bh P) ⦄ Z)) ∎
    where
      open Reasoning stm-setoid-≈
  κ-inserted-branch (Join S₁ S₂) (BExt P) (Susp T) (BExt Q) (Join U Sing) q .get (PShift Z) = ≈SShift refl≈stm
  κ-inserted-branch (Join S₁ S₂) (BShift P) T Q U q .get (PExt Z) = ≈SExt refl≈stm
  κ-inserted-branch (Join S₁ S₂) (BShift P) T Q U q .get (PShift Z) = begin
    (κ S₂ P T Z
      >>= map-shift (κ (S₂ >>[ P ] T) (inserted-branch S₂ P T Q) U ,, S⋆))
      ≈⟨ reflexive≈stm (>>=-shift (κ S₂ P T Z) _) ⟩
    SShift (κ S₂ P T Z >>= (κ (S₂ >>[ P ] T) (inserted-branch S₂ P T Q) U ,, S⋆))
      ≈⟨ ≈SShift (κ-inserted-branch S₂ P T Q U q .get Z) ⟩
    SShift (stm-≃ (sym≃′ (insertion-tree-inserted-branch S₂ P T Q U)) (κ S₂ P (T >>[ Q ] U) ⦃ insertion-trunk-height T Q U (bh P) ⦄ Z)) ∎
    where
      open Reasoning stm-setoid-≈
