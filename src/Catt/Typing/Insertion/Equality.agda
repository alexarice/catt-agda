open import Catt.Typing.Rule

module Catt.Typing.Insertion.Equality {index : Set}
                                  (rule : index → Rule)
                                  (lift-rule : ∀ i → LiftRule rule (rule i))
                                  (susp-rule : ∀ i → SuspRule rule (rule i))
                                  (sub-rule : ∀ i → SubRule rule (rule i)) where

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

open import Catt.Typing rule
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Suspension.Typing rule lift-rule susp-rule
open import Catt.Connection.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Boundary.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Structured.Typing rule
open import Catt.Tree.Structured.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Canonical.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Insertion.Typing rule lift-rule susp-rule sub-rule
open import Catt.Typing.DiscRemoval rule
open import Catt.Typing.EndoCoherenceRemoval rule
open import Catt.Typing.Insertion rule


-- module _ (ecr : HasEndoCoherenceRemoval) (dr : HasDiscRemoval) where
--   open import Catt.Typing.DiscRemoval.Properties rule lift-rule susp-rule sub-rule dr
--   open import Catt.Typing.EndoCoherenceRemoval.Properties rule lift-rule susp-rule sub-rule ecr

--   canonical-ecr : (d : ℕ)
--                → (T : Tree n)
--                → (tree-dim T < d)
--                → (1 < d)
--                → canonical-comp d T ≈[ tree-to-ctx T ]stm (identity-stm (pred d) >>= (canonical-label (n-disc (pred d)) T 0 ,, S⋆))
--   canonical-ecr (suc d) T p q = let
--     instance _ = n-disc-is-linear (sty-dim (canonical-type d T))
--     instance _ = n-disc-is-linear d
--     in begin
--     SCoh T
--          (SArr (canonical-stm d (tree-bd d T) >>=
--                                (tree-inc-label d T false))
--                (canonical-type d T)
--                (canonical-stm d (tree-bd d T) >>=
--                                (tree-inc-label d T true)))
--          (id-label-wt T)
--       ≈⟨ reflexive≈stm (SCoh≃ T (SArr≃ (canonical-stm-full-lem d T false (≤-pred p))
--                                        refl≃sty
--                                        (canonical-stm-full-lem d T true (≤-pred p)))
--                                 refl≃l
--                                 refl≃sty) ⟩
--     SCoh T (SArr (canonical-stm d T)
--                  (canonical-type d T)
--                  (canonical-stm d T))
--            (id-label-wt T)
--       ≈⟨ ecr-stm T (canonical-stm d T) (canonical-type d T) (id-label T) (canonical-stm-Ty d T) (canonical-type-Ty d T) (id-label-Ty T) ⟩
--     (identity-stm (sty-dim (canonical-type d T)) >>=
--       (label-from-linear-tree (n-disc (sty-dim (canonical-type d T)))
--                                             (canonical-stm d T)
--                                             (canonical-type d T) _ ,, S⋆)
--       ●lt (id-label T ,, S⋆))
--       ≈⟨ reflexive≈stm (>>=-≃ (refl≃stm {a = identity-stm (sty-dim (canonical-type d T))}) (comp-right-unit ((label-from-linear-tree (n-disc (sty-dim (canonical-type d T)))
--                                             (canonical-stm d T)
--                                             (canonical-type d T) _))) refl≃sty) ⟩
--     (identity-stm (sty-dim (canonical-type d T)) >>=
--                   (label-from-linear-tree (n-disc (sty-dim (canonical-type d T)))
--                                          (canonical-stm d T)
--                                          (canonical-type d T) _ ,, S⋆))
--       ≈⟨ ≈->>= (identity-stm (sty-dim (canonical-type d T))) (label-from-linear-tree-≈ (n-disc (sty-dim (canonical-type d T))) (canonical-stm-is-comp′ d ⦃ NonZero-≤ (≤-pred q) it ⦄ T) refl≈sty _) refl≈sty ⟩
--     (identity-stm (sty-dim (canonical-type d T)) >>=
--                   (label-from-linear-tree (n-disc (sty-dim (canonical-type d T)))
--                                          (canonical-comp′ d T)
--                                          (canonical-type d T) _ ,, S⋆))
--       ≈⟨ reflexive≈stm (>>=-≃ (refl≃stm {a = identity-stm (sty-dim (canonical-type d T))}) (label-from-linear-tree-canonical-lem-0 (n-disc (sty-dim (canonical-type d T))) T d (trans (tree-dim-n-disc (sty-dim (canonical-type d T))) (canonical-type-dim d T))) refl≃sty) ⟩
--     (identity-stm (sty-dim (canonical-type d T)) >>=
--                   (label-from-linear-tree-canonical (n-disc (sty-dim (canonical-type d T))) T 0 ,, S⋆))
--       ≈⟨ reflexive≈stm (reflexive≃stm (cong (λ x → (identity-stm x >>=
--                   (label-from-linear-tree-canonical (n-disc x) ⦃ n-disc-is-linear x ⦄ T 0 ,, S⋆))) (canonical-type-dim d T))) ⟩
--     (identity-stm d >>= (label-from-linear-tree-canonical (n-disc d) T 0 ,, S⋆)) ∎
--     where
--       open Reasoning stm-setoid-≈

--   pruned-bp-exterior-sub : (S : Tree n)
--                          → (p : BranchingPoint S l)
--                          → (T : Tree m)
--                          → .⦃ _ : has-linear-height l T ⦄
--                          → .(q : bp-height p < pred (height-of-branching p))
--                          → (x : tree-dim T < height-of-branching p)
--                          → label-max-equality
--                            (tree-to-ctx (insertion-tree (prune-tree S p) (pruned-bp S p q) T))
--                            (exterior-sub-label S
--                                                p
--                                                (n-disc (pred (height-of-branching p)))
--                                                ⦃ is-linear-has-linear-height l (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))) ⦄
--                            ●l (exterior-sub-label (prune-tree S p) (pruned-bp S p q) T ,, S⋆))
--                             (≃-label (sym≃′ (insertion-tree-pruned-bp S p T q)) (exterior-sub-label S p T))
--   pruned-bp-exterior-sub (Join S₁ S₂) (BPExt p) (Join T Sing) q x .get (PExt Z) = let
--     instance .y : _
--     y = is-linear-has-linear-height (bp-height p) (n-disc (height-of-branching′ p)) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ (≤-pred q)) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p))))))

--     in begin
--     (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z >>=
--           ((SExt ∘ exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
--                                         (pruned-bp S₁ p _) T)
--           ,, SArr (SPath PHere) S⋆ (SShift (SPath PHere))))
--       ≈⟨ reflexive≈stm (>>=-≃ (refl≃stm {a = exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z}) refl≃l (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm))) ⟩
--     (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z >>=
--           (map-ext (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
--                                         (pruned-bp S₁ p _) T ,, S⋆)))
--       ≈⟨ reflexive≈stm (>>=-ext (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z) (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
--                                         (pruned-bp S₁ p _) T ,, S⋆)) ⟩
--     SExt (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) Z
--          >>= (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
--                                  (pruned-bp S₁ p _) T ,, S⋆))
--       ≈⟨ ≈SExt (pruned-bp-exterior-sub S₁ p T (≤-pred q) (≤-pred x) .get Z) ⟩
--     SExt (≃-label (sym≃′ (insertion-tree-pruned-bp S₁ p T _)) (exterior-sub-label S₁ p T) Z) ∎
--     where
--       open Reasoning stm-setoid-≈
--   pruned-bp-exterior-sub (Join S₁ S₂) (BPExt p) (Join T Sing) q x .get (PShift Z) = refl≈stm
--   pruned-bp-exterior-sub (Join S₁ S₂) (BPShift p) T q x .get (PExt Z) = refl≈stm
--   pruned-bp-exterior-sub (Join S₁ S₂) (BPShift p) T q x .get (PShift Z) = let
--     instance .y : _
--     y = is-linear-has-linear-height (bp-height p) (n-disc (height-of-branching′ p)) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p))))))
--     in begin
--     (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z
--       >>= map-shift (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
--                                         (pruned-bp S₂ p _) T ,, S⋆))
--       ≈⟨ reflexive≈stm (>>=-shift (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z) (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
--                                         (pruned-bp S₂ p _) T ,, S⋆)) ⟩
--     SShift (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) Z
--       >>= (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
--                               (pruned-bp S₂ p _) T ,, S⋆))
--       ≈⟨ ≈SShift (pruned-bp-exterior-sub S₂ p T q x .get Z) ⟩
--     SShift (≃-label (sym≃′ (insertion-tree-pruned-bp S₂ p T _))
--                     (exterior-sub-label S₂ p T) Z) ∎
--     where
--       open Reasoning stm-setoid-≈
--   pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q x .get (PExt Z) = let
--     instance _ = n-disc-is-linear (tree-dim S₁)
--     in begin
--     (label-from-linear-tree-canonical (susp-tree S₁) (Join (n-disc (tree-dim S₁)) Sing) 1 Z
--       >>= connect-tree-inc-left (Join (n-disc (tree-dim S₁)) Sing) S₂
--       >>= (connect-label (label-from-linear-tree-canonical (Join (n-disc (tree-dim S₁)) Sing) T 0
--                           ●l (connect-tree-inc-left T S₂))
--                         (ap (connect-tree-inc-right T S₂)) ,, S⋆))
--       ≈⟨ reflexive≈stm (>>=-≃ (>>=-≃ (lfltu-maximal-path (susp-tree S₁) (Join (n-disc (tree-dim S₁)) Sing) 1 Z) refl≃l refl≃sty) refl≃l refl≃sty) ⟩
--     (canonical-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁))
--       >>= ((SPath ∘ PExt) ,, SArr (SPath PHere) S⋆ (SPath (PShift PHere)))
--       >>= (connect-label (label-from-linear-tree-canonical (Join (n-disc (tree-dim S₁)) Sing) T 0
--                           ●l (connect-tree-inc-left T S₂))
--                         (ap (connect-tree-inc-right T S₂)) ,, S⋆))
--       ≈⟨ reflexive≈stm (>>=-assoc (canonical-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁))) _ _) ⟩
--     (canonical-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁)) >>=
--           ((label-from-linear-tree-canonical (n-disc (tree-dim S₁)) T 1 ,, SArr SHere S⋆ (SPath (last-path T)))
--            ●lt (connect-tree-inc-left T S₂)))
--       ≈˘⟨ reflexive≈stm (>>=-assoc (canonical-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁))) _ _) ⟩
--     (canonical-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁))
--       >>= (label-from-linear-tree-canonical (n-disc (tree-dim S₁)) T 1 ,, SArr SHere S⋆ (SPath (last-path T)))
--       >>= connect-tree-inc-left T S₂)
--       ≡⟨⟩
--     (identity-stm (suc (tree-dim S₁))
--       >>= (label-from-linear-tree-canonical (n-disc (suc (tree-dim S₁))) T 0 ,, S⋆)
--       >>= connect-tree-inc-left T S₂)
--       ≈˘⟨ >>=-≈ (canonical-ecr (suc (suc (tree-dim S₁))) T x (s≤s (s≤s z≤n))) (connect-tree-inc-left-Ty T S₂) TySStar ⟩
--     (canonical-comp (2 + tree-dim S₁) T >>= (connect-tree-inc-left T S₂))
--       ≈˘⟨ reflexive≈stm (>>=-≃ (canonical-comp′-compat (2 + tree-dim S₁) T) refl≃l refl≃sty) ⟩
--     (canonical-comp′ (suc (suc (tree-dim S₁))) T >>=
--           (connect-tree-inc-left T S₂))
--       ≈˘⟨ reflexive≈stm (>>=-≃ (lfltu-maximal-path (Join S₁ Sing) T 1 Z) refl≃l refl≃sty) ⟩
--     (label-from-linear-tree-canonical (Join S₁ Sing) T 1 Z >>=
--           (connect-tree-inc-left T S₂)) ∎
--     where
--       open Reasoning stm-setoid-≈
--   pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q x .get (PShift Z) = reflexive≈stm (>>=-≃ (replace-not-here (SPath ∘ PShift) (SPath (PShift PHere)) Z) refl≃l refl≃sty)


module _ (disc-rem : HasDiscRemoval) where
  open import Catt.Typing.DiscRemoval.Properties rule lift-rule susp-rule sub-rule disc-rem

  exterior-disc : (S : Tree n)
                → (p : BranchingPoint S l)
                → exterior-label S p (n-disc (height-of-branching p))
                                     ⦃ has-trunk-height-n-disc (<⇒≤ (bp-height-<-hob p)) ⦄
                  ≈[ tree-to-ctx (insertion-tree S p (n-disc (height-of-branching p)) ⦃ _ ⦄) ]lm
                  ≃-label (sym≃′ (insertion-disc S p)) (id-label S)
  exterior-disc (Join S T) BPHere .get (PExt Z) = begin
    canonical-label (susp S) (n-disc (suc (tree-dim S))) (PExt Z)
      >>= connect-tree-inc-left (n-disc (suc (tree-dim S))) T
      ≈⟨ reflexive≈stm (>>=-≃ (canonical-label-max (susp S) (n-disc (suc (tree-dim S))) (PExt Z))
                              refl≃l
                              refl≃sty) ⟩
    canonical-comp′ (tree-dim (susp S)) (n-disc (suc (tree-dim S)))
      >>= connect-tree-inc-left (n-disc (suc (tree-dim S))) T
      ≈˘⟨ reflexive≈stm (>>=-≃ (canonical-comp′-≃ (≃n-to-≡ (tree-dim-n-disc {n = suc (tree-dim S)}))
                                                  (refl≃ {T = n-disc (suc (tree-dim S))}))
                               (refl≃l {L = ap (connect-tree-inc-left (n-disc (suc (tree-dim S))) T)})
                               refl≃sty) ⟩
    canonical-comp′ (tree-dim (n-disc (suc (tree-dim S)))) (n-disc (suc (tree-dim S)))
      >>= connect-tree-inc-left (n-disc (suc (tree-dim S))) T
      ≈⟨ reflexive≈stm (>>=-≃ (canonical-comp′-compat (tree-dim (n-disc (suc (tree-dim S))))
                                                      (n-disc (suc (tree-dim S))))
                              (refl≃l {L = ap (connect-tree-inc-left (n-disc (suc (tree-dim S))) T)})
                              refl≃sty) ⟩
    canonical-comp (tree-dim (n-disc (suc (tree-dim S)))) (n-disc (suc (tree-dim S)))
      >>= connect-tree-inc-left (n-disc (suc (tree-dim S))) T
      ≈˘⟨ reflexive≈stm (>>=-≃ (disc-stm-is-canonical (n-disc (suc (tree-dim S))))
                               (refl≃l {L = ap (connect-tree-inc-left (n-disc (suc (tree-dim S))) T)})
                               refl≃sty) ⟩
    disc-stm (n-disc (suc (tree-dim S))) >>= connect-tree-inc-left (susp (n-disc (tree-dim S))) T
      ≈⟨ disc-rem-stm (n-disc (suc (tree-dim S)))
                      (ap (connect-tree-inc-left (susp (n-disc (tree-dim S))) T))
                      (connect-tree-inc-left-Ty (n-disc (suc (tree-dim S))) T) ⟩
    ap (connect-tree-inc-left (susp (n-disc (tree-dim S))) T) (is-linear-max-path (n-disc (suc (tree-dim S))))
      ≡⟨⟩
    SPath (PExt (is-linear-max-path (n-disc (tree-dim S))))
      ≈⟨ reflexive≈stm (SPath≃ (Ext≃ (trans≃p (max-path-lin-tree (n-disc (tree-dim S))
                                                                 Z
                                                                 (≃′-to-≃ (linear-tree-unique (n-disc (tree-dim S)) S (≃n-to-≡ tree-dim-n-disc))))
                                              (ppath-≃-≃p (sym≃′ (linear-tree-unique (n-disc (tree-dim S)) S _)) Z)) refl≃)) ⟩
    SPath (PExt (ppath-≃ (sym≃′ (linear-tree-unique (n-disc (tree-dim S)) S _)) Z)) ∎
    where
      open Reasoning stm-setoid-≈
  exterior-disc (Join S T) BPHere .get (PShift Z) = refl≈stm
  exterior-disc (Join S T) (BPExt p) .get (PExt Z)
    = compute-≈ (≈SExt (trans≈stm (exterior-disc S p .get Z) (reflexive≈stm (stm-≃-spath (sym≃′ (insertion-disc S p)) Z))))
  exterior-disc (Join S T) (BPExt p) .get (PShift Z) = compute-≈ refl≈stm
  exterior-disc (Join S T) (BPShift p) .get (PExt Z) = compute-≈ refl≈stm
  exterior-disc (Join S T) (BPShift p) .get (PShift Z)
    = compute-≈ (≈SShift (trans≈stm (exterior-disc T p .get Z) (reflexive≈stm (stm-≃-spath (sym≃′ (insertion-disc T p)) Z))))

module _ (dr : HasDiscRemoval) (insert : HasInsertion) where
  open import Catt.Typing.DiscRemoval.Properties rule lift-rule susp-rule sub-rule dr

  exterior-canonical-type : (S : Tree n)
                          → (P : BranchingPoint S l)
                          → (T : Tree m)
                          → .⦃ _ : has-trunk-height l T ⦄
                          → (d : ℕ)
                          → (tree-dim T ≤ height-of-branching P)
                          → (canonical-type d S >>=′ (exterior-label S P T ,, S⋆))
                            ≈[ tree-to-ctx (insertion-tree S P T) ]sty
                            canonical-type d (insertion-tree S P T)
  exterior-canonical-comp : (S : Tree n)
                          → (P : BranchingPoint S l)
                          → (T : Tree m)
                          → .⦃ _ : has-trunk-height l T ⦄
                          → (d : ℕ)
                          → (tree-dim T ≤ height-of-branching P)
                          → canonical-comp d S >>= (exterior-label S P T ,, S⋆)
                            ≈[ tree-to-ctx (insertion-tree S P T) ]stm
                            canonical-comp d (insertion-tree S P T)
  exterior-canonical-comp′ : (S : Tree n)
                           → (P : BranchingPoint S l)
                           → (T : Tree m)
                           → .⦃ _ : has-trunk-height l T ⦄
                           → (d : ℕ)
                           → (tree-dim T ≤ height-of-branching P)
                           → canonical-comp′ d S >>= (exterior-label S P T ,, S⋆)
                             ≈[ tree-to-ctx (insertion-tree S P T) ]stm
                             canonical-comp′ d (insertion-tree S P T)
  exterior-canonical-stm : (S : Tree n)
                         → (P : BranchingPoint S l)
                         → (T : Tree m)
                         → .⦃ _ : has-trunk-height l T ⦄
                         → (d : ℕ)
                         → d ≥ tree-dim S
                         → (tree-dim T ≤ height-of-branching P)
                         → canonical-stm d S >>= (exterior-label S P T ,, S⋆)
                           ≈[ tree-to-ctx (insertion-tree S P T) ]stm
                           canonical-stm d (insertion-tree S P T)

  exterior-canonical-type S P T zero q = refl≈sty
  exterior-canonical-type S P T (suc d) q
    = ≈SArr (lem false)
            (exterior-canonical-type S P T d q)
            (lem true)
    where
      open Reasoning stm-setoid-≈

      lem3 : (x : Condition d T (height-of-branching P)) → tree-dim (tree-bd d T) ≤
               height-of-branching (bd-branching-point S P d (bd-bp-lem P x))
      lem3 x = (≤-trans (≤-reflexive (tree-dim-bd d T))
                        (≤-trans (⊓-monoʳ-≤ d q)
                                 (≤-reflexive (sym (bd-branching-point-height S P d (bd-bp-lem P x))))))

      lem2 : (b : Bool)
           → Bd-Conditions d P T
           → canonical-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (exterior-label S P T ,, S⋆)
             ≈[ tree-to-ctx (insertion-tree S P T) ]stm
             canonical-stm d (tree-bd d (insertion-tree S P T)) >>= tree-inc-label d (insertion-tree S P T) b
      lem2 b (Bd-Cond1 x y) = begin
        canonical-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (exterior-label S P T ,, S⋆)
          ≈⟨ ≈->>= (canonical-stm d (tree-bd d S))
                   (label-max-equality-to-equality (canonical-exterior-comm-1 S P T d x y q b)
                                                   (label-comp-Ty (tree-inc-Ty d S b) (exterior-label-Ty S P T) TySStar)
                                                   (label-≃-Ty (insertion-bd-1 S P T d y q) (tree-inc-Ty d (insertion-tree S P T) b)))
                   refl≈sty ⟩
        canonical-stm d (tree-bd d S) >>=
          label-wt-≃ (insertion-bd-1 S P T d y q) (tree-inc-label d (insertion-tree S P T) b)
          ≈˘⟨ reflexive≈stm (>>=-assoc (canonical-stm d (tree-bd d S)) _ _) ⟩
        canonical-stm d (tree-bd d S) >>= (SPath ∘ ppath-≃ (insertion-bd-1 S P T d y q) ,, S⋆) >>= tree-inc-label d (insertion-tree S P T) b
          ≈⟨ reflexive≈stm (>>=-≃ (canonical-stm-≃-prop d (insertion-bd-1 S P T d y q)) refl≃l refl≃sty) ⟩
        canonical-stm d (tree-bd d (insertion-tree S P T)) >>= tree-inc-label d (insertion-tree S P T) b ∎
      lem2 b (Bd-Cond2 x) = begin
        canonical-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (exterior-label S P T ,, S⋆)
          ≈⟨ ≈->>= (canonical-stm d (tree-bd d S))
                   (label-max-equality-to-equality
                     (canonical-exterior-comm-2 S P T d b q x)
                     (label-comp-Ty (tree-inc-Ty d S b) (exterior-label-Ty S P T) TySStar)
                     (label-comp-Ty (exterior-label-Ty (tree-bd d S)
                                                       (bd-branching-point S P d _)
                                                       (tree-bd d T)
                                                       ⦃ _ ⦄)
                                    (label-≃-Ty (insertion-bd-2 S P T d _) (tree-inc-Ty d (insertion-tree S P T) b)) TySStar))
                   refl≈sty ⟩
        canonical-stm d (tree-bd d S)
          >>= (exterior-label (tree-bd d S)
                              (bd-branching-point S P d _)
                              (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
          ●lt (label-wt-≃ (insertion-bd-2 S P T d _)
                          (tree-inc-label d (insertion-tree S P T) b))
          ≈˘⟨ reflexive≈stm (>>=-assoc (canonical-stm d (tree-bd d S))
                                       (exterior-label (tree-bd d S)
                                                       (bd-branching-point S P d _)
                                                       (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
                                       (_ ,, S⋆)) ⟩
        canonical-stm d (tree-bd d S)
          >>= (exterior-label (tree-bd d S) (bd-branching-point S P d _) (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
          >>= label-wt-≃ (insertion-bd-2 S P T d _) (tree-inc-label d (insertion-tree S P T) b)
          ≈⟨ >>=-≈ (exterior-canonical-stm (tree-bd d S)
                                           (bd-branching-point S P d (bd-bp-lem P x))
                                           (tree-bd d T)
                                           ⦃ _ ⦄
                                           d
                                           (tree-dim-bd″ d S)
                                           (lem3 x))
                   (label-≃-Ty (insertion-bd-2 S P T d _) (tree-inc-Ty d (insertion-tree S P T) b))
                   TySStar ⟩
        canonical-stm d (insertion-tree (tree-bd d S) (bd-branching-point S P d _) (tree-bd d T) ⦃ _ ⦄)
          >>= label-wt-≃ (insertion-bd-2 S P T d _)
                         (tree-inc-label d (insertion-tree S P T) b)
          ≈˘⟨ reflexive≈stm (>>=-assoc (canonical-stm d (insertion-tree (tree-bd d S) (bd-branching-point S P d _) (tree-bd d T) ⦃ _ ⦄))
                            (SPath ∘ ppath-≃ (insertion-bd-2 S P T d _) ,, S⋆)
                            (tree-inc-label d (insertion-tree S P T) b)) ⟩
        canonical-stm d (insertion-tree (tree-bd d S) (bd-branching-point S P d _) (tree-bd d T) ⦃ _ ⦄)
          >>= ((SPath ∘ ppath-≃ (insertion-bd-2 S P T d _)) ,, S⋆)
          >>= tree-inc-label d (insertion-tree S P T) b
          ≈⟨ reflexive≈stm (>>=-≃ (canonical-stm-≃-prop d (insertion-bd-2 S P T d _)) refl≃l refl≃sty) ⟩
        canonical-stm d (tree-bd d (insertion-tree S P T))
          >>= tree-inc-label d (insertion-tree S P T) b ∎

      lem : (b : Bool)
          → canonical-stm d (tree-bd d S) >>= tree-inc-label d S b >>= (exterior-label S P T ,, S⋆)
            ≈[ tree-to-ctx (insertion-tree S P T) ]stm
            canonical-stm d (tree-bd d (insertion-tree S P T)) >>= tree-inc-label d (insertion-tree S P T) b
      lem b = begin
        canonical-stm d (tree-bd d S) >>= tree-inc-label d S b >>= (exterior-label S P T ,, S⋆)
          ≈⟨ reflexive≈stm (>>=-assoc (canonical-stm d (tree-bd d S)) _ _) ⟩
        canonical-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (exterior-label S P T ,, S⋆)
          ≈⟨ lem2 b (Bd-Conditions-one-of d P T) ⟩
        canonical-stm d (tree-bd d (insertion-tree S P T)) >>= tree-inc-label d (insertion-tree S P T) b ∎

  exterior-canonical-comp S P T d p = begin
    SCoh S (canonical-type d S) (exterior-label S P T ,, S⋆)
      ≈⟨ insert (canonical-type d S)
                (exterior-label S P T)
                P
                (interior-label S P T)
                (exterior-branching-path S P T)
                (TySCoh S (canonical-type-Ty d S) (exterior-label-Ty S P T) TySStar) ⟩
    SCoh (insertion-tree S P T)
         (canonical-type d S >>=′ (exterior-label S P T ,, S⋆))
         (label-from-insertion S P T (exterior-label S P T) (interior-label S P T) ,, S⋆)
      ≈⟨ ≈SCoh (insertion-tree S P T)
               (exterior-canonical-type S P T d p)
               (reflexive≈l (exterior-interior-prop S P T)) refl≈sty ⟩
    SCoh (insertion-tree S P T) (canonical-type d (insertion-tree S P T)) (id-label-wt _) ∎
    where
      open Reasoning stm-setoid-≈

  exterior-canonical-comp′ S P T d p = begin
    canonical-comp′ d S >>= (exterior-label S P T ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-≃ (canonical-comp′-compat d S) refl≃l refl≃sty) ⟩
    canonical-comp d S >>= (exterior-label S P T ,, S⋆)
      ≈⟨ exterior-canonical-comp S P T d p ⟩
    canonical-comp d (insertion-tree S P T)
      ≈˘⟨ reflexive≈stm (canonical-comp′-compat d (insertion-tree S P T)) ⟩
    canonical-comp′ d (insertion-tree S P T) ∎
    where
      open Reasoning stm-setoid-≈

  exterior-canonical-stm S@(Join _ _) P T d q p = begin
    canonical-stm d S >>= (exterior-label S P T ,, S⋆)
      ≈⟨ >>=-≈ (canonical-stm-is-comp d ⦃ NonZero-≤ q it ⦄ S) (exterior-label-Ty S P T) TySStar ⟩
    canonical-comp d S >>= (exterior-label S P T ,, S⋆)
      ≈⟨ exterior-canonical-comp S P T d p ⟩
    canonical-comp d (insertion-tree S P T)
      ≈˘⟨ canonical-stm-is-comp d ⦃ NonZero-≤ q it ⦄ (insertion-tree S P T) ⟩
    canonical-stm d (insertion-tree S P T) ∎
    where
      open Reasoning stm-setoid-≈

  exterior-inserted-bp : (S : Tree n)
                       → (P : BranchingPoint S l)
                       → (T : Tree m)
                       → .⦃ _ : has-trunk-height l T ⦄
                       → .⦃ _ : non-linear T ⦄
                       → (Q : BranchingPoint T l′)
                       → (U : Tree m′)
                       → .⦃ _ : has-trunk-height l′ U ⦄
                       → tree-dim U ≤ height-of-branching Q
                       → exterior-label S P T ●l (exterior-label (insertion-tree S P T) (inserted-bp S P T Q) U ,, S⋆)
                       ≈[ tree-to-ctx (insertion-tree (insertion-tree S P T) (inserted-bp S P T Q) U) ]lm
                       ≃-label (sym≃′ (insertion-tree-inserted-bp S P T Q U)) (exterior-label S P (insertion-tree T Q U) ⦃ insertion-trunk-height T Q U l ⦄)
  exterior-inserted-bp (Join S₁ S₂) BPHere T Q U q .get (PExt Z) = begin
    canonical-label (susp S₁) T (PExt Z)
      >>= connect-tree-inc-left T S₂
      >>= (exterior-label (connect-tree T S₂) (connect-bp-left T S₂ Q) U ,, S⋆)
      ≈⟨ reflexive≈stm (>>=-assoc (canonical-label (susp S₁) T (PExt Z)) _ _) ⟩
    canonical-label (susp S₁) T (PExt Z)
      >>= connect-tree-inc-left T S₂ ●lt (exterior-label (connect-tree T S₂) (connect-bp-left T S₂ Q) U ,, S⋆)
      ≈⟨ fixup-reflexive≈stm (>>=-≃ (canonical-label-max (susp S₁) T (PExt Z))
                                    (exterior-bp-left-inc-left T S₂ Q U)
                                    (S⋆-≃ (≃′-to-≃ (insertion-bp-left T S₂ Q U))))
                             (insertion-bp-left T S₂ Q U) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
      (canonical-comp′ (1 + tree-dim S₁) T
        >>= (exterior-label T Q U ,, S⋆) ●lt (connect-tree-inc-left (insertion-tree T Q U) S₂))
      ≈˘⟨ reflexive≈stm (stm-≃-≃ (sym≃′ (insertion-bp-left T S₂ Q U)) (>>=-assoc (canonical-comp′ (1 + tree-dim S₁) T) (exterior-label T Q U ,, S⋆) _)) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
      (canonical-comp′ (1 + tree-dim S₁) T >>= (exterior-label T Q U ,, S⋆)
                                           >>= connect-tree-inc-left (insertion-tree T Q U) S₂)
      ≈⟨ stm-≃-≈ ((sym≃′ (insertion-bp-left T S₂ Q U))) (>>=-≈ (exterior-canonical-comp′ T Q U (1 + tree-dim S₁) q) (connect-tree-inc-left-Ty (insertion-tree T Q U) S₂) TySStar) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
      (canonical-comp′ (1 + tree-dim S₁) (insertion-tree T Q U)
        >>= connect-tree-inc-left (insertion-tree T Q U) S₂)
      ≈˘⟨ stm-≃-≈ (sym≃′ (insertion-bp-left T S₂ Q U)) (reflexive≈stm (>>=-≃ (canonical-label-max (susp S₁) (insertion-tree T Q U) (PExt Z)) refl≃l refl≃sty)) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
         (canonical-label (susp S₁) (insertion-tree T Q U) (PExt Z)
           >>= connect-tree-inc-left (insertion-tree T Q U) S₂) ∎
    where
      open Reasoning stm-setoid-≈
  exterior-inserted-bp (Join S₁ S₂) BPHere T Q U q .get (PShift Z)
    = fixup-reflexive≈stm (exterior-bp-left-inc-right T S₂ Q U .get Z) (insertion-bp-left T S₂ Q U)
  exterior-inserted-bp (Join S₁ S₂) (BPExt P) (susp T) BPHere U q = ⊥-elim (linear-non-linear T)
  exterior-inserted-bp (Join S₁ S₂) (BPExt P) (susp T) (BPExt Q) (Join U Sing) q .get (PExt Z) = begin
    (exterior-label S₁ P T Z >>= map-ext (exterior-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆))
      ≈⟨ reflexive≈stm (>>=-ext (exterior-label S₁ P T Z) (exterior-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆)) ⟩
    SExt (exterior-label S₁ P T Z >>= (exterior-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆))
      ≈⟨ ≈SExt (exterior-inserted-bp S₁ P T Q U (≤-pred q) .get Z) ⟩
    SExt (stm-≃ (sym≃′ (insertion-tree-inserted-bp S₁ P T Q U)) (exterior-label S₁ P (insertion-tree T Q U) ⦃ insertion-trunk-height T Q U (bp-height P) ⦄ Z)) ∎
    where
      open Reasoning stm-setoid-≈
  exterior-inserted-bp (Join S₁ S₂) (BPExt P) (susp T) (BPExt Q) (Join U Sing) q .get (PShift Z) = ≈SShift refl≈stm
  exterior-inserted-bp (Join S₁ S₂) (BPShift P) T Q U q .get (PExt Z) = ≈SExt refl≈stm
  exterior-inserted-bp (Join S₁ S₂) (BPShift P) T Q U q .get (PShift Z) = begin
    (exterior-label S₂ P T Z
      >>= map-shift (exterior-label (insertion-tree S₂ P T) (inserted-bp S₂ P T Q) U ,, S⋆))
      ≈⟨ reflexive≈stm (>>=-shift (exterior-label S₂ P T Z) _) ⟩
    SShift (exterior-label S₂ P T Z >>= (exterior-label (insertion-tree S₂ P T) (inserted-bp S₂ P T Q) U ,, S⋆))
      ≈⟨ ≈SShift (exterior-inserted-bp S₂ P T Q U q .get Z) ⟩
    SShift (stm-≃ (sym≃′ (insertion-tree-inserted-bp S₂ P T Q U)) (exterior-label S₂ P (insertion-tree T Q U) ⦃ insertion-trunk-height T Q U (bp-height P) ⦄ Z)) ∎
    where
      open Reasoning stm-setoid-≈
