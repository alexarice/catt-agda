open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Insertion.Equality {index : Set}
                                  (rule : index → Rule)
                                  (lift-rule : ∀ i → P.LiftRule rule i)
                                  (susp-rule : ∀ i → P.SuspRule rule i)
                                  (sub-rule : ∀ i → P.SubRule rule i) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Typing rule
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Suspension
open import Catt.Suspension.Typing rule lift-rule susp-rule
open import Catt.Connection
open import Catt.Connection.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Boundary.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Insertion.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Unbiased.Typing rule lift-rule susp-rule sub-rule
open import Catt.Typing.DiscRemoval rule
open import Catt.Typing.EndoCoherenceRemoval rule
open import Catt.Typing.Insertion rule
open import Relation.Binary

module _ (ecr : HasEndoCoherenceRemoval) (dr : HasDiscRemoval) where
  open import Catt.Typing.DiscRemoval.Properties rule lift-rule susp-rule sub-rule dr

  unbiased-ecr : (d : ℕ)
               → (T : Tree n)
               → (tree-dim T < d)
               → (1 < d)
               → unbiased-comp d T ≈[ tree-to-ctx T ]stm (identity-stm (pred d) >>= label-from-linear-tree-unbiased (n-disc (pred d)) ⦃ n-disc-is-linear (pred d) ⦄ T 0 ,, S⋆)
  unbiased-ecr (suc d) T p q = let
    instance _ = n-disc-is-linear (sty-dim (unbiased-type d T))
    instance _ = n-disc-is-linear d
    in begin
    SCoh T
         (SArr (unbiased-stm d (tree-bd d T) >>=
                               (tree-inc-label d T false))
               (unbiased-type d T)
               (unbiased-stm d (tree-bd d T) >>=
                               (tree-inc-label d T true)))
         (id-label-wt T)
      ≈⟨ reflexive≈stm (≃SCoh T (≃SArr (unbiased-stm-full-lem d T false (≤-pred p))
                                       refl≃sty
                                       (unbiased-stm-full-lem d T true (≤-pred p)))
                                refl≃l
                                refl≃sty) ⟩
    SCoh T (SArr (unbiased-stm d T)
                 (unbiased-type d T)
                 (unbiased-stm d T))
           (id-label-wt T)
      ≈⟨ ecr T (unbiased-stm d T) (unbiased-type d T) (id-label T) (unbiased-stm-Ty d T (≤-pred p)) (unbiased-type-Ty d T) (id-label-Ty T) ⟩
    (identity-stm (sty-dim (unbiased-type d T)) >>=
      label-wt-comp (label-from-linear-tree (n-disc (sty-dim (unbiased-type d T)))
                                            (unbiased-stm d T)
                                            (unbiased-type d T) _ ,, S⋆)
                    (id-label T ,, S⋆))
      ≈⟨ reflexive≈stm (extend-≃ (refl≃stm {a = identity-stm (sty-dim (unbiased-type d T))}) (comp-right-unit ((label-from-linear-tree (n-disc (sty-dim (unbiased-type d T)))
                                            (unbiased-stm d T)
                                            (unbiased-type d T) _))) refl≃sty) ⟩
    (identity-stm (sty-dim (unbiased-type d T)) >>=
                  label-from-linear-tree (n-disc (sty-dim (unbiased-type d T)))
                                         (unbiased-stm d T)
                                         (unbiased-type d T) _ ,, S⋆)
      ≈⟨ ≈-extend (identity-stm (sty-dim (unbiased-type d T))) (label-from-linear-tree-≈ (n-disc (sty-dim (unbiased-type d T))) (unbiased-stm-is-comp′ d ⦃ NonZero-≤ (≤-pred q) it ⦄ T) refl≈sty _) refl≈sty ⟩
    (identity-stm (sty-dim (unbiased-type d T)) >>=
                  label-from-linear-tree (n-disc (sty-dim (unbiased-type d T)))
                                         (unbiased-comp′ d T)
                                         (unbiased-type d T) _ ,, S⋆)
      ≈⟨ reflexive≈stm (extend-≃ (refl≃stm {a = identity-stm (sty-dim (unbiased-type d T))}) (label-from-linear-tree-unbiased-lem-0 (n-disc (sty-dim (unbiased-type d T))) T d (trans (tree-dim-n-disc (sty-dim (unbiased-type d T))) (unbiased-type-dim d T))) refl≃sty) ⟩
    (identity-stm (sty-dim (unbiased-type d T)) >>=
                  label-from-linear-tree-unbiased (n-disc (sty-dim (unbiased-type d T))) T 0 ,, S⋆)
      ≈⟨ reflexive≈stm (reflexive≃stm (cong (λ x → (identity-stm x >>=
                  label-from-linear-tree-unbiased (n-disc x) ⦃ n-disc-is-linear x ⦄ T 0 ,, S⋆)) (unbiased-type-dim d T))) ⟩
    (identity-stm d >>= label-from-linear-tree-unbiased (n-disc d) T 0 ,, S⋆) ∎
    where
      open Reasoning stm-setoid-≈

  pruned-bp-exterior-sub : (S : Tree n)
                         → (p : BranchingPoint S l)
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height l T ⦄
                         → .(q : bp-height p < pred (height-of-branching p))
                         → (x : tree-dim T < height-of-branching p)
                         → label-max-equality
                           (tree-to-ctx (insertion-tree (prune-tree S p) (pruned-bp S p q) T))
                           (label-comp (exterior-sub-label S
                                                           p
                                                           (n-disc (pred (height-of-branching p)))
                                                           ⦃ is-linear-has-linear-height l (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))) ⦄)
                                       (exterior-sub-label (prune-tree S p) (pruned-bp S p q) T ,, S⋆))
                            (≃-label (sym≃′ (insertion-tree-pruned-bp S p T q)) (exterior-sub-label S p T))
  pruned-bp-exterior-sub (Join S₁ S₂) (BPExt p) (Join T Sing) q x .get (PExt Z) = let
    instance .y : _
    y = is-linear-has-linear-height (bp-height p) (n-disc (height-of-branching′ p)) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ (≤-pred q)) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p))))))

    in begin
    (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z >>=
          (SExt ∘ exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
                                        (pruned-bp S₁ p _) T)
          ,, SArr (SPath PHere) S⋆ (SShift (SPath PHere)))
      ≈⟨ reflexive≈stm (extend-≃ (refl≃stm {a = exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z}) refl≃l (≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm))) ⟩
    (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z >>=
          (map-pext (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
                                        (pruned-bp S₁ p _) T ,, S⋆)))
      ≈⟨ reflexive≈stm (extend-map-pext (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z) (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
                                        (pruned-bp S₁ p _) T ,, S⋆)) ⟩
    SExt (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) Z
         >>= (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
                                 (pruned-bp S₁ p _) T) ,, S⋆)
      ≈⟨ ≈SExt (pruned-bp-exterior-sub S₁ p T (≤-pred q) (≤-pred x) .get Z) ⟩
    SExt (≃-label (sym≃′ (insertion-tree-pruned-bp S₁ p T _)) (exterior-sub-label S₁ p T) Z) ∎
    where
      open Reasoning stm-setoid-≈
  pruned-bp-exterior-sub (Join S₁ S₂) (BPExt p) (Join T Sing) q x .get (PShift Z) = refl≈stm
  pruned-bp-exterior-sub (Join S₁ S₂) (BPShift p) T q x .get (PExt Z) = refl≈stm
  pruned-bp-exterior-sub (Join S₁ S₂) (BPShift p) T q x .get (PShift Z) = let
    instance .y : _
    y = is-linear-has-linear-height (bp-height p) (n-disc (height-of-branching′ p)) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p))))))
    in begin
    (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z
      >>= map-pshift (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
                                        (pruned-bp S₂ p _) T ,, S⋆))
      ≈⟨ reflexive≈stm (extend-map-pshift (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄ Z) (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
                                        (pruned-bp S₂ p _) T ,, S⋆)) ⟩
    SShift (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) Z
      >>= (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ y ⦄)
                              (pruned-bp S₂ p _) T) ,, S⋆)
      ≈⟨ ≈SShift (pruned-bp-exterior-sub S₂ p T q x .get Z) ⟩
    SShift (≃-label (sym≃′ (insertion-tree-pruned-bp S₂ p T _))
                    (exterior-sub-label S₂ p T) Z) ∎
    where
      open Reasoning stm-setoid-≈
  pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q x .get (PExt Z) = let
    instance _ = n-disc-is-linear (tree-dim S₁)
    in begin
    (label-from-linear-tree-unbiased (suspTree S₁) (Join (n-disc (tree-dim S₁)) Sing) 1 Z
      >>= connect-tree-inc-left (Join (n-disc (tree-dim S₁)) Sing) S₂
      >>= (connect-label (label-comp (label-from-linear-tree-unbiased (Join (n-disc (tree-dim S₁)) Sing) T 0)
                                     (connect-tree-inc-left T S₂))
                        (ap (connect-tree-inc-right T S₂)) ,, S⋆))
      ≈⟨ reflexive≈stm (extend-≃ (extend-≃ (lfltu-maximal-path (suspTree S₁) (Join (n-disc (tree-dim S₁)) Sing) 1 Z) refl≃l refl≃sty) refl≃l refl≃sty) ⟩
    (unbiased-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁))
      >>= (SPath ∘ PExt) ,, SArr (SPath PHere) S⋆ (SPath (PShift PHere))
      >>= (connect-label (label-comp (label-from-linear-tree-unbiased (Join (n-disc (tree-dim S₁)) Sing) T 0)
                                     (connect-tree-inc-left T S₂))
                        (ap (connect-tree-inc-right T S₂)) ,, S⋆))
      ≈⟨ reflexive≈stm (extend-assoc (unbiased-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁))) _ _) ⟩
    (unbiased-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁)) >>=
          (label-wt-comp (label-from-linear-tree-unbiased (n-disc (tree-dim S₁)) T 1 ,, SArr SHere S⋆ (SPath (last-path T)))
                         (connect-tree-inc-left T S₂)))
      ≈˘⟨ reflexive≈stm (extend-assoc (unbiased-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁))) _ _) ⟩
    (unbiased-comp′ (suc (tree-dim S₁)) (n-disc (tree-dim S₁))
      >>= label-from-linear-tree-unbiased (n-disc (tree-dim S₁)) T 1 ,, SArr SHere S⋆ (SPath (last-path T))
      >>= connect-tree-inc-left T S₂)
      ≡⟨⟩
    (identity-stm (suc (tree-dim S₁))
      >>= label-from-linear-tree-unbiased (n-disc (suc (tree-dim S₁))) T 0 ,, S⋆
      >>= connect-tree-inc-left T S₂)
      ≈˘⟨ extend-≈ (unbiased-ecr (suc (suc (tree-dim S₁))) T x (s≤s (s≤s z≤n))) (connect-tree-inc-left-Ty T S₂) TySStar ⟩
    (unbiased-comp (2 + tree-dim S₁) T >>= (connect-tree-inc-left T S₂))
      ≈˘⟨ reflexive≈stm (extend-≃ (unbiased-comp′-compat (2 + tree-dim S₁) T) refl≃l refl≃sty) ⟩
    (unbiased-comp′ (suc (suc (tree-dim S₁))) T >>=
          (connect-tree-inc-left T S₂))
      ≈˘⟨ reflexive≈stm (extend-≃ (lfltu-maximal-path (Join S₁ Sing) T 1 Z) refl≃l refl≃sty) ⟩
    (label-from-linear-tree-unbiased (Join S₁ Sing) T 1 Z >>=
          (connect-tree-inc-left T S₂)) ∎
    where
      open Reasoning stm-setoid-≈
  pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q x .get (PShift Z) = reflexive≈stm (extend-≃ (replace-not-here (SPath ∘ PShift) (SPath (PShift PHere)) Z) refl≃l refl≃sty)

module _ (disc-rem : HasDiscRemoval) where
  open import Catt.Typing.DiscRemoval.Properties rule lift-rule susp-rule sub-rule disc-rem

  exterior-disc : (S : Tree n)
                → (p : BranchingPoint S l)
                → exterior-sub-label S p (n-disc (height-of-branching p)) ⦃ is-linear-has-linear-height l (n-disc (height-of-branching p)) ⦃ n-disc-is-linear (height-of-branching p) ⦄ (≤-trans (<⇒≤ (bp-height-<-hob p)) (≤-reflexive (sym (tree-dim-n-disc (height-of-branching p))))) ⦄
                ≈[ tree-to-ctx (insertion-tree S p (n-disc (height-of-branching p)) ⦃ _ ⦄) ]lm ≃-label (sym≃′ (insertion-disc S p)) (id-label S)
  exterior-disc (Join S T) BPHere .get (PExt Z) = let
    instance _ = n-disc-is-linear (tree-dim S)
    in begin
    (label-from-linear-tree-unbiased (suspTree S) (n-disc (suc (tree-dim S))) 0 (PExt Z) >>= (connect-tree-inc-left (Join (n-disc (tree-dim S)) Sing) T))
      ≈⟨ reflexive≈stm (extend-≃ (lfltu-maximal-path (suspTree S) (n-disc (suc (tree-dim S))) 0 (PExt Z)) refl≃l refl≃sty) ⟩
    (unbiased-comp′ (tree-dim (suspTree S)) (n-disc (suc (tree-dim S)))
      >>= connect-tree-inc-left (Join (n-disc (tree-dim S)) Sing) T)
      ≈˘⟨ extend-≈ (unbiased-stm-is-comp′ (suc (tree-dim S)) (n-disc (suc (tree-dim S)))) (connect-tree-inc-left-Ty (n-disc (suc (tree-dim S))) T) TySStar ⟩
    (unbiased-stm (suc (tree-dim S)) (n-disc (suc (tree-dim S))) >>=
      connect-tree-inc-left (n-disc (suc (tree-dim S))) T)
      ≡⟨⟩
    (unbiased-stm (tree-dim S) (n-disc (tree-dim S)) >>=
          (λ x → SPath (PExt x)) ,,
          SArr (SPath PHere) S⋆ (SPath (PShift PHere)))
      ≈⟨ reflexive≈stm (extend-≃ (unbiased-stm-linear (tree-dim S) (n-disc (tree-dim S)) (sym (tree-dim-n-disc (tree-dim S)))) refl≃l refl≃sty) ⟩
    SPath (PExt (is-linear-max-path (n-disc (tree-dim S))))
      ≈⟨ reflexive≈stm (≃SPath (≃Ext (trans≃p (max-path-lin-tree (n-disc (tree-dim S)) Z (≃′-to-≃ (linear-tree-unique (n-disc (tree-dim S)) S (tree-dim-n-disc (tree-dim S))))) (ppath-≃-≃p (sym≃′ (linear-tree-unique (n-disc (tree-dim S)) S _)) Z)) refl≃)) ⟩
    SPath (PExt (ppath-≃ (sym≃′ (linear-tree-unique (n-disc (tree-dim S)) S _)) Z)) ∎
    where
      open Reasoning stm-setoid-≈
  exterior-disc (Join S T) BPHere .get (PShift Z) = reflexive≈stm (replace-not-here (SPath ∘ PShift) (SPath (PShift PHere)) Z)
  exterior-disc (Join S T) (BPExt p) .get (PExt Z) = compute-≈ (≈SExt (trans≈stm (exterior-disc S p .get Z) (reflexive≈stm (stm-≃-spath (sym≃′ (insertion-disc S p)) Z))))
  exterior-disc (Join S T) (BPExt p) .get (PShift Z) = compute-≈ refl≈stm
  exterior-disc (Join S T) (BPShift p) .get (PExt Z) = compute-≈ refl≈stm
  exterior-disc (Join S T) (BPShift p) .get (PShift Z) = compute-≈ (≈SShift (trans≈stm (exterior-disc T p .get Z) (reflexive≈stm (stm-≃-spath (sym≃′ (insertion-disc T p)) Z))))

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

module _ (dr : HasDiscRemoval) (insert : HasInsertion) where
  open import Catt.Typing.DiscRemoval.Properties rule lift-rule susp-rule sub-rule dr

  exterior-unbiased-type : (S : Tree n)
                    → (P : BranchingPoint S l)
                    → (T : Tree m)
                    → .⦃ _ : has-linear-height l T ⦄
                    → (d : ℕ)
                    → (d ≤ 1 + tree-dim S)
                    → (tree-dim T ≤ height-of-branching P)
                    → (label-on-sty (unbiased-type d S) (exterior-sub-label S P T ,, S⋆))
                    ≈[ tree-to-ctx (insertion-tree S P T) ]sty unbiased-type d (insertion-tree S P T)
  exterior-unbiased-comp : (S : Tree n)
                    → (P : BranchingPoint S l)
                    → (T : Tree m)
                    → .⦃ _ : has-linear-height l T ⦄
                    → (d : ℕ)
                    → d ≡ tree-dim S
                    → (tree-dim T ≤ height-of-branching P)
                    → (unbiased-comp d S >>= exterior-sub-label S P T ,, S⋆)
                    ≈[ tree-to-ctx (insertion-tree S P T) ]stm unbiased-comp d (insertion-tree S P T)
  exterior-unbiased-comp′ : (S : Tree n)
                    → (P : BranchingPoint S l)
                    → (T : Tree m)
                    → .⦃ _ : has-linear-height l T ⦄
                    → (d : ℕ)
                    → d ≡ tree-dim S
                    → (tree-dim T ≤ height-of-branching P)
                    → (unbiased-comp′ d S >>= exterior-sub-label S P T ,, S⋆)
                    ≈[ tree-to-ctx (insertion-tree S P T) ]stm unbiased-comp′ d (insertion-tree S P T)
  exterior-unbiased-stm : (S : Tree n)
                    → (P : BranchingPoint S l)
                    → (T : Tree m)
                    → .⦃ _ : has-linear-height l T ⦄
                    → (d : ℕ)
                    → d ≡ tree-dim S
                    → (tree-dim T ≤ height-of-branching P)
                    → (unbiased-stm d S >>= exterior-sub-label S P T ,, S⋆)
                    ≈[ tree-to-ctx (insertion-tree S P T) ]stm unbiased-stm d (insertion-tree S P T)

  exterior-unbiased-type S P T zero p q = refl≈sty
  exterior-unbiased-type S P T (suc d) p q = ≈SArr (lem false) (exterior-unbiased-type S P T d (≤-trans (n≤1+n d) p) q) (lem true)
    where
      open Reasoning stm-setoid-≈

      lem3 : (x : Condition d T (height-of-branching P)) → tree-dim (tree-bd d T) ≤
               height-of-branching (bd-branching-point S P d (bd-bp-lem P x))
      lem3 x = (≤-trans (≤-reflexive (tree-dim-bd d T))
                      (≤-trans (⊓-monoʳ-≤ d q)
                               (≤-reflexive (sym (bd-branching-point-height S P d (bd-bp-lem P x))))))

      lem2 : (b : Bool) → Bd-Conditions d P T
           → (unbiased-stm d (tree-bd d S) >>= label-wt-comp (tree-inc-label d S b) (exterior-sub-label S P T ,, S⋆))
           ≈[ tree-to-ctx (insertion-tree S P T) ]stm
           (unbiased-stm d (tree-bd d (insertion-tree S P T)) >>= tree-inc-label d (insertion-tree S P T) b)
      lem2 b (Bd-Cond1 x y) = begin
        (unbiased-stm d (tree-bd d S) >>= label-wt-comp (tree-inc-label d S b) (exterior-sub-label S P T ,, S⋆))
          ≈⟨ ≈-extend (unbiased-stm d (tree-bd d S))
                      (label-max-equality-to-equality (unbiased-exterior-comm-1 S P T d x y q b)
                                                      (label-comp-Ty (tree-inc-Ty d S b) (exterior-sub-label-Ty S P T q) TySStar)
                                                      (label-≃-Ty (insertion-bd-1 S P T d y q) (tree-inc-Ty d (insertion-tree S P T) b)))
                      refl≈sty ⟩
        (unbiased-stm d (tree-bd d S) >>=
          label-wt-≃ (insertion-bd-1 S P T d y q) (tree-inc-label d (insertion-tree S P T) b))
          ≈˘⟨ reflexive≈stm (extend-assoc (unbiased-stm d (tree-bd d S)) _ _) ⟩
        (unbiased-stm d (tree-bd d S) >>= SPath ∘ ppath-≃ (insertion-bd-1 S P T d y q) ,, S⋆ >>= tree-inc-label d (insertion-tree S P T) b)
          ≈⟨ reflexive≈stm (extend-≃ (unbiased-stm-≃-prop d (insertion-bd-1 S P T d y q)) refl≃l refl≃sty) ⟩
        (unbiased-stm d (tree-bd d (insertion-tree S P T)) >>=
          tree-inc-label d (insertion-tree S P T) b) ∎
      lem2 b (Bd-Cond2 x) = begin
        (unbiased-stm d (tree-bd d S) >>= label-wt-comp (tree-inc-label d S b) (exterior-sub-label S P T ,, S⋆))
          ≈⟨ ≈-extend (unbiased-stm d (tree-bd d S))
                      (label-max-equality-to-equality
                        (unbiased-exterior-comm-2 S P T d b q x)
                        (label-comp-Ty (tree-inc-Ty d S b) (exterior-sub-label-Ty S P T q) TySStar)
                        (label-comp-Ty (exterior-sub-label-Ty (tree-bd d S)
                                                              (bd-branching-point S P d _)
                                                              (tree-bd d T)
                                                              ⦃ _ ⦄
                                                              (lem3 x))
                                       (label-≃-Ty (insertion-bd-2 S P T d _) (tree-inc-Ty d (insertion-tree S P T) b)) TySStar))
                      refl≈sty ⟩
        (unbiased-stm d (tree-bd d S) >>=
          (label-wt-comp (exterior-sub-label (tree-bd d S)
                                             (bd-branching-point S P d _)
                                             (tree-bd d T) ⦃ _ ⦄ ,, S⋆)
                         (label-wt-≃ (insertion-bd-2 S P T d _)
                                     (tree-inc-label d (insertion-tree S P T) b))))
          ≈˘⟨ reflexive≈stm (extend-assoc (unbiased-stm d (tree-bd d S)) (exterior-sub-label (tree-bd d S)
                                             (bd-branching-point S P d _)
                                             (tree-bd d T) ⦃ _ ⦄ ,, S⋆) (_ ,, S⋆)) ⟩
        (unbiased-stm d (tree-bd d S)
          >>= exterior-sub-label (tree-bd d S) (bd-branching-point S P d _) (tree-bd d T) ⦃ _ ⦄ ,, S⋆
          >>= label-wt-≃ (insertion-bd-2 S P T d _) (tree-inc-label d (insertion-tree S P T) b))
          ≈⟨ extend-≈ (exterior-unbiased-stm (tree-bd d S) (bd-branching-point S P d (bd-bp-lem P x)) (tree-bd d T) ⦃ _ ⦄ d (sym (tree-dim-bd′ d S (≤-pred p))) (lem3 x)) (label-≃-Ty (insertion-bd-2 S P T d _) (tree-inc-Ty d (insertion-tree S P T) b)) TySStar ⟩
        (unbiased-stm d (insertion-tree (tree-bd d S) (bd-branching-point S P d _) (tree-bd d T) ⦃ _ ⦄) >>= label-wt-≃ (insertion-bd-2 S P T d _) (tree-inc-label d (insertion-tree S P T) b))
          ≈˘⟨ reflexive≈stm (extend-assoc (unbiased-stm d (insertion-tree (tree-bd d S) (bd-branching-point S P d _) (tree-bd d T) ⦃ _ ⦄)) (SPath ∘ ppath-≃ (insertion-bd-2 S P T d _) ,, S⋆) (tree-inc-label d (insertion-tree S P T) b)) ⟩
        (unbiased-stm d
          (insertion-tree (tree-bd d S) (bd-branching-point S P d _)
           (tree-bd d T) ⦃ _ ⦄)
          >>= (SPath ∘ ppath-≃ (insertion-bd-2 S P T d _)) ,, S⋆
          >>= tree-inc-label d (insertion-tree S P T) b)
          ≈⟨ reflexive≈stm (extend-≃ (unbiased-stm-≃-prop d (insertion-bd-2 S P T d _)) refl≃l refl≃sty) ⟩
        (unbiased-stm d (tree-bd d (insertion-tree S P T)) >>=
          tree-inc-label d (insertion-tree S P T) b) ∎

      lem : (b : Bool) → (unbiased-stm d (tree-bd d S) >>= tree-inc-label d S b >>= exterior-sub-label S P T ,, S⋆)
          ≈[ tree-to-ctx (insertion-tree S P T) ]stm
          (unbiased-stm d (tree-bd d (insertion-tree S P T)) >>= tree-inc-label d (insertion-tree S P T) b)
      lem b = begin
        (unbiased-stm d (tree-bd d S) >>= tree-inc-label d S b >>= exterior-sub-label S P T ,, S⋆)
          ≈⟨ reflexive≈stm (extend-assoc (unbiased-stm d (tree-bd d S)) _ _) ⟩
        (unbiased-stm d (tree-bd d S) >>= label-wt-comp (tree-inc-label d S b) (exterior-sub-label S P T ,, S⋆))
          ≈⟨ lem2 b (Bd-Conditions-one-of d P T) ⟩
        (unbiased-stm d (tree-bd d (insertion-tree S P T)) >>= tree-inc-label d (insertion-tree S P T) b) ∎

  exterior-unbiased-comp S P T d q p = begin
    SCoh S (unbiased-type d S) (exterior-sub-label S P T ,, S⋆)
      ≈⟨ insert S (unbiased-type d S) (exterior-sub-label S P T) P T (interior-sub-label S P T) (exterior-branching-path S P T) (unbiased-type-Ty d S) (exterior-sub-label-Ty S P T p) ⟩
    SCoh (insertion-tree S P T) (label-on-sty (unbiased-type d S) (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T (exterior-sub-label S P T) (interior-sub-label S P T) ,, S⋆)
      ≈⟨ ≈SCoh (insertion-tree S P T) (exterior-unbiased-type S P T d (≤-trans (≤-reflexive q) (n≤1+n (tree-dim S))) p) (reflexive≈l (exterior-interior-prop S P T)) refl≈sty ⟩
    SCoh (insertion-tree S P T) (unbiased-type d (insertion-tree S P T)) (id-label-wt _) ∎
    where
      open Reasoning stm-setoid-≈

  exterior-unbiased-comp′ S P T d q p = begin
    (unbiased-comp′ d S >>= exterior-sub-label S P T ,, S⋆)
      ≈⟨ reflexive≈stm (extend-≃ (unbiased-comp′-compat d S) refl≃l refl≃sty) ⟩
    (unbiased-comp d S >>= exterior-sub-label S P T ,, S⋆)
      ≈⟨ exterior-unbiased-comp S P T d q p ⟩
    unbiased-comp d (insertion-tree S P T)
      ≈˘⟨ reflexive≈stm (unbiased-comp′-compat d (insertion-tree S P T)) ⟩
    unbiased-comp′ d (insertion-tree S P T) ∎
    where
      open Reasoning stm-setoid-≈

  exterior-unbiased-stm S@(Join _ _) P T d q p = begin
    (unbiased-stm d S >>= exterior-sub-label S P T ,, S⋆)
      ≈⟨ extend-≈ (unbiased-stm-is-comp d ⦃ NonZero-subst (sym q) it ⦄ S) (exterior-sub-label-Ty S P T p) TySStar ⟩
    (unbiased-comp d S >>= exterior-sub-label S P T ,, S⋆)
      ≈⟨ exterior-unbiased-comp S P T d q p ⟩
    unbiased-comp d (insertion-tree S P T)
      ≈˘⟨ unbiased-stm-is-comp d ⦃ NonZero-subst (sym q) it ⦄ (insertion-tree S P T) ⟩
    unbiased-stm d (insertion-tree S P T) ∎
    where
      open Reasoning stm-setoid-≈


  exterior-inserted-bp : (S : Tree n)
                       → (P : BranchingPoint S l)
                       → (T : Tree m)
                       → .⦃ _ : has-linear-height l T ⦄
                       → height-of-branching P ≡ tree-dim T
                       → .⦃ _ : non-linear T ⦄
                       → (Q : BranchingPoint T l′)
                       → (U : Tree m′)
                       → .⦃ _ : has-linear-height l′ U ⦄
                       → tree-dim U ≤ height-of-branching Q
                       → label-comp (exterior-sub-label S P T) (exterior-sub-label (insertion-tree S P T) (inserted-bp S P T Q) U ,, S⋆)
                       ≈[ tree-to-ctx (insertion-tree (insertion-tree S P T) (inserted-bp S P T Q) U) ]lm
                       ≃-label (sym≃′ (insertion-tree-inserted-bp S P T Q U)) (exterior-sub-label S P (insertion-tree T Q U) ⦃ insertion-linear-height T Q U l ⦄)
  exterior-inserted-bp (Join S₁ S₂) BPHere T p Q U q .get (PExt Z) = begin
    (label-from-linear-tree-unbiased S₁ T 1 Z
      >>= connect-tree-inc-left T S₂
      >>= exterior-sub-label (connect-tree T S₂) (connect-bp-left T S₂ Q) U ,, S⋆)
      ≈⟨ reflexive≈stm (extend-assoc (label-from-linear-tree-unbiased S₁ T 1 Z) _ _) ⟩
    (label-from-linear-tree-unbiased S₁ T 1 Z
      >>= label-wt-comp (connect-tree-inc-left T S₂)
                        (exterior-sub-label (connect-tree T S₂) (connect-bp-left T S₂ Q) U ,, S⋆))
      ≈⟨ fixup-reflexive≈stm (extend-≃ (lfltu-maximal-path S₁ T 1 Z) (exterior-bp-left-inc-left T S₂ Q U) (≃S⋆ (≃′-to-≃ (insertion-bp-left T S₂ Q U)))) (insertion-bp-left T S₂ Q U) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
      (unbiased-comp′ (1 + tree-dim S₁) T >>= label-wt-comp (exterior-sub-label T Q U ,, S⋆)
                                                            (connect-tree-inc-left (insertion-tree T Q U) S₂))
      ≈˘⟨ reflexive≈stm (stm-≃-≃ (sym≃′ (insertion-bp-left T S₂ Q U)) (extend-assoc (unbiased-comp′ (1 + tree-dim S₁) T) (exterior-sub-label T Q U ,, S⋆) _)) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
      (unbiased-comp′ (1 + tree-dim S₁) T >>=
       exterior-sub-label T Q U ,, S⋆
       >>= connect-tree-inc-left (insertion-tree T Q U) S₂)
      ≈⟨ stm-≃-≈ ((sym≃′ (insertion-bp-left T S₂ Q U))) (extend-≈ (exterior-unbiased-comp′ T Q U (1 + tree-dim S₁) p q) (connect-tree-inc-left-Ty (insertion-tree T Q U) S₂) TySStar) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
      (unbiased-comp′ (1 + tree-dim S₁) (insertion-tree T Q U)
        >>= connect-tree-inc-left (insertion-tree T Q U) S₂)
      ≈˘⟨ stm-≃-≈ (sym≃′ (insertion-bp-left T S₂ Q U)) (reflexive≈stm (extend-≃ (lfltu-maximal-path S₁ (insertion-tree T Q U) 1 Z) refl≃l refl≃sty)) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
         (label-from-linear-tree-unbiased S₁ (insertion-tree T Q U) 1 Z
           >>= connect-tree-inc-left (insertion-tree T Q U) S₂) ∎
    where
      open Reasoning stm-setoid-≈
  exterior-inserted-bp (Join S₁ S₂) BPHere T p Q U q .get (PShift Z) = begin
    (replace-label (ap (connect-tree-inc-right T S₂)) (SPath (connect-tree-inc-left′ T S₂ (last-path T))) Z
        >>= exterior-sub-label (connect-tree T S₂) (connect-bp-left T S₂ Q) U ,, S⋆)
      ≈⟨ reflexive≈stm (extend-≃ (replace-not-here (ap (connect-tree-inc-right T S₂)) (SPath (connect-tree-inc-left′ T S₂ (last-path T))) Z) refl≃l refl≃sty) ⟩
    exterior-sub-label (connect-tree T S₂) (connect-bp-left T S₂ Q) U (connect-tree-inc-right′ T S₂ Z)
      ≈⟨ fixup-reflexive≈stm (exterior-bp-left-inc-right T S₂ Q U .get Z) (insertion-bp-left T S₂ Q U) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U)) (ap (connect-tree-inc-right (insertion-tree T Q U) S₂) Z)
      ≈˘⟨ reflexive≈stm (stm-≃-≃ (sym≃′ (insertion-bp-left T S₂ Q U)) (replace-not-here _ _ Z)) ⟩
    stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
      (replace-label (ap (connect-tree-inc-right (insertion-tree T Q U) S₂))
                     (SPath (connect-tree-inc-left′ (insertion-tree T Q U) S₂ (last-path (insertion-tree T Q U))))
                     Z) ∎
    where
      open Reasoning stm-setoid-≈
  exterior-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) p BPHere U q = ⊥-elim (linear-non-linear T)
  exterior-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) p (BPExt Q) (Join U Sing) q .get (PExt Z) = begin
    (exterior-sub-label S₁ P T Z >>= map-pext (exterior-sub-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆))
      ≈⟨ reflexive≈stm (extend-map-pext (exterior-sub-label S₁ P T Z) (exterior-sub-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆)) ⟩
    SExt (exterior-sub-label S₁ P T Z >>= exterior-sub-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆)
      ≈⟨ ≈SExt (exterior-inserted-bp S₁ P T (cong pred p) Q U (≤-pred q) .get Z) ⟩
    SExt (stm-≃ (sym≃′ (insertion-tree-inserted-bp S₁ P T Q U)) (exterior-sub-label S₁ P (insertion-tree T Q U) ⦃ insertion-linear-height T Q U (bp-height P) ⦄ Z)) ∎
    where
      open Reasoning stm-setoid-≈
  exterior-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) p (BPExt Q) (Join U Sing) q .get (PShift Z) = ≈SShift refl≈stm
  exterior-inserted-bp (Join S₁ S₂) (BPShift P) T p Q U q .get (PExt Z) = ≈SExt refl≈stm
  exterior-inserted-bp (Join S₁ S₂) (BPShift P) T p Q U q .get (PShift Z) = begin
    (exterior-sub-label S₂ P T Z
      >>= map-pshift (exterior-sub-label (insertion-tree S₂ P T) (inserted-bp S₂ P T Q) U ,, S⋆))
      ≈⟨ reflexive≈stm (extend-map-pshift (exterior-sub-label S₂ P T Z) _) ⟩
    SShift (exterior-sub-label S₂ P T Z >>= exterior-sub-label (insertion-tree S₂ P T) (inserted-bp S₂ P T Q) U ,, S⋆)
      ≈⟨ ≈SShift (exterior-inserted-bp S₂ P T p Q U q .get Z) ⟩
    SShift (stm-≃ (sym≃′ (insertion-tree-inserted-bp S₂ P T Q U)) (exterior-sub-label S₂ P (insertion-tree T Q U) ⦃ insertion-linear-height T Q U (bp-height P) ⦄ Z)) ∎
    where
      open Reasoning stm-setoid-≈
