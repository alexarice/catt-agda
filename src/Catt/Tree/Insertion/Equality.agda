open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Insertion.Equality (index : ℕ)
                                  (rule : Fin index → Rule)
                                  (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                  (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                  (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Typing index rule
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Suspension
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Connection
open import Catt.Connection.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties

stm-eq : (ΓS : CtxOrTree n) → STm (COT-to-MT ΓS) → STm (COT-to-MT ΓS) → Set
stm-eq ΓS a b = Wrap (λ a b → stm-to-term a ≈[ COT-to-Ctx ΓS ]tm stm-to-term b) a b

syntax stm-eq ΓS a b = a ≈[ ΓS ]stm b

refl≈stm : a ≈[ ΓS ]stm a
refl≈stm = [ refl≈tm ]

sym≈stm : a ≈[ ΓS ]stm b → b ≈[ ΓS ]stm a
sym≈stm [ p ] = [ sym≈tm p ]

trans≈stm : a ≈[ ΓS ]stm b → b ≈[ ΓS ]stm c → a ≈[ ΓS ]stm c
trans≈stm [ p ] [ q ] = [ trans≈tm p q ]

reflexive≈stm : a ≃stm b → a ≈[ ΓS ]stm b
reflexive≈stm [ p ] = [ reflexive≈tm p ]

stm-setoid-≈ : CtxOrTree n → Setoid _ _
stm-setoid-≈ ΓS = record { Carrier = STm (COT-to-MT ΓS)
                         ; _≈_ = λ x y → x ≈[ ΓS ]stm y
                         ; isEquivalence = record { refl = refl≈stm
                                                  ; sym = sym≈stm
                                                  ; trans = trans≈stm
                                                  }
                         }

≈SExt : a ≈[ incTree S ]stm b → SExt a ≈[ incTree (Join S T) ]stm SExt b
≈SExt {T = T} [ p ] = [ (apply-sub-tm-eq (connect-susp-inc-left-Ty (tree-to-ctx T)) (suspTmEq p)) ]

≈SShift : a ≈[ incTree T ]stm b → SShift a ≈[ incTree (Join S T) ]stm SShift b
≈SShift {S = S} [ q ] = [ (apply-sub-tm-eq (connect-susp-inc-right-Ty (tree-to-ctx S)) q) ]

≈SPath : P ≃p Q → SPath P ≃stm SPath Q
≈SPath p = [ path-to-term-≃ p ]

label-max-equality : (ΓS : CtxOrTree n) → (L M : Label (COT-to-MT ΓS) S) → Set
label-max-equality {S = S} ΓS L M = Wrap (λ L M → ∀ (Q : Path S) → .⦃ is-Maximal Q ⦄ → L Q ≈[ ΓS ]stm M Q) L M

syntax label-max-equality ΓS L M = L ≈[ ΓS ]lm M

refl≈lm : L ≈[ ΓS ]lm L
refl≈lm .get Z = refl≈stm

compute-≈ : compute-stm a ≈[ incTree S ]stm compute-stm b → a ≈[ incTree S ]stm b
compute-≈ {a = a} {b = b} p = begin
  a
    ≈˘⟨ reflexive≈stm (compute-to-term a) ⟩
  compute-stm a
    ≈⟨ p ⟩
  compute-stm b
    ≈⟨ reflexive≈stm (compute-to-term b) ⟩
  b ∎
  where
    open Reasoning (stm-setoid-≈ _)

fixup-reflexive≈stm : {a : STm (someTree S)} → {b : STm (someTree T)} → a ≃stm b → (p : S ≃′ T) → a ≈[ incTree S ]stm stm-≃ (sym≃′ p) b
fixup-reflexive≈stm {a = a} {b} q p = reflexive≈stm (begin
  < a >stm
    ≈⟨ q ⟩
  < b >stm
    ≈⟨ stm-≃-≃stm (sym≃′ p) b ⟩
  < stm-≃ (sym≃′ p) b >stm ∎)
  where
    open Reasoning stm-setoid

stm-≃-≈ : (p : S ≃′ T) → a ≈[ incTree S ]stm b → stm-≃ p a ≈[ incTree T ]stm stm-≃ p b
stm-≃-≈ {a = a} {b = b} p q with ≃-to-same-n (≃′-to-≃ p)
... | refl with ≃-to-≡ (≃′-to-≃ p)
... | refl = begin
  stm-≃ p a
    ≈˘⟨ reflexive≈stm (stm-≃-≃stm p a) ⟩
  a
    ≈⟨ q ⟩
  b
    ≈⟨ reflexive≈stm (stm-≃-≃stm p b) ⟩
  stm-≃ p b ∎
  where
    open Reasoning (stm-setoid-≈ _)

pruned-bp-exterior-sub : (S : Tree n)
                       → (p : BranchingPoint S l)
                       → (T : Tree m)
                       → .⦃ _ : has-linear-height l T ⦄
                       → .(q : bp-height p < pred (height-of-branching p))
                       → label-max-equality
                         (incTree (insertion-tree (prune-tree S p) (pruned-bp S p q) T))
                         (label-comp (exterior-sub-label S
                                                         p
                                                         (n-disc (pred (height-of-branching p)))
                                                         ⦃ is-linear-has-linear-height l (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))) ⦄)
                                     (exterior-sub-label (prune-tree S p) (pruned-bp S p q) T ,, S⋆))
                          (≃-label (sym≃′ (insertion-tree-pruned-bp S p T q)) (exterior-sub-label S p T))
pruned-bp-exterior-sub (Join S₁ S₂) (BPExt p) (Join T Sing) q .get (PExt Z) = let
  instance .x : _
  x = is-linear-has-linear-height (bp-height p) (n-disc (height-of-branching′ p)) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ (≤-pred q)) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p))))))

  in begin
  (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄ Z >>=
        (SExt ∘ exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄)
                                      (pruned-bp S₁ p _) T)
        ,, SArr (SPath PHere) S⋆ (SShift (SPath PHere)))
    ≈⟨ reflexive≈stm (extend-≃ (refl≃stm {a = exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄ Z}) refl≃l (≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm))) ⟩
  (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄ Z >>=
        (map-pext (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄)
                                      (pruned-bp S₁ p _) T ,, S⋆)))
    ≈⟨ reflexive≈stm (extend-map-pext (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄ Z) (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄)
                                      (pruned-bp S₁ p _) T ,, S⋆)) ⟩
  SExt (exterior-sub-label S₁ p (n-disc (height-of-branching′ p)) Z
       >>= (exterior-sub-label (insertion-tree S₁ p (n-disc (height-of-branching′ p)) ⦃ x ⦄)
                               (pruned-bp S₁ p _) T) ,, S⋆)
    ≈⟨ ≈SExt (pruned-bp-exterior-sub S₁ p T (≤-pred q) .get Z) ⟩
  SExt (≃-label (sym≃′ (insertion-tree-pruned-bp S₁ p T _)) (exterior-sub-label S₁ p T) Z) ∎
  where
    open Reasoning (stm-setoid-≈ _)
pruned-bp-exterior-sub (Join S₁ S₂) (BPExt p) (Join T Sing) q .get (PShift Z) = refl≈stm
pruned-bp-exterior-sub (Join S₁ S₂) (BPShift p) T q .get (PExt Z) = refl≈stm
pruned-bp-exterior-sub (Join S₁ S₂) (BPShift p) T q .get (PShift Z) = let
  instance .x : _
  x = is-linear-has-linear-height (bp-height p) (n-disc (height-of-branching′ p)) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p))))))
  in begin
  (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) ⦃ x ⦄ Z
    >>= map-pshift (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ x ⦄)
                                      (pruned-bp S₂ p _) T ,, S⋆))
    ≈⟨ reflexive≈stm (extend-map-pshift (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) ⦃ x ⦄ Z) (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ x ⦄)
                                      (pruned-bp S₂ p _) T ,, S⋆)) ⟩
  SShift (exterior-sub-label S₂ p (n-disc (height-of-branching′ p)) Z
    >>= (exterior-sub-label (insertion-tree S₂ p (n-disc (height-of-branching′ p)) ⦃ x ⦄)
                            (pruned-bp S₂ p _) T) ,, S⋆)
    ≈⟨ ≈SShift (pruned-bp-exterior-sub S₂ p T q .get Z) ⟩
  SShift (≃-label (sym≃′ (insertion-tree-pruned-bp S₂ p T _))
                  (exterior-sub-label S₂ p T) Z) ∎
  where
    open Reasoning (stm-setoid-≈ _)
pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q .get (PExt Z) = let
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
  (unbiased-comp′ (suc (suc (tree-dim S₁))) (n-disc (suc (tree-dim S₁)))
    >>= label-from-linear-tree-unbiased (n-disc (suc (tree-dim S₁))) T 0 ,, S⋆
    >>= connect-tree-inc-left T S₂)
    ≈⟨ {!!} ⟩
  (unbiased-comp′ (suc (suc (tree-dim S₁))) T >>=
        (connect-tree-inc-left T S₂))
    ≈˘⟨ reflexive≈stm (extend-≃ (lfltu-maximal-path (Join S₁ Sing) T 1 Z) refl≃l refl≃sty) ⟩
  (label-from-linear-tree-unbiased (Join S₁ Sing) T 1 Z >>=
        (connect-tree-inc-left T S₂)) ∎
  where
    open Reasoning (stm-setoid-≈ _)
pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q .get (PShift Z) = reflexive≈stm (extend-≃ (replace-not-here (SPath ∘ PShift) (SPath (PShift PHere)) Z) refl≃l refl≃sty)

exterior-disc : (S : Tree n)
              → (p : BranchingPoint S l)
              → exterior-sub-label S p (n-disc (height-of-branching p)) ⦃ is-linear-has-linear-height l (n-disc (height-of-branching p)) ⦃ n-disc-is-linear (height-of-branching p) ⦄ (≤-trans (<⇒≤ (bp-height-<-hob p)) (≤-reflexive (sym (tree-dim-n-disc (height-of-branching p))))) ⦄
              ≈[ incTree (insertion-tree S p (n-disc (height-of-branching p)) ⦃ _ ⦄) ]lm ≃-label (sym≃′ (insertion-disc S p)) (id-label S)
exterior-disc (Join S T) BPHere .get (PExt Z) = let
  instance _ = n-disc-is-linear (tree-dim S)
  in begin
  (label-from-linear-tree-unbiased S (n-disc (suc (tree-dim S))) 1 Z >>= (connect-tree-inc-left (Join (n-disc (tree-dim S)) Sing) T))
    ≈⟨ reflexive≈stm (extend-≃ (lfltu-maximal-path S (n-disc (suc (tree-dim S))) 1 Z) refl≃l refl≃sty) ⟩
  (unbiased-comp′ (tree-dim S) (n-disc (tree-dim S)) >>=
        (λ x → SPath (PExt x)) ,,
        SArr (SPath PHere) S⋆ (SPath (PShift PHere)))
    ≈⟨ {!!} ⟩
  (unbiased-stm (tree-dim S) (n-disc (tree-dim S)) >>=
        (λ x → SPath (PExt x)) ,,
        SArr (SPath PHere) S⋆ (SPath (PShift PHere)))
    ≈⟨ reflexive≈stm (extend-≃ (unbiased-stm-linear (tree-dim S) (n-disc (tree-dim S)) (sym (tree-dim-n-disc (tree-dim S)))) refl≃l refl≃sty) ⟩
  SPath (PExt (is-linear-max-path (n-disc (tree-dim S))))
    ≈⟨ reflexive≈stm (≃SPath (≃Ext (trans≃p (max-path-lin-tree (n-disc (tree-dim S)) Z (≃′-to-≃ (linear-tree-unique (n-disc (tree-dim S)) S (tree-dim-n-disc (tree-dim S))))) (ppath-≃-≃p (sym≃′ (linear-tree-unique (n-disc (tree-dim S)) S _)) Z)) refl≃)) ⟩
  SPath (PExt (ppath-≃ (sym≃′ (linear-tree-unique (n-disc (tree-dim S)) S _)) Z)) ∎
  where
    open Reasoning (stm-setoid-≈ _)
exterior-disc (Join S T) BPHere .get (PShift Z) = reflexive≈stm (replace-not-here (SPath ∘ PShift) (SPath (PShift PHere)) Z)
exterior-disc (Join S T) (BPExt p) .get (PExt Z) = compute-≈ (≈SExt (trans≈stm (exterior-disc S p .get Z) (reflexive≈stm (stm-≃-spath (sym≃′ (insertion-disc S p)) Z))))
exterior-disc (Join S T) (BPExt p) .get (PShift Z) = compute-≈ refl≈stm
exterior-disc (Join S T) (BPShift p) .get (PExt Z) = compute-≈ refl≈stm
exterior-disc (Join S T) (BPShift p) .get (PShift Z) = compute-≈ (≈SShift (trans≈stm (exterior-disc T p .get Z) (reflexive≈stm (stm-≃-spath (sym≃′ (insertion-disc T p)) Z))))

exterior-inserted-bp : (S : Tree n)
                     → (P : BranchingPoint S l)
                     → (T : Tree m)
                     → .⦃ _ : has-linear-height l T ⦄
                     → .⦃ _ : non-linear T ⦄
                     → (Q : BranchingPoint T l′)
                     → (U : Tree m′)
                     → .⦃ _ : has-linear-height l′ U ⦄
                     → label-comp (exterior-sub-label S P T) (exterior-sub-label (insertion-tree S P T) (inserted-bp S P T Q) U ,, S⋆)
                     ≈[ incTree (insertion-tree (insertion-tree S P T) (inserted-bp S P T Q) U) ]lm
                     ≃-label (sym≃′ (insertion-tree-inserted-bp S P T Q U)) (exterior-sub-label S P (insertion-tree T Q U) ⦃ insertion-linear-height T Q U l ⦄)
exterior-inserted-bp (Join S₁ S₂) BPHere T Q U .get (PExt Z) = begin
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
    ≈⟨ stm-≃-≈ ((sym≃′ (insertion-bp-left T S₂ Q U))) {!!} ⟩
  stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
    (unbiased-comp′ (1 + tree-dim S₁) (insertion-tree T Q U)
      >>= connect-tree-inc-left (insertion-tree T Q U) S₂)
    ≈˘⟨ stm-≃-≈ (sym≃′ (insertion-bp-left T S₂ Q U)) (reflexive≈stm (extend-≃ (lfltu-maximal-path S₁ (insertion-tree T Q U) 1 Z) refl≃l refl≃sty)) ⟩
  stm-≃ (sym≃′ (insertion-bp-left T S₂ Q U))
       (label-from-linear-tree-unbiased S₁ (insertion-tree T Q U) 1 Z
         >>= connect-tree-inc-left (insertion-tree T Q U) S₂) ∎
  where
    open Reasoning (stm-setoid-≈ _)
exterior-inserted-bp (Join S₁ S₂) BPHere T Q U .get (PShift Z) = begin
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
                   Z) ∎ -- ap (connect-tree-inc-right (insertion-tree T Q U) S₂) Z
   -- ≈˘⟨ replace-not-here (ap (connect-tree-inc-right (insertion-tree T Q U) S₂)) _ Z ⟩
  -- replace-label (ap (connect-tree-inc-right (insertion-tree T Q U) S₂))
  --   (SPath (connect-tree-inc-left′ (insertion-tree T Q U) S₂ (last-path (insertion-tree T Q U)))) Z ∎
  where
    open Reasoning (stm-setoid-≈ _)
exterior-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) BPHere U = ⊥-elim (linear-non-linear T)
exterior-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) .get (PExt Z) = begin
  (exterior-sub-label S₁ P T Z >>= map-pext (exterior-sub-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆))
    ≈⟨ reflexive≈stm (extend-map-pext (exterior-sub-label S₁ P T Z) (exterior-sub-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆)) ⟩
  SExt (exterior-sub-label S₁ P T Z >>= exterior-sub-label (insertion-tree S₁ P T) (inserted-bp S₁ P T Q) U ,, S⋆)
    ≈⟨ ≈SExt (exterior-inserted-bp S₁ P T Q U .get Z) ⟩
  SExt (stm-≃ (sym≃′ (insertion-tree-inserted-bp S₁ P T Q U)) (exterior-sub-label S₁ P (insertion-tree T Q U) ⦃ insertion-linear-height T Q U (bp-height P) ⦄ Z)) ∎
  where
    open Reasoning (stm-setoid-≈ _)
exterior-inserted-bp (Join S₁ S₂) (BPExt P) (Join T Sing) (BPExt Q) (Join U Sing) .get (PShift Z) = ≈SShift refl≈stm
exterior-inserted-bp (Join S₁ S₂) (BPShift P) T Q U .get (PExt Z) = ≈SExt refl≈stm
exterior-inserted-bp (Join S₁ S₂) (BPShift P) T Q U .get (PShift Z) = begin
  (exterior-sub-label S₂ P T Z
    >>= map-pshift (exterior-sub-label (insertion-tree S₂ P T) (inserted-bp S₂ P T Q) U ,, S⋆))
    ≈⟨ reflexive≈stm (extend-map-pshift (exterior-sub-label S₂ P T Z) _) ⟩
  SShift (exterior-sub-label S₂ P T Z >>= exterior-sub-label (insertion-tree S₂ P T) (inserted-bp S₂ P T Q) U ,, S⋆)
    ≈⟨ ≈SShift (exterior-inserted-bp S₂ P T Q U .get Z) ⟩
  SShift (stm-≃ (sym≃′ (insertion-tree-inserted-bp S₂ P T Q U)) (exterior-sub-label S₂ P (insertion-tree T Q U) ⦃ insertion-linear-height T Q U (bp-height P) ⦄ Z)) ∎
  where
    open Reasoning (stm-setoid-≈ _)
