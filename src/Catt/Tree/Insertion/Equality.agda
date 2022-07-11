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
    ≈⟨ ≈SShift (pruned-bp-exterior-sub S₂ p T q .get Z ⦃ proj₂ it ⦄) ⟩
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
pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q .get (PShift Z) = reflexive≈stm (extend-≃ (replace-not-here (SPath ∘ PShift) (SPath (PShift PHere)) Z ⦃ proj₁ it ⦄) refl≃l refl≃sty)
