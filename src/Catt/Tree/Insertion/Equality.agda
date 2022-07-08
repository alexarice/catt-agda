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
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Path

label-max-equality : (ΓS : CtxOrTree n) → (L M : Label (COT-to-MT ΓS) S) → Set
label-max-equality {S = S} ΓS L M = Wrap (λ L M → ∀ (Q : Path S) → .⦃ is-Maximal Q ⦄ → stm-to-term (L Q) ≈[ COT-to-Ctx ΓS ]tm stm-to-term (M Q)) L M

pruned-bp-exterior-sub : (S : Tree n)
                       → (p : BranchingPoint S l)
                       → (T : Tree m)
                       → .⦃ _ : has-linear-height l T ⦄
                       → .(q : bp-height p < pred (height-of-branching p))
                       → label-max-equality (incTree (insertion-tree (prune-tree S p) (pruned-bp S p q) T)) (label-comp (exterior-sub-label S p (n-disc (pred (height-of-branching p))) ⦃ is-linear-has-linear-height l (n-disc (pred (height-of-branching p))) ⦃ n-disc-is-linear (pred (height-of-branching p)) ⦄ (≤-trans (<⇒≤ q) (≤-reflexive (sym (tree-dim-n-disc (pred (height-of-branching p)))))) ⦄) (exterior-sub-label (prune-tree S p) (pruned-bp S p q) T ,, ⋆))
                          (label-comp (exterior-sub-label S p T) ?)
pruned-bp-exterior-sub (Join S₁ S₂) (BPExt p) T q = {!!}
pruned-bp-exterior-sub (Join S₁ S₂) (BPShift p) T q = {!!}
pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q .get (PExt Z) = {!!}
pruned-bp-exterior-sub (Join (Join S₁ Sing) S₂) BPHere T q .get (PShift Z) = {!!}
