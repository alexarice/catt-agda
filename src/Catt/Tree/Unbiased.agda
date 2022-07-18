module Catt.Tree.Unbiased where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Boundary
open import Catt.Tree.Properties
open import Catt.Tree.Label
open import Catt.Globular
open import Relation.Nullary

unbiased-type : (d : ℕ) → (T : Tree n) → STy (someTree T)
unbiased-term : (d : ℕ) → (T : Tree n) → Tm (suc n)
unbiased-stm : (d : ℕ) → (T : Tree n) → STm (someTree T)
unbiased-comp : (d : ℕ) → (T : Tree n) → STm (someTree T)
unbiased-comp′ : (d : ℕ) → (T : Tree n) → STm (someTree T)

unbiased-type zero T = S⋆
unbiased-type (suc d) T = SArr (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false) (unbiased-type d T) (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true)

unbiased-term d T = stm-to-term (unbiased-stm d T)

unbiased-stm zero Sing = SHere
unbiased-stm zero (Join S T) = unbiased-comp zero (Join S T)
unbiased-stm (suc d) Sing = unbiased-comp (suc d) Sing
unbiased-stm (suc d) (Join T Sing) = SExt (unbiased-stm d T)
unbiased-stm (suc d) (Join T (Join T₁ T₂)) = unbiased-comp (suc d) (Join T (Join T₁ T₂))
-- unbiased-stm d Sing = SHere
-- unbiased-stm d (Join S (Join T T′)) = unbiased-comp d (Join S (Join T T′))
-- unbiased-stm zero (Join S Sing) = SExt (unbiased-stm zero S)
-- unbiased-stm (suc d) (Join S Sing) = SExt (unbiased-stm d S)

unbiased-comp d T = SCoh T (unbiased-type d T) (id-label-wt T)

unbiased-comp′ zero T = unbiased-comp zero T
unbiased-comp′ (suc d) Sing = unbiased-comp (suc d) Sing
unbiased-comp′ (suc d) (Join T Sing) = SExt (unbiased-comp′ d T)
unbiased-comp′ (suc d) T@(Join _ (Join _ _)) = unbiased-comp (suc d) T

-- unbiased-term d T with is-linear-dec T
-- ... | yes p = 0V
-- ... | no p = unbiased-comp d T

-- unbiased-comp d T = Coh (tree-to-ctx T) (unbiased-type d T) idSub

-- unbiased-type zero T = ⋆
-- unbiased-type (suc d) T = (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm) ─⟨ unbiased-type d T ⟩⟶ (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)

-- sub-from-linear-tree-unbiased : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → Sub (suc n) (suc m) (unbiased-type d T)
-- sub-from-linear-tree-unbiased Sing T d = ⟨ ⟨⟩ , (unbiased-comp d T) ⟩
-- sub-from-linear-tree-unbiased (Join S Sing) T d = unrestrict (sub-from-linear-tree-unbiased S T (suc d))

label-from-linear-tree-unbiased : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → Label (someTree T) S
label-from-linear-tree-unbiased Sing T d P = unbiased-comp′ d T
label-from-linear-tree-unbiased (Join S Sing) T d PHere = unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false
label-from-linear-tree-unbiased (Join S Sing) T d (PExt P) = label-from-linear-tree-unbiased S T (suc d) P
label-from-linear-tree-unbiased (Join S Sing) T d (PShift PHere) = unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true

identity-stm : (n : ℕ) → STm (someTree (n-disc n))
identity-stm n = unbiased-comp′ (suc n) (n-disc n)

-- label-from-linear-tree : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (t : Tm m) → (A : Ty m) → .(ty-dim A ≡ tree-dim S) → Label
-- label-from-linear-tree Sing t A p = ⟨ ⟨⟩ , t ⟩
-- label-from-linear-tree (Join S Sing) t (s ─⟨ A ⟩⟶ s′) p = ⟨ ⟨ (label-from-linear-tree S s A (cong pred p)) , s′ ⟩ , t ⟩

-- identity-tree : (t : Tm n) → (A : Ty n) → Tm n
-- identity-tree t A = Coh (tree-to-ctx (n-disc (ty-dim A))) (unbiased-type (suc (ty-dim A)) (n-disc (ty-dim A))) (sub-from-linear-tree (n-disc (ty-dim A)) ⦃ n-disc-is-linear (ty-dim A) ⦄ t A (sym (tree-dim-n-disc (ty-dim A))))
