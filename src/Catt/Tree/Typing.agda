open import Catt.Typing.Rule

module Catt.Tree.Typing {index : Set}
                        (rule : index → Rule)
                        (lift-rule : ∀ i → LiftRule rule (rule i))
                        (susp-rule : ∀ i → SuspRule rule (rule i))
                        (sub-rule : ∀ i → SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Tree
open import Catt.Tree.Properties

open import Catt.Typing rule
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing rule lift-rule
open import Catt.Suspension.Typing rule lift-rule susp-rule
open import Catt.Connection.Typing rule lift-rule susp-rule sub-rule

⌊_⌋-Ty : (T : Tree n) → Typing-Ctx ⌊ T ⌋
⌊_⌋-Ty Sing = TyAdd TyEmp TyStar
⌊_⌋-Ty (Join S T) = connect-susp-Ty (⌊_⌋-Ty S) (⌊_⌋-Ty T)

fst-var-Ty : (Γ : Ctx (suc n)) → Typing-Tm Γ (Var (fromℕ _)) ⋆
fst-var-Ty (∅ , ⋆) = TyVar zero
fst-var-Ty (∅ , s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)
fst-var-Ty (Γ , B , A) = lift-tm-typing (fst-var-Ty (Γ , B))

tree-last-var-Ty : (T : Tree n) → Typing-Tm ⌊ T ⌋ (tree-last-var T) ⋆
tree-last-var-Ty Sing = TyVar zero
tree-last-var-Ty (Join S T) = apply-sub-tm-typing (tree-last-var-Ty T) (connect-susp-inc-right-Ty ⌊ S ⌋)
