open import Catt.Typing.Rule

module Catt.Tree.Typing (ops : Op)
                        (rules : RuleSet)
                        (tame : Tame ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Tree
open import Catt.Tree.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Globular.Typing ops rules
open import Catt.Suspension.Typing ops susp-op rules susp-cond
open import Catt.Wedge.Typing ops rules tame

⌊⌋-Ty : (T : Tree n) → Typing-Ctx ⌊ T ⌋
⌊⌋-Ty Sing = TyAdd TyEmp TyStar
⌊⌋-Ty (Join S T) = wedge-susp-Ty (⌊⌋-Ty S) (⌊⌋-Ty T)

fst-var-Ty : (Γ : Ctx (suc n)) → Typing-Tm Γ (Var (fromℕ _)) ⋆
fst-var-Ty (∅ , ⋆) = TyVar zero
fst-var-Ty (∅ , s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)
fst-var-Ty (Γ , B , A) = wk-tm-typing (fst-var-Ty (Γ , B))

tree-last-var-Ty : (T : Tree n) → Typing-Tm ⌊ T ⌋ (tree-last-var T) ⋆
tree-last-var-Ty Sing = TyVar zero
tree-last-var-Ty (Join S T) = apply-sub-tm-typing (tree-last-var-Ty T) (wedge-susp-inc-right-Ty ⌊ S ⌋)
