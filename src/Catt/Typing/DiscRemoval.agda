open import Catt.Typing.Rule

module Catt.Typing.DiscRemoval (ops : Op) (rules : RuleSet) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct

open import Catt.Typing ops rules
open import Catt.Tree.Structured.Typing ops rules

open import Catt.Typing.DiscRemoval.Rule

HasDiscRemoval : Set
HasDiscRemoval = ∀ {m n}
               → .⦃ NonZero n ⦄
               → {Γ : Ctx m}
               → {σ : Sub (disc-size n) m ⋆}
               → {A : Ty m}
               → Typing-Tm Γ (disc-term n σ) A
               → disc-term n σ ≈[ Γ ]tm 0V [ σ ]tm

HasDiscRemoval-STm : Set
HasDiscRemoval-STm = ∀ {m n}
               → {Γ : Ctx m}
               → {X : MaybeTree m}
               → (S : Tree n)
               → .⦃ _ : is-linear S ⦄
               → .⦃ NonZero (tree-dim S) ⦄
               → (L : Label X S)
               → Typing-Label Γ (L ,, S⋆)
               → disc-stm S >>= (L ,, S⋆) ≈[ Γ ]stm L (is-linear-max-path S)

HasDiscRemovalRule : Set
HasDiscRemovalRule = DiscRemovalSet ⊆r rules

dr-from-rule : HasDiscRemovalRule → HasDiscRemoval
dr-from-rule p tty = Rule≈ _ (p [ (DR _ _) ]) tty
