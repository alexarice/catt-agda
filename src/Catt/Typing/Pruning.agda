open import Catt.Typing.Rule

module Catt.Typing.Pruning (ops : Op) (rules : RuleSet) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules

open import Catt.Typing.Pruning.Rule

open Rule

HasPruning : Set
HasPruning = ∀ {m n}
           → {Γ : Ctx m}
           → {dy : Dyck (suc n) 0}
           → {A : Ty (3 + double n)}
           → (p : Peak dy)
           → {σ : Sub (3 + double n) m ⋆}
           → {B : Ty m}
           → {t : Tm m}
           → (peak-term p [ σ ]tm ≃tm identity-term B t)
           → {C : Ty m}
           → Typing-Tm Γ (Coh ⌊ dy ⌋d A σ) C
           → Coh ⌊ dy ⌋d A σ ≈[ Γ ]tm Coh ⌊ dy // p ⌋d (A [ π p ]ty) (σ //s p)

HasPruningRule : Set
HasPruningRule = PruningSet ⊆r rules

pruning-from-rule : HasPruningRule → HasPruning
pruning-from-rule p pk pf tty = Rule≈ _ (p [ Prune _ _ _ pk _ _ _ pf ]) tty
