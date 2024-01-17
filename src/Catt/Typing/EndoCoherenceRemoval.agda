open import Catt.Typing.Rule

module Catt.Typing.EndoCoherenceRemoval (rules : RuleSet) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Suspension
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Path

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules
open import Catt.Tree.Structured.Typing rules

open import Catt.Typing.EndoCoherenceRemoval.Rule

open Rule

HasEndoCoherenceRemoval : Set
HasEndoCoherenceRemoval = ∀ {m n}
                        → {Γ : Ctx m}
                        → {s : Tm (suc n)}
                        → {A : Ty (suc n)}
                        → {σ : Sub (suc n) m ⋆}
                        → {Δ : Ctx (suc n)}
                        → {B : Ty m}
                        → Typing-Tm Γ (Coh Δ (s ─⟨ A ⟩⟶ s) σ) B
                        → Coh Δ (s ─⟨ A ⟩⟶ s) σ ≈[ Γ ]tm identity (ty-dim A) (sub-from-disc (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) (s [ σ ]tm))

HasEndoCoherenceRemoval-STm : Set
HasEndoCoherenceRemoval-STm = ∀ {m n}
                        → {Γ : Ctx m}
                        → {X : MaybeTree m}
                        → (S : Tree n)
                        → (s : STm (someTree S))
                        → (As : STy (someTree S))
                        → (L : Label X S)
                        → Typing-STm ⌊ S ⌋ s As
                        → Typing-STy ⌊ S ⌋ As
                        → Typing-Label Γ (L ,, S⋆)
                        → SCoh S (SArr s As s) (L ,, S⋆)
                          ≈[ Γ ]stm
                          (identity-stm (n-disc (sty-dim As))
                            >>= (stm-to-label (n-disc (sty-dim As)) s As ,, S⋆) ●lt (L ,, S⋆))

HasEndoCoherenceRemovalRule : Set
HasEndoCoherenceRemovalRule = ECRSet ⊆r rules

ecr-from-rule : HasEndoCoherenceRemovalRule → HasEndoCoherenceRemoval
ecr-from-rule p tty = Rule≈ _ (p [ (ECR _ _ _ _ _) ]) tty
