open import Catt.Typing.Rule

module Catt.Typing.EndoCoherenceRemoval (ops : Op)
                                        (rules : RuleSet) where

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

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Tree.Structured.Typing ops rules

open import Catt.Support
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support

open import Catt.Typing.EndoCoherenceRemoval.Rule

open Rule

HasEndoCoherenceRemoval : Set
HasEndoCoherenceRemoval = ∀ {m n}
                        → {Γ : Ctx m}
                        → {Δ : Ctx (suc n)}
                        → {s : Tm (suc n)}
                        → {A : Ty (suc n)}
                        → (supp : SuppTm Δ s ≡ full)
                        → {σ : Sub (suc n) m ⋆}
                        → {B : Ty m}
                        → Typing-Tm Γ (Coh Δ (s ─⟨ A ⟩⟶ s) σ) B
                        → Coh Δ (s ─⟨ A ⟩⟶ s) σ ≈[ Γ ]tm identity-term (A [ σ ]ty) (s [ σ ]tm)

HasEndoCoherenceRemoval-STm : Set
HasEndoCoherenceRemoval-STm = ∀ {m n}
                            → {Γ : Ctx m}
                            → {X : MaybeTree m}
                            → (S : Tree n)
                            → (s : STm (someTree S))
                            → (SuppSTm (incTree S) s ≡ full)
                            → (As : STy (someTree S))
                            → ops ⌊ S ⌋ (SuppSTm (incTree S) s) (SuppSTm (incTree S) s)
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
ecr-from-rule p sfull tty = Rule≈ _ (p [ (ECR _ _ _ sfull _ _) ]) tty
