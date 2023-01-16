open import Catt.Typing.Base

module Catt.Typing.DiscRemoval {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Support
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Path
open import Catt.Typing.Properties rule
open import Catt.Suspension

HasDiscRemoval : Set
HasDiscRemoval = ∀ {m n}
               → {Γ : Ctx m}
               → {X : MaybeTree m}
               → (S : Tree n)
               → .⦃ _ : is-linear S ⦄
               → .⦃ NonZero (tree-dim S) ⦄
               → (L : Label X S)
               → Typing-Label Γ (L ,, S⋆)
               → (unbiased-comp (tree-dim S) S >>= L ,, S⋆) ≈[ Γ ]stm L (is-linear-max-path S)

module Conditions (dr : HasDiscRemoval) where

  lift-rule : ∀ {m n}
            → {Γ : Ctx m}
            → (S : Tree n)
            → .⦃ _ : is-linear S ⦄
            → .⦃ NonZero (tree-dim S) ⦄
            → (L : Label (Other m) S)
            → {A : Ty m}
            → Typing-Label (Γ , A) (lift-label (L ,, S⋆))
            → lift-stm (unbiased-comp (tree-dim S) S >>= L ,, S⋆) ≈[ Γ , A ]stm lift-stm (L (is-linear-max-path S))
  lift-rule S L Lty = dr S (lift-stm ∘ L) Lty

  susp-rule : ∀ {m n}
            → {Γ : Ctx m}
            → {X : MaybeTree m}
            → (S : Tree n)
            → .⦃ _ : is-linear S ⦄
            → .⦃ NonZero (tree-dim S) ⦄
            → (L : Label X S)
            → Typing-Label (suspCtx Γ) (susp-label-full L ,, S⋆)
            → susp-stm (unbiased-comp (tree-dim S) S >>= L ,, S⋆) ≈[ suspCtx Γ ]stm susp-stm (L (is-linear-max-path S))
  susp-rule S L Lty = begin
    susp-stm (unbiased-comp (tree-dim S) S >>= L ,, S⋆)
      ≈⟨ reflexive≈stm (susp-stm-SCoh S (unbiased-type (tree-dim S) S) (L ,, S⋆)) ⟩
    SCoh S (unbiased-type (tree-dim S) S) (susp-label (L ,, S⋆))
      ≈⟨ reflexive≈stm (SCoh-unrestrict S (unbiased-type (tree-dim S) S) (susp-label (L ,, S⋆))) ⟩
    SCoh (suspTree S) (susp-sty (unbiased-type (tree-dim S) S)) (susp-label-full L ,, S⋆)
      ≈⟨ reflexive≈stm (≃SCoh (suspTree S) (unbiased-type-susp-lem (tree-dim S) S) refl≃l refl≃sty) ⟩
    SCoh (suspTree S) (unbiased-type (suc (tree-dim S)) (suspTree S)) (susp-label-full L ,, S⋆)
      ≈⟨ dr (suspTree S) (susp-label-full L) Lty ⟩
    susp-label-full L (is-linear-max-path (suspTree S))
      ≡⟨⟩
    susp-stm (L (is-linear-max-path S)) ∎
    where
      open Reasoning stm-setoid-≈

  sub-rule : ∀ {m n l}
           → {Γ : Ctx l}
           → {Δ : Ctx m}
           → {X : MaybeTree m}
           → (S : Tree n)
           → .⦃ _ : is-linear S ⦄
           → .⦃ NonZero (tree-dim S) ⦄
           → (L : Label X S)
           → (σ : Sub m l ⋆)
           → Typing-Label Γ (label-sub (L ,, S⋆) σ)
           → stm-sub (unbiased-comp (tree-dim S) S >>= L ,, S⋆) σ ≈[ Γ ]stm stm-sub (L (is-linear-max-path S)) σ
  sub-rule S L σ Lty = begin
    stm-sub (unbiased-comp (tree-dim S) S >>= L ,, S⋆) σ
      ≈⟨ reflexive≈stm (stm-sub-SCoh S (unbiased-type (tree-dim S) S) (L ,, S⋆) σ) ⟩
    SCoh S (unbiased-type (tree-dim S) S) (label-sub (L ,, S⋆) σ)
      ≈⟨ dr S (ap (label-sub (L ,, S⋆) σ)) Lty ⟩
    stm-sub (L (is-linear-max-path S)) σ ∎
    where
      open Reasoning stm-setoid-≈

  -- support-rule : ∀ {m n}
  --              → {ΓS : CtxOrTree m}
  --              → (S : Tree n)
  --              → .⦃ _ : is-linear S ⦄
  --              → .⦃ NonZero (tree-dim S) ⦄
  --              → (L : Label (COT-to-MT ΓS) S)
  --              → Typing-Label (COT-to-Ctx ΓS) (L ,, S⋆)
  --              → DCM ΓS (FVSTm (unbiased-comp (tree-dim S) S >>= L ,, S⋆)) ≡ DCM ΓS (FVSTm (L (is-linear-max-path S)))
  -- support-rule = {!!}
