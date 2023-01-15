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
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Path
open import Catt.Typing.Properties rule

HasDiscRemoval : Set
HasDiscRemoval = ∀ {m n}
               → {ΓS : CtxOrTree m}
               → (S : Tree n)
               → .⦃ _ : is-linear S ⦄
               → .⦃ NonZero (tree-dim S) ⦄
               → (L : Label (COT-to-MT ΓS) S)
               → Typing-Label ΓS (L ,, S⋆)
               → (unbiased-comp (tree-dim S) S >>= L ,, S⋆) ≈[ ΓS ]stm L (is-linear-max-path S)

module Conditions (dr : HasDiscRemoval) where

  -- lift-rule : ∀ {m n}
  --           → {Γ : Ctx m}
  --           → (S : Tree n)
  --           → .⦃ _ : is-linear S ⦄
  --           → .⦃ NonZero (tree-dim S) ⦄
  --           → (L : Label (Other m) S)
  --           → {A : Ty m}
  --           → Typing-Label (incCtx (Γ , A)) (lift-label (L ,, S⋆))
  --           → lift-stm (unbiased-comp (tree-dim S) S >>= L ,, S⋆) ≈[ incCtx (Γ , A) ]stm lift-stm (L (is-linear-max-path S))
  -- lift-rule S L Lty = dr S (lift-stm ∘ L) Lty

  susp-rule : ∀ {m n}
            → {ΓS : CtxOrTree m}
            → (S : Tree n)
            → .⦃ _ : is-linear S ⦄
            → .⦃ NonZero (tree-dim S) ⦄
            → (L : Label (COT-to-MT ΓS) S)
            → Typing-Label
