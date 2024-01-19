open import Catt.Typing.Rule

module Catt.Tree.Standard.Typing (rules : RuleSet)
                                  (tame : Tame rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Boundary

open import Catt.Tree.Structured.Typing rules
open import Catt.Tree.Structured.Typing.Properties rules tame
open import Catt.Tree.Boundary.Typing rules tame

standard-type-Ty : (d : ℕ) → (T : Tree n) → Typing-STy ⌊ T ⌋ (standard-type d T)
standard-stm-Ty : (d : ℕ) → (T : Tree n) → Typing-STm ⌊ T ⌋ (standard-stm d T) (standard-type d T)
standard-comp-Ty : (d : ℕ) → (T : Tree n) → Typing-STm ⌊ T ⌋ (standard-comp d T) (standard-type d T)

standard-type-Ty zero T = TySStar
standard-type-Ty (suc d) T
  = TySArr (TySConv (>>=-Ty (standard-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T false) TySStar) (reflexive≈sty (sym≃sty (standard-type-prop d T d ≤-refl false))))
           (standard-type-Ty d T)
           (TySConv (>>=-Ty (standard-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T true) TySStar) (reflexive≈sty (sym≃sty (standard-type-prop d T d ≤-refl true))))

standard-stm-Ty zero Sing = TySPath PHere
standard-stm-Ty zero (Join T₁ T₂) = standard-comp-Ty zero (Join T₁ T₂)
standard-stm-Ty (suc d) Sing = standard-comp-Ty (suc d) Sing
standard-stm-Ty (suc d) (Join T Sing) = TySConv (TySExt (standard-stm-Ty d T)) (reflexive≈sty (trans≃sty (map-sty-ext-susp-compat (standard-type d T)) (standard-type-susp-lem d T)))
standard-stm-Ty (suc d) (Join T (Join T₁ T₂)) = standard-comp-Ty (suc d) (Join T (Join T₁ T₂))

standard-comp-Ty d T = TySConv (TySCoh T (standard-type-Ty d T) (id-label-Ty T) TySStar) (reflexive≈sty (>>=′-id (standard-type d T)))

standard-comp′-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → Typing-STm ⌊ T ⌋ (standard-comp′ d T) (standard-type d T)
standard-comp′-Ty d T = transport-stm-typing (standard-comp-Ty d T) (sym≃stm (standard-comp′-compat d T)) refl≃sty

standard-label-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → .⦃ NonZero (tree-dim S) ⦄ → (T : Tree m) → Typing-Label ⌊ T ⌋ (standard-label S T ,, S⋆)
standard-label-Ty S T = stm-to-label-Ty S (standard-comp′-Ty (tree-dim S) T) (standard-type-Ty (tree-dim S) T)
