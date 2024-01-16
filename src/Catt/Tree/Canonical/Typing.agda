open import Catt.Typing.Rule

module Catt.Tree.Canonical.Typing (rules : RuleSet)
                                  (tame : Tame rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Canonical
open import Catt.Tree.Canonical.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Boundary

open import Catt.Tree.Structured.Typing rules
open import Catt.Tree.Structured.Typing.Properties rules tame
open import Catt.Tree.Boundary.Typing rules tame

canonical-type-Ty : (d : ℕ) → (T : Tree n) → Typing-STy ⌊ T ⌋ (canonical-type d T)
canonical-stm-Ty : (d : ℕ) → (T : Tree n) → Typing-STm ⌊ T ⌋ (canonical-stm d T) (canonical-type d T)
canonical-comp-Ty : (d : ℕ) → (T : Tree n) → Typing-STm ⌊ T ⌋ (canonical-comp d T) (canonical-type d T)

canonical-type-Ty zero T = TySStar
canonical-type-Ty (suc d) T
  = TySArr (TySConv (>>=-Ty (canonical-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T false) TySStar) (reflexive≈sty (sym≃sty (canonical-type-prop d T d ≤-refl false))))
           (canonical-type-Ty d T)
           (TySConv (>>=-Ty (canonical-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T true) TySStar) (reflexive≈sty (sym≃sty (canonical-type-prop d T d ≤-refl true))))

canonical-stm-Ty zero Sing = TySPath PHere
canonical-stm-Ty zero (Join T₁ T₂) = canonical-comp-Ty zero (Join T₁ T₂)
canonical-stm-Ty (suc d) Sing = canonical-comp-Ty (suc d) Sing
canonical-stm-Ty (suc d) (Join T Sing) = TySConv (TySExt (canonical-stm-Ty d T)) (reflexive≈sty (trans≃sty (map-sty-ext-susp-compat (canonical-type d T)) (canonical-type-susp-lem d T)))
canonical-stm-Ty (suc d) (Join T (Join T₁ T₂)) = canonical-comp-Ty (suc d) (Join T (Join T₁ T₂))

canonical-comp-Ty d T = TySConv (TySCoh T (canonical-type-Ty d T) (id-label-Ty T) TySStar) (reflexive≈sty (>>=′-id (canonical-type d T)))

canonical-comp′-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → Typing-STm ⌊ T ⌋ (canonical-comp′ d T) (canonical-type d T)
canonical-comp′-Ty d T = transport-stm-typing (canonical-comp-Ty d T) (sym≃stm (canonical-comp′-compat d T)) refl≃sty

canonical-label-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → .⦃ NonZero (tree-dim S) ⦄ → (T : Tree m) → Typing-Label ⌊ T ⌋ (canonical-label S T ,, S⋆)
canonical-label-Ty S T = stm-to-label-Ty S (canonical-comp′-Ty (tree-dim S) T) (canonical-type-Ty (tree-dim S) T)
