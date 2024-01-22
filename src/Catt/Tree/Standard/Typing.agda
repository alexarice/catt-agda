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

standard-sty-Ty : (d : ℕ) → (T : Tree n) → Typing-STy ⌊ T ⌋ (standard-sty d T)
standard-stm-Ty : (d : ℕ) → (T : Tree n) → Typing-STm ⌊ T ⌋ (standard-stm d T) (standard-sty d T)
standard-coh-Ty : (d : ℕ) → (T : Tree n) → Typing-STm ⌊ T ⌋ (standard-coh d T) (standard-sty d T)

standard-sty-Ty zero T = TySStar
standard-sty-Ty (suc d) T
  = TySArr (TySConv (>>=-Ty (standard-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T false) TySStar) (reflexive≈sty (sym≃sty (standard-sty-prop d T d ≤-refl false))))
           (standard-sty-Ty d T)
           (TySConv (>>=-Ty (standard-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T true) TySStar) (reflexive≈sty (sym≃sty (standard-sty-prop d T d ≤-refl true))))

standard-stm-Ty zero Sing = TySPath PHere
standard-stm-Ty zero (Join T₁ T₂) = standard-coh-Ty zero (Join T₁ T₂)
standard-stm-Ty (suc d) Sing = standard-coh-Ty (suc d) Sing
standard-stm-Ty (suc d) (Join T Sing) = TySConv (TySExt (standard-stm-Ty d T)) (reflexive≈sty (trans≃sty (map-sty-ext-susp-compat (standard-sty d T)) (standard-sty-susp-lem d T)))
standard-stm-Ty (suc d) (Join T (Join T₁ T₂)) = standard-coh-Ty (suc d) (Join T (Join T₁ T₂))

standard-coh-Ty d T = TySConv (TySCoh T (standard-sty-Ty d T) (id-label-Ty T) TySStar) (reflexive≈sty (>>=′-id (standard-sty d T)))

standard-coh′-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → Typing-STm ⌊ T ⌋ (standard-coh′ d T) (standard-sty d T)
standard-coh′-Ty d T = transport-stm-typing (standard-coh-Ty d T) (sym≃stm (standard-coh′-compat d T)) refl≃sty

standard-label-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → .⦃ NonZero (tree-dim S) ⦄ → (T : Tree m) → Typing-Label ⌊ T ⌋ (standard-label S T ,, S⋆)
standard-label-Ty S T = stm-to-label-Ty S (standard-coh′-Ty (tree-dim S) T) (standard-sty-Ty (tree-dim S) T)
