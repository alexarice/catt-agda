open import Catt.Typing.Rule

module Catt.Tree.Standard.Typing (ops : Op)
                                 (rules : RuleSet)
                                 (tame : Tame ops rules) where

open Tame tame

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
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties

open import Catt.Ops.Tree ops

open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Standard.Support

open import Catt.Typing ops rules
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame
open import Catt.Tree.Boundary.Typing ops rules tame

standard-sty-Ty : (d : ℕ) → (T : Tree n) → Typing-STy ⌊ T ⌋ (standard-sty d T)
standard-stm-Ty : (d : ℕ)
                → (T : Tree n)
                → d ≥ tree-dim T
                → Typing-STm ⌊ T ⌋ (standard-stm d T) (standard-sty d T)
standard-coh-Ty : (d : ℕ)
                → .⦃ NonZero d ⦄
                → (T : Tree n)
                → d ≥ tree-dim T
                → Typing-STm ⌊ T ⌋ (standard-coh d T) (standard-sty d T)

standard-sty-Ty zero T = TySStar
standard-sty-Ty (suc d) T
  = TySArr (TySConv (>>=-Ty (standard-stm-Ty d (tree-bd d T) (tree-dim-bd″ d T)) (tree-inc-Ty d T false) TySStar) (reflexive≈sty (sym≃sty (standard-sty-prop d T d ≤-refl false))))
           (standard-sty-Ty d T)
           (TySConv (>>=-Ty (standard-stm-Ty d (tree-bd d T) (tree-dim-bd″ d T)) (tree-inc-Ty d T true) TySStar) (reflexive≈sty (sym≃sty (standard-sty-prop d T d ≤-refl true))))

standard-stm-Ty zero Sing p = TySPath PHere
standard-stm-Ty (suc d) Sing p = standard-coh-Ty (suc d) Sing p
standard-stm-Ty (suc d) (Join T Sing) p = TySConv (TySExt (standard-stm-Ty d T (≤-pred p))) (reflexive≈sty (trans≃sty (map-sty-ext-susp-compat (standard-sty d T)) (standard-sty-susp-lem d T)))
standard-stm-Ty (suc d) (Join T (Join T₁ T₂)) p = standard-coh-Ty (suc d) (Join T (Join T₁ T₂)) p

standard-coh-Ty (suc d) T p
  = TySConv (TySCoh T
                    (subst₂ (ops-s T)
                            (sym (supp-standard-lem d T false))
                            (sym (supp-standard-lem d T true))
                            (standard-op-s standard-op T d p))
                    (standard-sty-Ty (suc d) T)
                    (id-label-Ty T)
                    TySStar)
            (reflexive≈sty (>>=′-id (standard-sty (suc d) T)))

standard-coh′-Ty : (d : ℕ)
                 → .⦃ NonZero d ⦄
                 → (T : Tree n)
                 → d ≥ tree-dim T
                 → Typing-STm ⌊ T ⌋ (standard-coh′ d T) (standard-sty d T)
standard-coh′-Ty d T p = transport-stm-typing (standard-coh-Ty d T p) (sym≃stm (standard-coh′-compat d T)) refl≃sty

standard-label-Ty : (S : Tree n)
                  → .⦃ _ : is-linear S ⦄
                  → .⦃ NonZero (tree-dim S) ⦄
                  → (T : Tree m)
                  → (tree-dim S ≥ tree-dim T)
                  → Typing-Label ⌊ T ⌋ (standard-label S T ,, S⋆)
standard-label-Ty S T p = stm-to-label-Ty S (standard-coh′-Ty (tree-dim S) T p) (standard-sty-Ty (tree-dim S) T)
