open import Catt.Typing.Rule

module Catt.Tree.Unbiased.Typing {index : Set}
                                 (rule : index → Rule)
                                 (lift-rule : ∀ i → LiftRule rule (rule i))
                                 (susp-rule : ∀ i → SuspRule rule (rule i))
                                 (sub-rule : ∀ i → SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Path
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Typing.Properties rule lift-rule susp-rule sub-rule

unbiased-type-Ty : (d : ℕ) → (T : Tree n) → Typing-STy (tree-to-ctx T) (unbiased-type d T)
unbiased-stm-Ty : (d : ℕ) → (T : Tree n) → Typing-STm (tree-to-ctx T) (unbiased-stm d T) (unbiased-type d T)
unbiased-comp-Ty : (d : ℕ) → (T : Tree n) → Typing-STm (tree-to-ctx T) (unbiased-comp d T) (unbiased-type d T)

unbiased-type-Ty zero T = TySStar
unbiased-type-Ty (suc d) T
  = TySArr (TySConv (extend-Ty (unbiased-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T false) TySStar) (reflexive≈sty (sym≃sty (unbiased-type-prop d T d ≤-refl false))))
           (unbiased-type-Ty d T)
           (TySConv (extend-Ty (unbiased-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T true) TySStar) (reflexive≈sty (sym≃sty (unbiased-type-prop d T d ≤-refl true))))

unbiased-stm-Ty zero Sing = TySPath PHere
unbiased-stm-Ty zero (Join T₁ T₂) = unbiased-comp-Ty zero (Join T₁ T₂)
unbiased-stm-Ty (suc d) Sing = unbiased-comp-Ty (suc d) Sing
unbiased-stm-Ty (suc d) (Join T Sing) = TySConv (TySExt (unbiased-stm-Ty d T)) (reflexive≈sty (trans≃sty (map-sty-pext-susp-compat (unbiased-type d T)) (unbiased-type-susp-lem d T)))
unbiased-stm-Ty (suc d) (Join T (Join T₁ T₂)) = unbiased-comp-Ty (suc d) (Join T (Join T₁ T₂))

unbiased-comp-Ty d T = TySConv (TySCoh T (unbiased-type-Ty d T) (id-label-Ty T) TySStar) (reflexive≈sty (id-label-on-sty (unbiased-type d T)))

unbiased-comp′-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → Typing-STm (tree-to-ctx T) (unbiased-comp′ d T) (unbiased-type d T)
unbiased-comp′-Ty d T = transport-stm-typing (unbiased-comp-Ty d T) (sym≃stm (unbiased-comp′-compat d T)) refl≃sty

label-from-linear-tree-unbiased-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → .⦃ NonZero (tree-dim S + d) ⦄ → Typing-Label (tree-to-ctx T) (label-from-linear-tree-unbiased S T d ,, unbiased-type d T)
label-from-linear-tree-unbiased-Ty Sing T d = TySing (unbiased-comp′-Ty d ⦃ it ⦄ T)
label-from-linear-tree-unbiased-Ty (Join S Sing) T d
  = TyJoin (transport-stm-typing (extend-Ty (unbiased-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T false) TySStar) refl≃stm (sym≃sty (unbiased-type-prop d T d ≤-refl false)))
           (label-from-linear-tree-unbiased-Ty S T (suc d) ⦃ NonZero-subst (sym (+-suc (tree-dim S) d)) it ⦄)
           (TySing (transport-stm-typing (extend-Ty (unbiased-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T true) TySStar) refl≃stm (sym≃sty (unbiased-type-prop d T d ≤-refl true))))

label-from-linear-tree-unbiased-Ty-0 : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → .⦃ NonZero (tree-dim S) ⦄ → Typing-Label (tree-to-ctx T) (label-from-linear-tree-unbiased S T 0 ,, S⋆)
label-from-linear-tree-unbiased-Ty-0 S T = label-from-linear-tree-unbiased-Ty S T 0 ⦃ NonZero-subst (sym (+-identityʳ (tree-dim S))) it ⦄

label-from-linear-tree-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {a : STm X} → {As : STy X} → Typing-STm Γ a As → Typing-STy Γ As → .(p : tree-dim S ≤ sty-dim As) → Typing-Label Γ (label-from-linear-tree S a As p ,, label-from-linear-tree-type S As)
label-from-linear-tree-type-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {As : STy X} → Typing-STy Γ As → Typing-STy Γ (label-from-linear-tree-type S As)

label-from-linear-tree-Ty Sing aTy AsTy p = TySing aTy
label-from-linear-tree-Ty (Join S Sing) aTy AsTy p = transport-label-typing (unrestrict-label-Ty (label-from-linear-tree-Ty S aTy AsTy (≤-trans (n≤1+n (tree-dim S)) p)) (label-from-linear-tree-type-Ty S AsTy) ⦃ label-from-linear-tree-nz S _ p ⦄) refl≃l (sym≃sty (label-from-linear-tree-type-prop S _))

label-from-linear-tree-type-Ty Sing AsTy = AsTy
label-from-linear-tree-type-Ty (Join S Sing) AsTy = label-from-linear-tree-type-Ty S (TySArr-proj₂ AsTy)

label-from-linear-tree-type-≈ : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (As ≈[ Γ ]sty Bs) → label-from-linear-tree-type S As ≈[ Γ ]sty label-from-linear-tree-type S Bs
label-from-linear-tree-type-≈ Sing p = p
label-from-linear-tree-type-≈ (Join S Sing) p = label-from-linear-tree-type-≈ S (sty-base-≈ p)

label-from-linear-tree-≈ : (S : Tree n) → .⦃ _ : is-linear S ⦄
                         → {a b : STm X} → (a ≈[ Γ ]stm b)
                         → {As Bs : STy X} → (q : As ≈[ Γ ]sty Bs)
                         → .(r : tree-dim S ≤ sty-dim As)
                         → label-from-linear-tree S a As r ≈[ Γ ]l label-from-linear-tree S b Bs (≤-trans r (≤-reflexive (sty-dim-≈ q)))
label-from-linear-tree-≈ Sing p q r .get P = p
label-from-linear-tree-≈ (Join S Sing) p q r .get PHere = sty-src-≈ (label-from-linear-tree-type-≈ S q) ⦃ _ ⦄
label-from-linear-tree-≈ (Join S Sing) p q r .get (PExt P) = label-from-linear-tree-≈ S p q _ .get P
label-from-linear-tree-≈ (Join S Sing) p q r .get (PShift PHere) = sty-tgt-≈ (label-from-linear-tree-type-≈ S q) ⦃ _ ⦄
