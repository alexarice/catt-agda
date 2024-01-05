open import Catt.Typing.Rule

module Catt.Tree.Canonical.Typing {index : Set}
                                 (rule : index → Rule)
                                 (lift-rule : ∀ i → LiftRule rule (rule i))
                                 (susp-rule : ∀ i → SuspRule rule (rule i))
                                 (sub-rule : ∀ i → SubRule rule (rule i)) where

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

open import Catt.Tree.Structured.Typing rule
open import Catt.Tree.Structured.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Tree.Boundary.Typing rule lift-rule susp-rule sub-rule

canonical-type-Ty : (d : ℕ) → (T : Tree n) → Typing-STy (tree-to-ctx T) (canonical-type d T)
canonical-stm-Ty : (d : ℕ) → (T : Tree n) → Typing-STm (tree-to-ctx T) (canonical-stm d T) (canonical-type d T)
canonical-comp-Ty : (d : ℕ) → (T : Tree n) → Typing-STm (tree-to-ctx T) (canonical-comp d T) (canonical-type d T)

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

canonical-comp′-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → Typing-STm (tree-to-ctx T) (canonical-comp′ d T) (canonical-type d T)
canonical-comp′-Ty d T = transport-stm-typing (canonical-comp-Ty d T) (sym≃stm (canonical-comp′-compat d T)) refl≃sty

canonical-label-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → .⦃ NonZero (tree-dim S) ⦄ → (T : Tree m) → Typing-Label (tree-to-ctx T) (canonical-label S T ,, S⋆)
canonical-label-Ty S T = stm-to-label-Ty S (canonical-comp′-Ty (tree-dim S) T) (canonical-type-Ty (tree-dim S) T)

-- label-from-linear-tree-canonical-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → .⦃ NonZero (tree-dim S + d) ⦄ → Typing-Label (tree-to-ctx T) (label-from-linear-tree-canonical S T d ,, canonical-type d T)
-- label-from-linear-tree-canonical-Ty Sing T d = TySing (canonical-comp′-Ty d ⦃ it ⦄ T)
-- label-from-linear-tree-canonical-Ty (Join S Sing) T d
--   = TyJoin (transport-stm-typing (>>=-Ty (canonical-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T false) TySStar) refl≃stm (sym≃sty (canonical-type-prop d T d ≤-refl false)))
--            (label-from-linear-tree-canonical-Ty S T (suc d) ⦃ NonZero-subst (sym (+-suc (tree-dim S) d)) it ⦄)
--            (TySing (transport-stm-typing (>>=-Ty (canonical-stm-Ty d (tree-bd d T)) (tree-inc-Ty d T true) TySStar) refl≃stm (sym≃sty (canonical-type-prop d T d ≤-refl true))))

-- label-from-linear-tree-canonical-Ty-0 : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → .⦃ NonZero (tree-dim S) ⦄ → Typing-Label (tree-to-ctx T) (label-from-linear-tree-canonical S T 0 ,, S⋆)
-- label-from-linear-tree-canonical-Ty-0 S T = label-from-linear-tree-canonical-Ty S T 0 ⦃ NonZero-subst (sym (+-identityʳ (tree-dim S))) it ⦄

-- label-from-linear-tree-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {a : STm X} → {As : STy X} → Typing-STm Γ a As → Typing-STy Γ As → .(p : tree-dim S ≤ sty-dim As) → Typing-Label Γ (label-from-linear-tree S a As p ,, label-from-linear-tree-type S As)
-- label-from-linear-tree-type-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {As : STy X} → Typing-STy Γ As → Typing-STy Γ (label-from-linear-tree-type S As)

-- label-from-linear-tree-Ty Sing aTy AsTy p = TySing aTy
-- label-from-linear-tree-Ty (Join S Sing) aTy AsTy p = transport-label-typing (unrestrict-label-Ty (label-from-linear-tree-Ty S aTy AsTy (≤-trans (n≤1+n (tree-dim S)) p)) (label-from-linear-tree-type-Ty S AsTy) ⦃ label-from-linear-tree-nz S _ p ⦄) refl≃l (sym≃sty (label-from-linear-tree-type-prop S _))

-- label-from-linear-tree-type-Ty Sing AsTy = AsTy
-- label-from-linear-tree-type-Ty (Join S Sing) AsTy = label-from-linear-tree-type-Ty S (TySArr-proj₂ AsTy)

-- label-from-linear-tree-type-≈ : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (As ≈[ Γ ]sty Bs) → label-from-linear-tree-type S As ≈[ Γ ]sty label-from-linear-tree-type S Bs
-- label-from-linear-tree-type-≈ Sing p = p
-- label-from-linear-tree-type-≈ (Join S Sing) p = label-from-linear-tree-type-≈ S (sty-base-≈ p)

-- label-from-linear-tree-≈ : (S : Tree n) → .⦃ _ : is-linear S ⦄
--                          → {a b : STm X} → (a ≈[ Γ ]stm b)
--                          → {As Bs : STy X} → (q : As ≈[ Γ ]sty Bs)
--                          → .(r : tree-dim S ≤ sty-dim As)
--                          → label-from-linear-tree S a As r ≈[ Γ ]l label-from-linear-tree S b Bs (≤-trans r (≤-reflexive (sty-dim-≈ q)))
-- label-from-linear-tree-≈ Sing p q r .get P = p
-- label-from-linear-tree-≈ (Join S Sing) p q r .get PHere = sty-src-≈ (label-from-linear-tree-type-≈ S q) ⦃ _ ⦄
-- label-from-linear-tree-≈ (Join S Sing) p q r .get (PExt P) = label-from-linear-tree-≈ S p q _ .get P
-- label-from-linear-tree-≈ (Join S Sing) p q r .get (PShift PHere) = sty-tgt-≈ (label-from-linear-tree-type-≈ S q) ⦃ _ ⦄