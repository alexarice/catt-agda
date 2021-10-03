{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Tree.Unbiased.Typing (index : ℕ)
                                 (rule : Fin index → Rule)
                                 (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                 (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                 (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Unbiased.Support
open import Catt.Tree.Support
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Discs
open import Catt.Discs.Typing index rule lift-rule
open import Catt.Suspension
open import Catt.Suspension.Typing index rule lift-rule susp-rule

-- unbiased-term-Ty : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ d) → Typing-Tm (tree-to-ctx T) (unbiased-term d T) (unbiased-type d T)
-- unbiased-comp-Ty : (d : ℕ) → .⦃ NonZero′ d ⦄ → (T : Tree n) → .(tree-dim T ≡ d) → Typing-Sub (tree-to-ctx T) Γ σ
--                  → Typing-Tm Γ (Coh T (unbiased-type d T) σ) (unbiased-type d T [ σ ]ty)
-- unbiased-type-Ty : (d : ℕ) → (T : Tree n) → .(d ≤ tree-dim T) → Typing-Ty (tree-to-ctx T) (unbiased-type d T)

-- unbiased-comp-Ty (suc d) T q σty = TyCoh (unbiased-type-Ty (suc d) T (≤-reflexive (sym q))) σty true (unbiased-supp-condition d T (recompute ((tree-dim T) ≟ (suc d)) q)) refl≈ty

-- unbiased-term-Ty d T q with is-linear-dec T
-- ... | yes p = TyVarZ (reflexive≈ty (linear-tree-unbiased-lem d T ⦃ p ⦄ q))
-- ... | no p = term-conversion (unbiased-comp-Ty d ⦃ NonZero′-subst q (non-linear-has-no-zero-dim T p) ⦄ T q id-Ty) (reflexive≈ty (id-on-ty (unbiased-type d T)))
--   where
--     non-linear-has-no-zero-dim : (T : Tree n) → ¬ is-linear T → NonZero′ (tree-dim T)
--     non-linear-has-no-zero-dim Sing p = ⊥-elim (p tt)
--     non-linear-has-no-zero-dim (Join S T) p with tree-dim (Join S T) | join-tree-has-non-zero-dim S T
--     ... | zero | q = ⊥-elim (q refl)
--     ... | suc d | q = it


-- unbiased-type-Ty zero T q = TyStar
-- unbiased-type-Ty (suc d) T q
--   = TyArr (apply-sub-tm-typing (unbiased-term-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))) (tree-inc-Ty d T false))
--           (apply-sub-ty-typing (unbiased-type-Ty d (tree-bd d T) (≤-reflexive (sym (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))))) (tree-inc-Ty d T false))
--           (term-conversion (apply-sub-tm-typing (unbiased-term-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))) (tree-inc-Ty d T true)) (reflexive≈ty (unbiased-type-inc-lem d T)))

unbiased-type-Ty : (d : ℕ) → (T : Tree n) → (d ≤ tree-dim T) → Typing-Ty (tree-to-ctx T) (unbiased-type d T)
unbiased-term-Ty : (d : ℕ) → (T : Tree n) → (tree-dim T ≡ d) → Typing-Tm (tree-to-ctx T) (unbiased-term d T) (unbiased-type d T)
unbiased-comp-Ty : (d : ℕ) → .⦃ NonZero′ d ⦄ → (T : Tree n) → (tree-dim T ≡ d)
                  → Typing-Tm (tree-to-ctx T) (unbiased-comp d T) (unbiased-type d T)

unbiased-type-Ty zero T q = TyStar
unbiased-type-Ty (suc d) T q = TyArr (term-conversion (apply-sub-tm-typing utty (tree-inc-Ty d T false)) (reflexive≈ty (sym≃ty (unbiased-type-prop d T d ≤-refl false)))) (unbiased-type-Ty d T (≤-trans (n≤1+n d) q)) (term-conversion (apply-sub-tm-typing utty (tree-inc-Ty d T true)) (reflexive≈ty (sym≃ty (unbiased-type-prop d T d ≤-refl true))))
  where
    utty = unbiased-term-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))

unbiased-term-Ty d T q with is-linear-dec T
... | yes p = TyVarZ (reflexive≈ty (linear-tree-unbiased-lem d T ⦃ p ⦄ q))
... | no p = unbiased-comp-Ty d ⦃ NonZero′-subst q (non-linear-has-no-zero-dim T p) ⦄ T q
  where
    non-linear-has-no-zero-dim : (T : Tree n) → ¬ is-linear T → NonZero′ (tree-dim T)
    non-linear-has-no-zero-dim Sing p = ⊥-elim (p tt)
    non-linear-has-no-zero-dim (Join S T) p with tree-dim (Join S T) | join-tree-has-non-zero-dim S T
    ... | zero | q = ⊥-elim (q refl)
    ... | suc d | q = it

unbiased-comp-Ty (suc d) T q = TyCoh (unbiased-type-Ty (suc d) T (≤-reflexive (sym q))) id-Ty true (unbiased-supp-condition d T q) (reflexive≈ty (id-on-ty _))

-- sub-from-sphere-unbiased-Ty : (d : ℕ) → (T : Tree n) → .(d ≡ tree-dim T) → Typing-Sub (Sphere d) (tree-to-ctx T) (sub-from-sphere-unbiased d T)
-- sub-from-sphere-unbiased-Ty d T p = sub-from-sphere-Ty d (unbiased-type-Ty d T (≤-reflexive p)) (unbiased-type-dim d T)

-- sub-from-disc-unbiased-Ty : (d : ℕ) → .⦃ NonZero′ d ⦄ → (T : Tree n) → .(d ≡ tree-dim T) → Typing-Sub (Disc d) (tree-to-ctx T) (sub-from-disc-unbiased d T)
-- sub-from-disc-unbiased-Ty d T p = sub-from-disc-Ty d (unbiased-type-Ty d T (≤-reflexive p)) (unbiased-type-dim d T) (term-conversion (unbiased-comp-Ty d T (sym p) id-Ty) (reflexive≈ty (id-on-ty (unbiased-type d T))))

sub-from-linear-tree-unbiased-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → .⦃ NonZero′ (tree-dim T) ⦄ → (d : ℕ) → (tree-dim T ≡ tree-dim S + d) → Typing-Sub (tree-to-ctx S) (tree-to-ctx T) (sub-from-linear-tree-unbiased S T d)
sub-from-linear-tree-unbiased-Ty Sing T d p = TyExt (TyNull (unbiased-type-Ty d T (≤-reflexive (sym p)))) (unbiased-comp-Ty d ⦃ NonZero′-subst p it ⦄ T p)
sub-from-linear-tree-unbiased-Ty (Join S Sing) T d p = unrestrictTy (sub-from-linear-tree-unbiased-Ty S T (suc d) (trans p (sym (+-suc (tree-dim S) d))))
