{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Unbiased.Typing (index : ℕ)
                                 (rule : Fin index → Rule)
                                 (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                 (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                 (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
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
open import Catt.Tree.Pasting
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Unbiased.Support
open import Catt.Tree.Support
open import Catt.Suspension
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Globular

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

unbiased-type-Ty : (d : ℕ) → (T : Tree n) → (d ≤ suc (tree-dim T)) → Typing-Ty (tree-to-ctx T) (unbiased-type d T)
unbiased-term-Ty : (d : ℕ) → (T : Tree n) → (tree-dim T ≡ d) → Typing-Tm (tree-to-ctx T) (unbiased-term d T) (unbiased-type d T)
unbiased-comp-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → (tree-dim T ≡ d)
                  → Typing-Tm (tree-to-ctx T) (unbiased-comp d T) (unbiased-type d T)

unbiased-type-Ty zero T q = TyStar
unbiased-type-Ty (suc d) T q =
  TyArr (term-conversion (apply-sub-tm-typing utty (tree-inc-Ty d T false)) (reflexive≈ty (sym≃ty (unbiased-type-prop d T d ≤-refl false))))
        (unbiased-type-Ty d T (≤-trans (n≤1+n d) q))
        (term-conversion (apply-sub-tm-typing utty (tree-inc-Ty d T true)) (reflexive≈ty (sym≃ty (unbiased-type-prop d T d ≤-refl true))))
  where
    utty = unbiased-term-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-pred q))

unbiased-term-Ty d T q with is-linear-dec T
... | no p = unbiased-comp-Ty d ⦃ NonZero-subst q (non-linear-has-no-zero-dim T p) ⦄ T q
  where
    non-linear-has-no-zero-dim : (T : Tree n) → ¬ is-linear T → NonZero (tree-dim T)
    non-linear-has-no-zero-dim Sing p = ⊥-elim (p tt)
    non-linear-has-no-zero-dim (Join S T) p = it

... | yes p with tree-to-ctx T | tree-to-ctx-Ty T | linear-tree-unbiased-lem d T ⦃ p ⦄ q
... | Γ , A | TyAdd Γty x | l = TyVarZ x (reflexive≈ty l)

unbiased-comp-Ty (suc d) T q = TyCoh ⦃ tree-to-pd T ⦄ (unbiased-type-Ty (suc d) T (s≤s (≤-trans (n≤1+n d) (≤-reflexive (sym q))))) (id-Ty (tree-to-ctx-Ty T)) true (unbiased-supp-condition d T q) (reflexive≈ty (id-on-ty _))

-- sub-from-sphere-unbiased-Ty : (d : ℕ) → (T : Tree n) → .(d ≡ tree-dim T) → Typing-Sub (Sphere d) (tree-to-ctx T) (sub-from-sphere-unbiased d T)
-- sub-from-sphere-unbiased-Ty d T p = sub-from-sphere-Ty d (unbiased-type-Ty d T (≤-reflexive p)) (unbiased-type-dim d T)

-- sub-from-disc-unbiased-Ty : (d : ℕ) → .⦃ NonZero′ d ⦄ → (T : Tree n) → .(d ≡ tree-dim T) → Typing-Sub (Disc d) (tree-to-ctx T) (sub-from-disc-unbiased d T)
-- sub-from-disc-unbiased-Ty d T p = sub-from-disc-Ty d (unbiased-type-Ty d T (≤-reflexive p)) (unbiased-type-dim d T) (term-conversion (unbiased-comp-Ty d T (sym p) id-Ty) (reflexive≈ty (id-on-ty (unbiased-type d T))))

sub-from-linear-tree-unbiased-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → .⦃ NonZero (tree-dim T) ⦄ → (d : ℕ) → (tree-dim T ≡ tree-dim S + d) → Typing-Sub (tree-to-ctx S) (tree-to-ctx T) (sub-from-linear-tree-unbiased S T d)
sub-from-linear-tree-unbiased-Ty Sing T d p = TyExt (TyNull (unbiased-type-Ty d T (≤-trans (≤-reflexive (sym p)) (n≤1+n (tree-dim T))))) TyStar (unbiased-comp-Ty d ⦃ NonZero-subst p it ⦄ T p)
sub-from-linear-tree-unbiased-Ty (Join S Sing) T d p = unrestrictTy (sub-from-linear-tree-unbiased-Ty S T (suc d) (trans p (trans (cong (_+ d) (max-lem (suc (tree-dim S)))) (sym (+-suc (tree-dim S) d)))))

sub-from-linear-tree-unbiased-Ty-0 : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → .⦃ NonZero (tree-dim T) ⦄ → .(tree-dim T ≡ tree-dim S) → Typing-Sub (tree-to-ctx S) (tree-to-ctx T) (sub-from-linear-tree-unbiased S T 0)
sub-from-linear-tree-unbiased-Ty-0 S T p = sub-from-linear-tree-unbiased-Ty S T 0 (trans (recompute ((tree-dim T) ≟ (tree-dim S)) p) (sym (+-identityʳ (tree-dim S))))

sub-from-linear-tree-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → Typing-Tm Γ t A → Typing-Ty Γ A → (p : ty-dim A ≡ tree-dim S) → Typing-Sub (tree-to-ctx S) Γ (sub-from-linear-tree S t A p)
sub-from-linear-tree-Ty Sing tty TyStar p = TyExt (TyNull TyStar) TyStar tty
sub-from-linear-tree-Ty (Join S Sing) tty (TyArr sty Aty sty′) p
  rewrite (≃c-to-≡ (susp-lin-tree S)) =
    TyExt (TyExt (sub-from-linear-tree-Ty S sty Aty (max-pred-0 p)) (‼-Ty (tree-to-ctx-Ty S) zero)
                 (term-conversion sty′ (reflexive≈ty (sym≃ty (sub-from-linear-tree-‼-0 S _ _ (max-pred-0 p))))))
          (TyArr (var-Ty (TyAdd (tree-to-ctx-Ty S) (‼-Ty (tree-to-ctx-Ty S) zero)) (suc zero))
                 (lift-ty-typing (‼-Ty (tree-to-ctx-Ty S) zero))
                 (var-Ty (TyAdd (tree-to-ctx-Ty S) (‼-Ty (tree-to-ctx-Ty S) zero)) zero))
          (term-conversion tty (reflexive≈ty (sym≃ty (Arr≃ (sub-from-linear-tree-0V S _ _ (max-pred-0 p))
                                                           (trans≃ty (lift-sub-comp-lem-ty (sub-from-linear-tree S _ _ _) (tree-to-ctx S ‼ zero)) (sub-from-linear-tree-‼-0 S _ _ (max-pred-0 p)))
                                                           refl≃tm))))

identity-Ty : Typing-Tm Γ t A → Typing-Ty Γ A → Typing-Tm Γ (identity t A) (t ─⟨ A ⟩⟶ t)
identity-Ty {t = t} {A = A} tty Aty
  = TyCoh ⦃ tree-to-pd (n-disk (ty-dim A)) ⦄
          (unbiased-type-Ty (suc (ty-dim A))
                            (n-disk (ty-dim A))
                            (s≤s (≤-reflexive (sym (tree-dim-n-disk (ty-dim A))))))
          (sub-from-linear-tree-Ty (n-disk (ty-dim A)) ⦃ n-disk-is-linear (ty-dim A) ⦄
                                   tty
                                   Aty
                                   (sym (tree-dim-n-disk (ty-dim A))))
          false
          (full-⊆ lem-supp)
          (reflexive≈ty (Arr≃ (l1 false) l2 (l1 true)))
    where
      lem-supp : full ⊆ FVTy (unbiased-type (suc (ty-dim A)) (n-disk (ty-dim A)))
      lem-supp = begin
        full
          ≡˘⟨ supp-tree-bd-full (ty-dim A) (n-disk (ty-dim A)) false (≤-reflexive (tree-dim-n-disk (ty-dim A))) ⟩
        supp-tree-bd (ty-dim A) (n-disk (ty-dim A)) false
          ≡˘⟨ supp-unbiased-lem (ty-dim A) (n-disk (ty-dim A)) (≤-reflexive (sym (tree-dim-n-disk (ty-dim A)))) false ⟩
        FVTy (unbiased-type (ty-dim A) (n-disk (ty-dim A))) ∪
          FVTm
          (unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disk (ty-dim A)))
           [ tree-inc (ty-dim A) (n-disk (ty-dim A)) false ]tm)
          ≤⟨ ∪-⊆-1 _ _ ⟩
        FVTy (unbiased-type (ty-dim A) (n-disk (ty-dim A))) ∪
        FVTm (unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disk (ty-dim A)))
          [ tree-inc (ty-dim A) (n-disk (ty-dim A)) false ]tm) ∪
        FVTm (unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disk (ty-dim A)))
          [ tree-inc (ty-dim A) (n-disk (ty-dim A)) true ]tm) ∎
        where
          open PReasoning (⊆-poset _)

      instance _ = n-disk-is-linear (ty-dim A)
      l1 : (b : Bool) →
           (unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disk (ty-dim A)))
             [ tree-inc (ty-dim A) (n-disk (ty-dim A)) b ]tm
             [ sub-from-linear-tree (n-disk (ty-dim A)) t A (sym (tree-dim-n-disk (ty-dim A))) ]tm)
         ≃tm t
      l1 b = begin
        < unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disk (ty-dim A)))
           [ tree-inc (ty-dim A) (n-disk (ty-dim A)) b ]tm
           [ sub-from-linear-tree (n-disk (ty-dim A)) t A _ ]tm >tm
          ≈⟨ sub-action-≃-tm (sub-action-≃-tm (unbiased-term-≃ refl (tree-bd-full (ty-dim A) (n-disk (ty-dim A)) (≤-reflexive (tree-dim-n-disk (ty-dim A))))) (tree-inc-full (ty-dim A) (n-disk (ty-dim A)) b (≤-reflexive (tree-dim-n-disk (ty-dim A))))) refl≃s ⟩
        < unbiased-term (ty-dim A) (n-disk (ty-dim A))
          [ idSub ]tm
          [ sub-from-linear-tree (n-disk (ty-dim A)) t A (sym (tree-dim-n-disk (ty-dim A))) ]tm >tm
          ≈⟨ sub-action-≃-tm (id-on-tm (unbiased-term (ty-dim A) (n-disk (ty-dim A)))) refl≃s ⟩
        < unbiased-term (ty-dim A) (n-disk (ty-dim A))
          [ sub-from-linear-tree (n-disk (ty-dim A)) t A _ ]tm >tm
          ≈⟨ sub-action-≃-tm (unbiased-term-disk (ty-dim A)) refl≃s ⟩
        < 0V [ sub-from-linear-tree (n-disk (ty-dim A)) t A _ ]tm >tm
          ≈⟨ sub-from-linear-tree-0V (n-disk (ty-dim A)) t A (sym (tree-dim-n-disk (ty-dim A))) ⟩
        < t >tm ∎
        where
          open Reasoning tm-setoid

      l2 : unbiased-type (ty-dim A) (n-disk (ty-dim A))
           [ sub-from-linear-tree (n-disk (ty-dim A)) t A (sym (tree-dim-n-disk (ty-dim A))) ]ty
         ≃ty A
      l2 = begin
        < unbiased-type (ty-dim A) (n-disk (ty-dim A))
          [ sub-from-linear-tree (n-disk (ty-dim A)) t A _ ]ty >ty
          ≈⟨ sub-action-≃-ty (unbiased-type-disk (ty-dim A)) refl≃s ⟩
        < tree-to-ctx (n-disk (ty-dim A)) ‼ zero
          [ sub-from-linear-tree (n-disk (ty-dim A)) t A _ ]ty >ty
          ≈⟨ sub-from-linear-tree-‼-0 (n-disk (ty-dim A)) t A (sym (tree-dim-n-disk (ty-dim A))) ⟩
        < A >ty ∎
        where
          open Reasoning ty-setoid

sub-from-linear-tree-≈ : (S : Tree n) → .⦃ _ : is-linear S ⦄ → s ≈[ Γ ]tm t → (r : A ≈[ Γ ]ty B) → (p : ty-dim A ≡ tree-dim S) → sub-from-linear-tree S s A p ≈[ Γ ]s sub-from-linear-tree S t B (trans (sym (ty-dim-≈ r)) p)
sub-from-linear-tree-≈ Sing a Star≈ p = Ext≈ (Null≈ Star≈) a
sub-from-linear-tree-≈ (Join S Sing) a (Arr≈ b c d) p = Ext≈ (Ext≈ (sub-from-linear-tree-≈ S b c (max-pred-0 p)) d) a

identity-≈ : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → identity s A ≈[ Γ ]tm identity t B
identity-≈ {A = A} {B = B} p q = trans≈tm (reflexive≈tm (Coh≃ (tree-to-ctx-≃ (n-disk-≃ (ty-dim-≈ q))) (unbiased-type-≃ (cong suc (ty-dim-≈ q)) (n-disk-≃ (ty-dim-≈ q))) (sub-from-linear-tree-≃ (n-disk-≃ (ty-dim-≈ q)) ⦃ n-disk-is-linear (ty-dim A) ⦄ ⦃ n-disk-is-linear (ty-dim B) ⦄ refl≃tm refl≃ty (sym (tree-dim-n-disk (ty-dim A))) (trans (ty-dim-≈ q) (sym (tree-dim-n-disk (ty-dim B))))))) (Coh≈ refl≈ty (sub-from-linear-tree-≈ (n-disk (ty-dim B)) ⦃ n-disk-is-linear (ty-dim B) ⦄ p q (trans (ty-dim-≈ q) (sym (tree-dim-n-disk (ty-dim B))))))

sub-from-linear-tree-to-term-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {t : Tm m} → {A : Ty m} → (p : ty-dim A ≡ tree-dim S) → Typing-Sub (tree-to-ctx S) Γ (sub-from-linear-tree S t A p) → Typing-Tm Γ t A
sub-from-linear-tree-to-term-Ty Sing {A = ⋆} p (TyExt σty Bty tty) = tty
sub-from-linear-tree-to-term-Ty (Join S Sing) {A = s ─⟨ A ⟩⟶ t} p σty
  rewrite ≃c-to-≡ (susp-lin-tree S) with σty
... | TyExt τty Bty tty = term-conversion tty (reflexive≈ty (Arr≃ (sub-from-linear-tree-0V S s A (max-pred-0 p)) (trans≃ty (lift-sub-comp-lem-ty (sub-from-linear-tree S s A _) (tree-to-ctx S ‼ zero)) (sub-from-linear-tree-‼-0 S s A (max-pred-0 p))) refl≃tm))

sub-from-linear-tree-to-type-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {t : Tm m} → {A : Ty m} → (p : ty-dim A ≡ tree-dim S) → Typing-Sub (tree-to-ctx S) Γ (sub-from-linear-tree S t A p) → Typing-Ty Γ A
sub-from-linear-tree-to-type-Ty Sing {A = ⋆} p (TyExt σty Bty tty) = TyStar
sub-from-linear-tree-to-type-Ty (Join S Sing) {A = s ─⟨ A ⟩⟶ t} p σty
  rewrite ≃c-to-≡ (susp-lin-tree S) with σty
... | TyExt (TyExt τty Aty sty) Bty tty = TyArr (sub-from-linear-tree-to-term-Ty S (max-pred-0 p) τty) (sub-from-linear-tree-to-type-Ty S (max-pred-0 p) τty) (term-conversion sty (reflexive≈ty (sub-from-linear-tree-‼-0 S s A (max-pred-0 p))))

identity-to-term-Ty : Typing-Tm Γ (identity t A) B → Typing-Tm Γ t A
identity-to-term-Ty {A = A} (TyCoh Uty σty _ _ _) = sub-from-linear-tree-to-term-Ty (n-disk (ty-dim A)) ⦃ n-disk-is-linear (ty-dim A) ⦄ (sym (tree-dim-n-disk (ty-dim A))) σty

identity-to-type-Ty : Typing-Tm Γ (identity t A) B → Typing-Ty Γ A
identity-to-type-Ty {A = A} (TyCoh Uty σty _ _ _) = sub-from-linear-tree-to-type-Ty (n-disk (ty-dim A)) ⦃ n-disk-is-linear (ty-dim A) ⦄ (sym (tree-dim-n-disk (ty-dim A))) σty
