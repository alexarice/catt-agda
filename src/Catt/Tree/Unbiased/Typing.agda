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
open import Catt.Tree.Path
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Unbiased.Support
open import Catt.Tree.Support
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Boundary.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Suspension
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Globular
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing index rule
open import Catt.Tree.Label.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Relation.Binary.Definitions

unbiased-type-Ty : (d : ℕ) → (T : Tree n) → Typing-STy (incTree T) (unbiased-type d T)
unbiased-stm-Ty : (d : ℕ) → (T : Tree n) → (tree-dim T ≤ d) → Typing-STm (incTree T) (unbiased-stm d T) (unbiased-type d T)
unbiased-comp-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → (tree-dim T ≤ d) → Typing-STm (incTree T) (unbiased-comp d T) (unbiased-type d T)

unbiased-type-Ty zero T = TySStar
unbiased-type-Ty (suc d) T
  = TySArr (TySConv (extend-Ty (unbiased-stm-Ty d (tree-bd d T) (tree-dim-bd″ d T)) (tree-inc-Ty d T false) TySStar) (reflexive≈sty (sym≃sty (unbiased-type-prop d T d ≤-refl false))))
           (unbiased-type-Ty d T)
           (TySConv (extend-Ty (unbiased-stm-Ty d (tree-bd d T) (tree-dim-bd″ d T)) (tree-inc-Ty d T true) TySStar) (reflexive≈sty (sym≃sty (unbiased-type-prop d T d ≤-refl true))))

unbiased-stm-Ty zero Sing p = TySPath PHere
unbiased-stm-Ty zero (Join T₁ T₂) ()
unbiased-stm-Ty (suc d) Sing p = unbiased-comp-Ty (suc d) Sing p
unbiased-stm-Ty (suc d) (Join T Sing) p = TySConv (TySExt (unbiased-stm-Ty d T (≤-pred p))) (reflexive≈sty (trans≃sty (map-sty-pext-susp-compat (unbiased-type d T)) (unbiased-type-susp-lem d T)))
unbiased-stm-Ty (suc d) (Join T (Join T₁ T₂)) p = unbiased-comp-Ty (suc d) (Join T (Join T₁ T₂)) p

open Relation.Binary.Definitions.Tri
unbiased-comp-Ty d T p with <-cmp (tree-dim T) d
... | tri< a ¬b ¬c = TySConv (TySCoh T (unbiased-type-Ty d T) (id-label-Ty T) TySStar false (unbiased-supp-condition-2 d T a)) (reflexive≈sty (id-label-on-sty (unbiased-type d T)))
... | tri≈ ¬a b ¬c = TySConv (TySCoh T (unbiased-type-Ty d T) (id-label-Ty T) TySStar true (unbiased-supp-condition-1 d T b)) (reflexive≈sty (id-label-on-sty (unbiased-type d T)))
... | tri> ¬a ¬b c = ⊥-elim (<⇒≱ c p)

unbiased-comp′-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → (tree-dim T ≤ d) → Typing-STm (incTree T) (unbiased-comp′ d T) (unbiased-type d T)
unbiased-comp′-Ty d T p = transport-stm-typing (unbiased-comp-Ty d T p) (sym≃stm (unbiased-comp′-compat d T)) refl≃sty

label-from-linear-tree-unbiased-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → .⦃ NonZero (tree-dim S + d) ⦄ → tree-dim T ≤ tree-dim S + d → Typing-Label (incTree T) (label-from-linear-tree-unbiased S T d ,, unbiased-type d T)
label-from-linear-tree-unbiased-Ty Sing T d p = TySing (unbiased-comp′-Ty d ⦃ it ⦄ T p)
label-from-linear-tree-unbiased-Ty (Join S Sing) T d p
  = TyJoin (transport-stm-typing (extend-Ty (unbiased-stm-Ty d (tree-bd d T) (tree-dim-bd″ d T)) (tree-inc-Ty d T false) TySStar) refl≃stm (sym≃sty (unbiased-type-prop d T d ≤-refl false)))
           (label-from-linear-tree-unbiased-Ty S T (suc d) ⦃ NonZero-subst (sym (+-suc (tree-dim S) d)) it ⦄ (≤-trans p (≤-reflexive (sym (+-suc (tree-dim S) d)))))
           (TySing (transport-stm-typing (extend-Ty (unbiased-stm-Ty d (tree-bd d T) (tree-dim-bd″ d T)) (tree-inc-Ty d T true) TySStar) refl≃stm (sym≃sty (unbiased-type-prop d T d ≤-refl true))))

label-from-linear-tree-unbiased-Ty-0 : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → .⦃ NonZero (tree-dim S) ⦄ → tree-dim T ≤ tree-dim S → Typing-Label (incTree T) (label-from-linear-tree-unbiased S T 0 ,, S⋆)
label-from-linear-tree-unbiased-Ty-0 S T p = label-from-linear-tree-unbiased-Ty S T 0 ⦃ NonZero-subst (sym (+-identityʳ (tree-dim S))) it ⦄ (≤-trans p (≤-reflexive (sym (+-identityʳ (tree-dim S)))))

label-from-linear-tree-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {a : STm (COT-to-MT ΓS)} → {As : STy (COT-to-MT ΓS)} → Typing-STm ΓS a As → Typing-STy ΓS As → .(p : tree-dim S ≤ sty-dim As) → Typing-Label ΓS (label-from-linear-tree S a As p ,, label-from-linear-tree-type S As)
label-from-linear-tree-type-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {As : STy (COT-to-MT ΓS)} → Typing-STy ΓS As → Typing-STy ΓS (label-from-linear-tree-type S As)

label-from-linear-tree-Ty Sing aTy AsTy p = TySing aTy
label-from-linear-tree-Ty (Join S Sing) aTy AsTy p = transport-label-typing (unrestrict-label-Ty (label-from-linear-tree-Ty S aTy AsTy (≤-trans (n≤1+n (tree-dim S)) p)) (label-from-linear-tree-type-Ty S AsTy) ⦃ label-from-linear-tree-nz S _ p ⦄) refl≃l (sym≃sty (label-from-linear-tree-type-prop S _))

label-from-linear-tree-type-Ty Sing AsTy = AsTy
label-from-linear-tree-type-Ty (Join S Sing) AsTy = label-from-linear-tree-type-Ty S (TySArr-proj₂ AsTy)

label-from-linear-tree-type-≈ : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (As ≈[ ΓS ]sty Bs) → label-from-linear-tree-type S As ≈[ ΓS ]sty label-from-linear-tree-type S Bs
label-from-linear-tree-type-≈ Sing p = p
label-from-linear-tree-type-≈ (Join S Sing) p = label-from-linear-tree-type-≈ S (sty-base-≈ p)

label-from-linear-tree-≈ : {ΓS : CtxOrTree m}
                         → (S : Tree n) → .⦃ _ : is-linear S ⦄
                         → {a b : STm (COT-to-MT ΓS)} → (a ≈[ ΓS ]stm b)
                         → {As Bs : STy (COT-to-MT ΓS)} → (q : As ≈[ ΓS ]sty Bs)
                         → .(r : tree-dim S ≤ sty-dim As)
                         → label-from-linear-tree S a As r ≈[ ΓS ]l label-from-linear-tree S b Bs (≤-trans r (≤-reflexive (sty-dim-≈ q)))
label-from-linear-tree-≈ Sing p q r .get P = p
label-from-linear-tree-≈ (Join S Sing) p q r .get PHere = sty-src-≈ (label-from-linear-tree-type-≈ S q) ⦃ _ ⦄
label-from-linear-tree-≈ (Join S Sing) p q r .get (PExt P) = label-from-linear-tree-≈ S p q _ .get P
label-from-linear-tree-≈ (Join S Sing) p q r .get (PShift PHere) = sty-tgt-≈ (label-from-linear-tree-type-≈ S q) ⦃ _ ⦄

{-
unbiased-type-Ty : (d : ℕ) → (T : Tree n) → (d ≤ suc (tree-dim T)) → Typing-Ty (tree-to-ctx T) (unbiased-type d T)
unbiased-term-Ty : (d : ℕ) → (T : Tree n) → (tree-dim T ≡ d) → Typing-Tm (tree-to-ctx T) (unbiased-term d T) (unbiased-type d T)
unbiased-comp-Ty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → (tree-dim T ≡ d)
                  → Typing-Tm (tree-to-ctx T) (unbiased-comp d T) (unbiased-type d T)

unbiased-type-Ty zero T q = TyStar
unbiased-type-Ty (suc d) T q =
  TyArr (TyConv (apply-sub-tm-typing utty (tree-inc-Ty d T false)) (reflexive≈ty (sym≃ty (unbiased-type-prop d T d ≤-refl false))))
        (unbiased-type-Ty d T (≤-trans (n≤1+n d) q))
        (TyConv (apply-sub-tm-typing utty (tree-inc-Ty d T true)) (reflexive≈ty (sym≃ty (unbiased-type-prop d T d ≤-refl true))))
  where
    utty = unbiased-term-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-pred q))

unbiased-term-Ty d T q with is-linear-dec T
... | no p = unbiased-comp-Ty d ⦃ NonZero-subst q (non-linear-has-no-zero-dim T p) ⦄ T q
  where
    non-linear-has-no-zero-dim : (T : Tree n) → ¬ is-linear T → NonZero (tree-dim T)
    non-linear-has-no-zero-dim Sing p = ⊥-elim (p tt)
    non-linear-has-no-zero-dim (Join S T) p = it

... | yes p with tree-to-ctx T | tree-to-ctx-Ty T | linear-tree-unbiased-lem d T ⦃ p ⦄ q
... | Γ , A | TyAdd Γty x | l = TyConv (TyVar zero) (reflexive≈ty l)

unbiased-comp-Ty (suc d) T q = TyConv (TyCoh ⦃ tree-to-pd T ⦄ (unbiased-type-Ty (suc d) T (s≤s (≤-trans (n≤1+n d) (≤-reflexive (sym q))))) id-Ty true (unbiased-supp-condition d T q)) (reflexive≈ty (id-on-ty _))

sub-from-linear-tree-unbiased-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → .⦃ NonZero (tree-dim T) ⦄ → (d : ℕ) → (tree-dim T ≡ tree-dim S + d) → Typing-Sub (tree-to-ctx S) (tree-to-ctx T) (sub-from-linear-tree-unbiased S T d)
sub-from-linear-tree-unbiased-Ty Sing T d p = TyExt (TyNull (unbiased-type-Ty d T (≤-trans (≤-reflexive (sym p)) (n≤1+n (tree-dim T))))) (unbiased-comp-Ty d ⦃ NonZero-subst p it ⦄ T p)
sub-from-linear-tree-unbiased-Ty (Join S Sing) T d p = unrestrictTy (sub-from-linear-tree-unbiased-Ty S T (suc d) (trans p (sym (+-suc (tree-dim S) d))))

sub-from-linear-tree-unbiased-Ty-0 : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → .⦃ NonZero (tree-dim T) ⦄ → .(tree-dim T ≡ tree-dim S) → Typing-Sub (tree-to-ctx S) (tree-to-ctx T) (sub-from-linear-tree-unbiased S T 0)
sub-from-linear-tree-unbiased-Ty-0 S T p = sub-from-linear-tree-unbiased-Ty S T 0 (trans (recompute ((tree-dim T) ≟ (tree-dim S)) p) (sym (+-identityʳ (tree-dim S))))

sub-from-linear-tree-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → Typing-Tm Γ t A → Typing-Ty Γ A → (p : ty-dim A ≡ tree-dim S) → Typing-Sub (tree-to-ctx S) Γ (sub-from-linear-tree S t A p)
sub-from-linear-tree-Ty Sing tty TyStar p = TyExt (TyNull TyStar) tty
sub-from-linear-tree-Ty (Join S Sing) tty (TyArr sty Aty sty′) p
  rewrite (≃c-to-≡ (susp-lin-tree S)) =
    TyExt (TyExt (sub-from-linear-tree-Ty S sty Aty (cong pred p))
                 (TyConv sty′ (reflexive≈ty (sym≃ty (sub-from-linear-tree-‼-0 S _ _ (cong pred p))))))
          (TyConv tty (reflexive≈ty (sym≃ty (Arr≃ (sub-from-linear-tree-0V S _ _ (cong pred p))
                                                           (trans≃ty (lift-sub-comp-lem-ty (sub-from-linear-tree S _ _ _) (tree-to-ctx S ‼ zero)) (sub-from-linear-tree-‼-0 S _ _ (cong pred p)))
                                                           refl≃tm))))

identity-tree-Ty : Typing-Tm Γ t A → Typing-Ty Γ A → Typing-Tm Γ (identity-tree t A) (t ─⟨ A ⟩⟶ t)
identity-tree-Ty {t = t} {A = A} tty Aty
  = TyConv (TyCoh ⦃ tree-to-pd (n-disc (ty-dim A)) ⦄
          (unbiased-type-Ty (suc (ty-dim A))
                            (n-disc (ty-dim A))
                            (s≤s (≤-reflexive (sym (tree-dim-n-disc (ty-dim A))))))
          (sub-from-linear-tree-Ty (n-disc (ty-dim A)) ⦃ n-disc-is-linear (ty-dim A) ⦄
                                   tty
                                   Aty
                                   (sym (tree-dim-n-disc (ty-dim A))))
          false
          (full-⊆ lem-supp))
          (reflexive≈ty (Arr≃ (l1 false) l2 (l1 true)))
    where
      lem-supp : full ⊆ FVTy (unbiased-type (suc (ty-dim A)) (n-disc (ty-dim A)))
      lem-supp = begin
        full
          ≡˘⟨ supp-tree-bd-full (ty-dim A) (n-disc (ty-dim A)) false (≤-reflexive (tree-dim-n-disc (ty-dim A))) ⟩
        supp-tree-bd (ty-dim A) (n-disc (ty-dim A)) false
          ≡˘⟨ supp-unbiased-lem (ty-dim A) (n-disc (ty-dim A)) (≤-reflexive (sym (tree-dim-n-disc (ty-dim A)))) false ⟩
        FVTy (unbiased-type (ty-dim A) (n-disc (ty-dim A))) ∪
          FVTm
          (unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disc (ty-dim A)))
           [ tree-inc (ty-dim A) (n-disc (ty-dim A)) false ]tm)
          ≤⟨ ∪-⊆-1 _ _ ⟩
        FVTy (unbiased-type (ty-dim A) (n-disc (ty-dim A))) ∪
        FVTm (unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disc (ty-dim A)))
          [ tree-inc (ty-dim A) (n-disc (ty-dim A)) false ]tm) ∪
        FVTm (unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disc (ty-dim A)))
          [ tree-inc (ty-dim A) (n-disc (ty-dim A)) true ]tm) ∎
        where
          open PReasoning (⊆-poset _)

      instance _ = n-disc-is-linear (ty-dim A)
      l1 : (b : Bool) →
           (unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disc (ty-dim A)))
             [ tree-inc (ty-dim A) (n-disc (ty-dim A)) b ]tm
             [ sub-from-linear-tree (n-disc (ty-dim A)) t A (sym (tree-dim-n-disc (ty-dim A))) ]tm)
         ≃tm t
      l1 b = begin
        < unbiased-term (ty-dim A) (tree-bd (ty-dim A) (n-disc (ty-dim A)))
           [ tree-inc (ty-dim A) (n-disc (ty-dim A)) b ]tm
           [ sub-from-linear-tree (n-disc (ty-dim A)) t A _ ]tm >tm
          ≈⟨ sub-action-≃-tm (sub-action-≃-tm (unbiased-term-≃ refl (tree-bd-full (ty-dim A) (n-disc (ty-dim A)) (≤-reflexive (tree-dim-n-disc (ty-dim A))))) (tree-inc-full (ty-dim A) (n-disc (ty-dim A)) b (≤-reflexive (tree-dim-n-disc (ty-dim A))))) refl≃s ⟩
        < unbiased-term (ty-dim A) (n-disc (ty-dim A))
          [ idSub ]tm
          [ sub-from-linear-tree (n-disc (ty-dim A)) t A (sym (tree-dim-n-disc (ty-dim A))) ]tm >tm
          ≈⟨ sub-action-≃-tm (id-on-tm (unbiased-term (ty-dim A) (n-disc (ty-dim A)))) refl≃s ⟩
        < unbiased-term (ty-dim A) (n-disc (ty-dim A))
          [ sub-from-linear-tree (n-disc (ty-dim A)) t A _ ]tm >tm
          ≈⟨ sub-action-≃-tm (unbiased-term-disc (ty-dim A)) refl≃s ⟩
        < 0V [ sub-from-linear-tree (n-disc (ty-dim A)) t A _ ]tm >tm
          ≈⟨ sub-from-linear-tree-0V (n-disc (ty-dim A)) t A (sym (tree-dim-n-disc (ty-dim A))) ⟩
        < t >tm ∎
        where
          open Reasoning tm-setoid

      l2 : unbiased-type (ty-dim A) (n-disc (ty-dim A))
           [ sub-from-linear-tree (n-disc (ty-dim A)) t A (sym (tree-dim-n-disc (ty-dim A))) ]ty
         ≃ty A
      l2 = begin
        < unbiased-type (ty-dim A) (n-disc (ty-dim A))
          [ sub-from-linear-tree (n-disc (ty-dim A)) t A _ ]ty >ty
          ≈⟨ sub-action-≃-ty (unbiased-type-disc (ty-dim A)) refl≃s ⟩
        < tree-to-ctx (n-disc (ty-dim A)) ‼ zero
          [ sub-from-linear-tree (n-disc (ty-dim A)) t A _ ]ty >ty
          ≈⟨ sub-from-linear-tree-‼-0 (n-disc (ty-dim A)) t A (sym (tree-dim-n-disc (ty-dim A))) ⟩
        < A >ty ∎
        where
          open Reasoning ty-setoid

sub-from-linear-tree-≈ : (S : Tree n) → .⦃ _ : is-linear S ⦄ → s ≈[ Γ ]tm t → (r : A ≈[ Γ ]ty B) → (p : ty-dim A ≡ tree-dim S) → sub-from-linear-tree S s A p ≈[ Γ ]s sub-from-linear-tree S t B (trans (sym (ty-dim-≈ r)) p)
sub-from-linear-tree-≈ Sing a Star≈ p = Ext≈ (Null≈ Star≈) a
sub-from-linear-tree-≈ (Join S Sing) a (Arr≈ b c d) p = Ext≈ (Ext≈ (sub-from-linear-tree-≈ S b c (cong pred p)) d) a

identity-tree-≈ : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → identity-tree s A ≈[ Γ ]tm identity-tree t B
identity-tree-≈ {A = A} {B = B} p q = trans≈tm (reflexive≈tm (Coh≃ (tree-to-ctx-≃ (n-disc-≃ (ty-dim-≈ q))) (unbiased-type-≃ (cong suc (ty-dim-≈ q)) (n-disc-≃ (ty-dim-≈ q))) (sub-from-linear-tree-≃ (n-disc-≃ (ty-dim-≈ q)) ⦃ n-disc-is-linear (ty-dim A) ⦄ ⦃ n-disc-is-linear (ty-dim B) ⦄ refl≃tm refl≃ty (sym (tree-dim-n-disc (ty-dim A))) (trans (ty-dim-≈ q) (sym (tree-dim-n-disc (ty-dim B))))))) (Coh≈ refl≈ty (sub-from-linear-tree-≈ (n-disc (ty-dim B)) ⦃ n-disc-is-linear (ty-dim B) ⦄ p q (trans (ty-dim-≈ q) (sym (tree-dim-n-disc (ty-dim B))))))

sub-from-linear-tree-to-term-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {t : Tm m} → {A : Ty m} → (p : ty-dim A ≡ tree-dim S) → Typing-Sub (tree-to-ctx S) Γ (sub-from-linear-tree S t A p) → Typing-Tm Γ t A
sub-from-linear-tree-to-term-Ty Sing {A = ⋆} p (TyExt σty tty) = tty
sub-from-linear-tree-to-term-Ty (Join S Sing) {A = s ─⟨ A ⟩⟶ t} p σty
  rewrite ≃c-to-≡ (susp-lin-tree S) with σty
... | TyExt τty tty = TyConv tty (reflexive≈ty (Arr≃ (sub-from-linear-tree-0V S s A (cong pred p)) (trans≃ty (lift-sub-comp-lem-ty (sub-from-linear-tree S s A _) (tree-to-ctx S ‼ zero)) (sub-from-linear-tree-‼-0 S s A (cong pred p))) refl≃tm))

sub-from-linear-tree-to-type-Ty : (S : Tree n) → .⦃ _ : is-linear S ⦄ → {t : Tm m} → {A : Ty m} → (p : ty-dim A ≡ tree-dim S) → Typing-Sub (tree-to-ctx S) Γ (sub-from-linear-tree S t A p) → Typing-Ty Γ A
sub-from-linear-tree-to-type-Ty Sing {A = ⋆} p (TyExt σty tty) = TyStar
sub-from-linear-tree-to-type-Ty (Join S Sing) {A = s ─⟨ A ⟩⟶ t} p σty
  rewrite ≃c-to-≡ (susp-lin-tree S) with σty
... | TyExt (TyExt τty sty) tty = TyArr (sub-from-linear-tree-to-term-Ty S (cong pred p) τty) (sub-from-linear-tree-to-type-Ty S (cong pred p) τty) (TyConv sty (reflexive≈ty (sub-from-linear-tree-‼-0 S s A (cong pred p))))

identity-tree-to-term-Ty : Typing-Tm Γ (identity-tree t A) B → Typing-Tm Γ t A
identity-tree-to-term-Ty (TyConv tty p) = identity-tree-to-term-Ty tty
identity-tree-to-term-Ty {A = A} (TyCoh Uty σty _ _) = sub-from-linear-tree-to-term-Ty (n-disc (ty-dim A)) ⦃ n-disc-is-linear (ty-dim A) ⦄ (sym (tree-dim-n-disc (ty-dim A))) σty

identity-tree-to-type-Ty : Typing-Tm Γ (identity-tree t A) B → Typing-Ty Γ A
identity-tree-to-type-Ty (TyConv tty p) = identity-tree-to-type-Ty tty
identity-tree-to-type-Ty {A = A} (TyCoh Uty σty _ _) = sub-from-linear-tree-to-type-Ty (n-disc (ty-dim A)) ⦃ n-disc-is-linear (ty-dim A) ⦄ (sym (tree-dim-n-disc (ty-dim A))) σty

unbiased-comp-lemma : (d : ℕ) → (T : Tree n) → Typing-Tm Γ (unbiased-comp d T) A → NonZero d
unbiased-comp-lemma zero T (TyConv tty x) = unbiased-comp-lemma zero T tty
unbiased-comp-lemma zero T (TyCoh x x₁ false ())
unbiased-comp-lemma zero T (TyCoh x x₁ true ())
unbiased-comp-lemma (suc d) T tty = it
-}
