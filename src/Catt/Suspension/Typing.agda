open import Catt.Typing.Rule

module Catt.Suspension.Typing (ops : Op)
                              (susp-op : SuspOp ops)
                              (rules : RuleSet)
                              (lift-cond : LiftCond rules)
                              (susp-cond : SuspCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Support
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Pasting
open import Catt.Suspension.Support

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Lifting ops rules lift-cond


susp-ctxTy : Typing-Ctx Γ → Typing-Ctx (susp-ctx Γ)
susp-tyTy : Typing-Ty Γ A → Typing-Ty (susp-ctx Γ) (susp-ty A)
susp-tmTy : Typing-Tm Γ t A → Typing-Tm (susp-ctx Γ) (susp-tm t) (susp-ty A)
susp-subTy : Typing-Sub Γ Δ σ → Typing-Sub (susp-ctx Γ) (susp-ctx Δ) (susp-sub σ)
get-fstTy : {Γ : Ctx n} → Typing-Tm (susp-ctx Γ) (get-fst) ⋆
get-sndTy : {Γ : Ctx n} → Typing-Tm (susp-ctx Γ) (get-snd) ⋆

susp-tyEq : A ≈[ Γ ]ty B → susp-ty A ≈[ susp-ctx Γ ]ty susp-ty B
susp-tmEq : s ≈[ Γ ]tm t → susp-tm s ≈[ susp-ctx Γ ]tm susp-tm t
susp-subEq : σ ≈[ Γ ]s τ → susp-sub σ ≈[ susp-ctx Γ ]s susp-sub τ

susp-ctxTy TyEmp = TyAdd (TyAdd TyEmp TyStar) TyStar
susp-ctxTy (TyAdd ty x) = TyAdd (susp-ctxTy ty) (susp-tyTy x)

susp-tyTy TyStar = TyArr get-fstTy TyStar get-sndTy
susp-tyTy (TyArr p q r) = TyArr (susp-tmTy p) (susp-tyTy q) (susp-tmTy r)

susp-tmTy (TyConv tty p) = TyConv (susp-tmTy tty) (susp-tyEq p)
susp-tmTy {Γ = Γ} (TyVar i) = TyConv (TyVar (inject₁ (inject₁ i))) (reflexive≈ty (susp-‼ Γ i))
susp-tmTy (TyCoh {Δ = Δ} {A = A@(s ─⟨ _ ⟩⟶ t)} supp Aty σty) = let
  instance .x : susp-ctx Δ ⊢pd
  x = susp-pd it
  in TyConv (TyCoh ⦃ nz = NonZero-subst (sym (susp-dim A)) it ⦄
                   (subst₂ (ops (susp-ctx Δ)) (sym (suspSuppTm′ Δ s))
                                              (sym (suspSuppTm′ Δ t))
                                              (susp-op _ _ _ supp))
                   (susp-tyTy Aty)
                   (susp-subTy σty))
            (reflexive≈ty (sym≃ty (susp-functorial-ty _ A)))

susp-subTy (TyNull x) = TyExt (TyExt (TyNull TyStar) get-fstTy) get-sndTy
susp-subTy (TyExt p r) = TyExt (susp-subTy p) (TyConv (susp-tmTy r) (reflexive≈ty (susp-functorial-ty _ _)))

get-fstTy {Γ = ∅} = TyVar (suc zero)
get-fstTy {Γ = Γ , A} = lift-tm-typing get-fstTy

get-sndTy {Γ = ∅} = TyVar zero
get-sndTy {Γ = Γ , A} = lift-tm-typing get-sndTy

susp-tyEq Star≈ = refl≈ty
susp-tyEq (Arr≈ q r s) = Arr≈ (susp-tmEq q) (susp-tyEq r) (susp-tmEq s)
susp-tmEq (Var≈ x) = Var≈ (begin
  toℕ (inject₁ (inject₁ _)) ≡⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ _) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ _ ≡⟨ x ⟩
  toℕ _ ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ _) ≡˘⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ (inject₁ _)) ∎)
  where
    open ≡-Reasoning

susp-tmEq (Sym≈ eq) = Sym≈ (susp-tmEq eq)
susp-tmEq (Trans≈ eq eq′) = Trans≈ (susp-tmEq eq) (susp-tmEq eq′)
susp-tmEq (Coh≈ q r) = Coh≈ (susp-tyEq q) (susp-subEq r)
susp-tmEq (Rule≈ r p tc) = Rule≈ (susp-rule r) (susp-cond p) (susp-tmTy tc)

susp-subEq (Null≈ x) = refl≈s
susp-subEq (Ext≈ p x) = Ext≈ (susp-subEq p) (susp-tmEq x)

↓-Ty : Typing-Sub Γ Δ σ → Typing-Sub (susp-ctx Γ) Δ (↓ σ)
↓-Ty (TyNull (TyArr p q r)) = TyExt (TyExt (TyNull q) p) r
↓-Ty (TyExt σty x) = TyExt (↓-Ty σty) (TyConv x (reflexive≈ty (sym≃ty (↓-comp-ty _ _))))

↑-Ty : {σ : Sub (2 + n) m A}
     → Typing-Sub (susp-ctx Γ) Δ σ
     → Typing-Sub Γ Δ (↑ σ)
↑-Ty {Γ = ∅} (TyExt (TyExt (TyNull z) y) x) = TyNull (TyArr y z x)
↑-Ty {Γ = ∅ , A} (TyExt (TyExt (TyExt σty z) y) x)
  = TyExt (↑-Ty (TyExt (TyExt σty z) y))
          (TyConv x (reflexive≈ty (trans≃ty (sub-action-≃-ty (refl≃ty {A = susp-ty A}) (sym≃s (↓-↑-≃ ⟨ ⟨ _ , _ ⟩ , _ ⟩)))
                                            (↓-comp-ty A (↑ ⟨ ⟨ _ , _ ⟩ , _ ⟩)))))
↑-Ty {Γ = ∅ , B , A} (TyExt (TyExt (TyExt σty z) y) x)
  = TyExt (↑-Ty (TyExt (TyExt σty z) y))
          (TyConv x (reflexive≈ty (trans≃ty (sub-action-≃-ty (refl≃ty {A = susp-ty A}) (sym≃s (↓-↑-≃ ⟨ ⟨ _ , _ ⟩ , _ ⟩)))
                                            (↓-comp-ty A (↑ ⟨ ⟨ _ , _ ⟩ , _ ⟩)))))
↑-Ty {Γ = Γ , C , B , A} (TyExt (TyExt (TyExt σty z) y) x)
  = TyExt (↑-Ty (TyExt (TyExt σty z) y))
          (TyConv x (reflexive≈ty (trans≃ty (sub-action-≃-ty (refl≃ty {A = susp-ty A}) (sym≃s (↓-↑-≃ ⟨ ⟨ _ , _ ⟩ , _ ⟩)))
                                            (↓-comp-ty A (↑ ⟨ ⟨ _ , _ ⟩ , _ ⟩)))))
