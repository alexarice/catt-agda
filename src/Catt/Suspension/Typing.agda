open import Catt.Typing.Rule

module Catt.Suspension.Typing (rules : RuleSet)
                              (lift-cond : LiftCond rules)
                              (susp-cond : SuspCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Pasting

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules
open import Catt.Typing.Properties.Lifting rules lift-cond


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
susp-tmTy (TyCoh Aty σty) = TyConv (TyCoh ⦃ susp-pd it ⦄ (susp-tyTy Aty) (susp-subTy σty)) (reflexive≈ty (sym≃ty (susp-functorial-ty _ _)))

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

unrestrictTy : Typing-Sub Γ Δ σ → Typing-Sub (susp-ctx Γ) Δ (unrestrict σ)
unrestrictTy (TyNull (TyArr p q r)) = TyExt (TyExt (TyNull q) p) r
unrestrictTy (TyExt σty x) = TyExt (unrestrictTy σty) (TyConv x (reflexive≈ty (sym≃ty (unrestrict-comp-ty _ _))))
