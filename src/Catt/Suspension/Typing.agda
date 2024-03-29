open import Catt.Typing.Rule

module Catt.Suspension.Typing (ops : Op)
                              (susp-op : SuspOp ops)
                              (rules : RuleSet)
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

open import Catt.Typing.Weak ops
open import Catt.Typing.Rule.Properties ops

get-fstTy : {Γ : Ctx n} → Typing-Tm (susp-ctx Γ) (get-fst) ⋆
get-fstTy {Γ = Γ} = TyConv (TyVar (fromℕ _)) (reflexive≈ty (susp-‼-get-fst Γ))

get-sndTy : {Γ : Ctx n} → Typing-Tm (susp-ctx Γ) (get-snd) ⋆
get-sndTy {Γ = Γ} = TyConv (TyVar (inject₁ (fromℕ _))) (reflexive≈ty (susp-‼-get-snd Γ))

susp-ctxTy : Typing-Ctx Γ → Typing-Ctx (susp-ctx Γ)
susp-tyTy : Typing-Ty Γ A → Typing-Ty (susp-ctx Γ) (susp-ty A)
susp-tmTy : Typing-Tm Γ t A → Typing-Tm (susp-ctx Γ) (susp-tm t) (susp-ty A)
susp-sub-↑Ty : Typing-Sub Γ Δ σ → Typing-Sub Γ (susp-ctx Δ) (susp-sub-↑ σ)
susp-subTy : Typing-Sub Γ Δ σ → Typing-Sub (susp-ctx Γ) (susp-ctx Δ) (susp-sub σ)

susp-tyEq : A ≈[ Γ ]ty B → susp-ty A ≈[ susp-ctx Γ ]ty susp-ty B
susp-tmEq : s ≈[ Γ ]tm t → susp-tm s ≈[ susp-ctx Γ ]tm susp-tm t
susp-sub-↑Eq : σ ≈[ Γ ]s τ → susp-sub-↑ σ ≈[ susp-ctx Γ ]s susp-sub-↑ τ
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
                   (subst₂ (ops (susp-ctx Δ)) (sym (susp-SuppTm Δ s))
                                              (sym (susp-SuppTm Δ t))
                                              (susp-op _ _ _ supp))
                   (susp-tyTy Aty)
                   (susp-subTy σty))
            (reflexive≈ty (sym≃ty (susp-functorial-ty _ A)))

susp-sub-↑Ty (TyNull x) = TyNull (susp-tyTy x)
susp-sub-↑Ty (TyExt {A = A} σty x)
  = TyExt (susp-sub-↑Ty σty) (TyConv (susp-tmTy x) (reflexive≈ty (susp-↑-comp-ty A _)))

susp-subTy σty = ↓-Ty (susp-sub-↑Ty σty)

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

susp-sub-↑Eq (Null≈ x) = Null≈ (susp-tyEq x)
susp-sub-↑Eq (Ext≈ σty x) = Ext≈ (susp-sub-↑Eq σty) (susp-tmEq x)

susp-subEq p = ↓-≈ (susp-sub-↑Eq p)
