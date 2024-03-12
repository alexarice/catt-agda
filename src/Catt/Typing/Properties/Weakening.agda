open import Catt.Typing.Rule

module Catt.Typing.Properties.Weakening (ops : Op)
                                        (rules : RuleSet)
                                        (wk-cond : WkCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules

open Rule

wk-ty-typing : Typing-Ty Γ A → Typing-Ty (Γ , B) (wk-ty A)
wk-tm-typing : Typing-Tm Γ t A → Typing-Tm (Γ , B) (wk-tm t) (wk-ty A)
wk-sub-typing : Typing-Sub Γ Δ σ → Typing-Sub Γ (Δ , B) (wk-sub σ)

wk-ty-equality : B ≈[ Γ ]ty C → (wk-ty B) ≈[ Γ , A ]ty (wk-ty C)
wk-tm-equality : s ≈[ Γ ]tm t → (wk-tm s) ≈[ Γ , A ]tm (wk-tm t)
wk-sub-equality : σ ≈[ Γ ]s τ → (wk-sub σ) ≈[ Γ , A ]s (wk-sub τ)

wk-ty-typing TyStar = TyStar
wk-ty-typing (TyArr p q r) = TyArr (wk-tm-typing p) (wk-ty-typing q) (wk-tm-typing r)

wk-tm-typing (TyConv tty p) = TyConv (wk-tm-typing tty) (wk-ty-equality p)
wk-tm-typing (TyVar i) = TyVar (suc i)
wk-tm-typing (TyCoh {A = A} supp Aty σty) = TyConv (TyCoh supp Aty (wk-sub-typing σty)) (reflexive≈ty (apply-wk-sub-ty-≃ A _))

wk-sub-typing (TyNull x) = TyNull (wk-ty-typing x)
wk-sub-typing (TyExt {A = A} p r) = TyExt (wk-sub-typing p) (TyConv (wk-tm-typing r) (reflexive≈ty (sym≃ty (apply-wk-sub-ty-≃ A _))))

wk-ty-equality Star≈ = Star≈
wk-ty-equality (Arr≈ q r s) = Arr≈ (wk-tm-equality q) (wk-ty-equality r) (wk-tm-equality s)

wk-tm-equality (Var≈ x) = Var≈ (cong suc x)
wk-tm-equality (Sym≈ eq) = Sym≈ (wk-tm-equality eq)
wk-tm-equality (Trans≈ eq eq′) = Trans≈ (wk-tm-equality eq) (wk-tm-equality eq′)

wk-tm-equality (Coh≈ r s) = Coh≈ r (wk-sub-equality s)
wk-tm-equality {A = A} (Rule≈ r p tc) = Rule≈ (wk-rule r A)
                                                (wk-cond A p)
                                                (wk-tm-typing tc)

wk-sub-equality (Null≈ x) = Null≈ (wk-ty-equality x)
wk-sub-equality (Ext≈ eq x) = Ext≈ (wk-sub-equality eq) (wk-tm-equality x)

id-Ty : Typing-Sub Γ Γ idSub
id-Ty {Γ = ∅} = TyNull TyStar
id-Ty {Γ = Γ , A} = TyExt (wk-sub-typing id-Ty) (TyConv (TyVar zero) (reflexive≈ty (sym≃ty (trans≃ty (apply-wk-sub-ty-≃ A idSub) (wk-ty-≃ (id-on-ty A))))))

project-Ty : Typing-Sub Γ (Γ , A) project
project-Ty = wk-sub-typing id-Ty

idSub≃-Ty : (p : Γ ≃c Δ) → Typing-Sub Γ Δ (idSub≃ p)
idSub≃-Ty Emp≃ = TyNull TyStar
idSub≃-Ty (Add≃ {A = A} {A′ = A′} p x) = TyExt (wk-sub-typing (idSub≃-Ty p)) (TyConv (TyVar zero) (reflexive≈ty (sym≃ty (trans≃ty (apply-wk-sub-ty-≃ A (idSub≃ p)) (wk-ty-≃ (trans≃ty (idSub≃-on-ty p A) x))))))
  where
    open Reasoning ty-setoid

    lem : wk-ty A′ ≃ty (A [ wk-sub (idSub≃ p) ]ty)
    lem = begin
      < wk-ty A′ >ty ≈˘⟨ wk-ty-≃ x ⟩
      < wk-ty A >ty ≈˘⟨ wk-ty-≃ (idSub≃-on-ty p A) ⟩
      < wk-ty (A [ idSub≃ p ]ty) >ty ≈˘⟨ apply-wk-sub-ty-≃ A (idSub≃ p) ⟩
      < A [ wk-sub (idSub≃ p) ]ty >ty ∎

‼-Ty : Typing-Ctx Γ → (i : Fin n) → Typing-Ty Γ (Γ ‼ i)
‼-Ty (TyAdd Γty Aty) zero = wk-ty-typing Aty
‼-Ty (TyAdd Γty Aty) (suc i) = wk-ty-typing (‼-Ty Γty i)
