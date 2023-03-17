open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Typing.Properties.Lifting {index : Set}
                                      (rule : index → Rule)
                                      (lift-rule : ∀ i → P.LiftRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open P rule
open import Catt.Prelude.Properties

lift-ty-typing : Typing-Ty Γ A → Typing-Ty (Γ , B) (lift-ty A)
lift-tm-typing : Typing-Tm Γ t A → Typing-Tm (Γ , B) (lift-tm t) (lift-ty A)
lift-sub-typing : Typing-Sub Γ Δ σ → Typing-Sub Γ (Δ , B) (lift-sub σ)

lift-ty-equality : B ≈[ Γ ]ty C → (lift-ty B) ≈[ Γ , A ]ty (lift-ty C)
lift-tm-equality : s ≈[ Γ ]tm t → (lift-tm s) ≈[ Γ , A ]tm (lift-tm t)
lift-sub-equality : σ ≈[ Γ ]s τ → (lift-sub σ) ≈[ Γ , A ]s (lift-sub τ)

lift-ty-typing TyStar = TyStar
lift-ty-typing (TyArr p q r) = TyArr (lift-tm-typing p) (lift-ty-typing q) (lift-tm-typing r)

lift-tm-typing (TyConv tty p) = TyConv (lift-tm-typing tty) (lift-ty-equality p)
lift-tm-typing (TyVar i) = TyVar (suc i)
lift-tm-typing (TyCoh {A = A} Aty σty b sc) = TyConv (TyCoh Aty (lift-sub-typing σty) b sc) (reflexive≈ty (apply-lifted-sub-ty-≃ A _))

lift-sub-typing (TyNull x) = TyNull (lift-ty-typing x)
lift-sub-typing (TyExt {A = A} p r) = TyExt (lift-sub-typing p) (TyConv (lift-tm-typing r) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ A _))))

lift-ty-equality Star≈ = Star≈
lift-ty-equality (Arr≈ q r s) = Arr≈ (lift-tm-equality q) (lift-ty-equality r) (lift-tm-equality s)

lift-tm-equality (Var≈ x) = Var≈ (cong suc x)
lift-tm-equality (Sym≈ eq) = Sym≈ (lift-tm-equality eq)
lift-tm-equality (Trans≈ eq eq′) = Trans≈ (lift-tm-equality eq) (lift-tm-equality eq′)

lift-tm-equality (Coh≈ r s) = Coh≈ r (lift-sub-equality s)
lift-tm-equality {A = A} (Rule≈ i tc) = lift-rule i (lift-tm-typing tc)

lift-sub-equality (Null≈ x) = Null≈ (lift-ty-equality x)
lift-sub-equality (Ext≈ eq x) = Ext≈ (lift-sub-equality eq) (lift-tm-equality x)

id-Ty : Typing-Sub Γ Γ idSub
id-Ty {Γ = ∅} = TyNull TyStar
id-Ty {Γ = Γ , A} = TyExt (lift-sub-typing id-Ty) (TyConv (TyVar zero) (reflexive≈ty (sym≃ty (trans≃ty (apply-lifted-sub-ty-≃ A idSub) (lift-ty-≃ (id-on-ty A))))))

idSub≃-Ty : (p : Γ ≃c Δ) → Typing-Sub Γ Δ (idSub≃ p)
idSub≃-Ty Emp≃ = TyNull TyStar
idSub≃-Ty (Add≃ {A = A} {A′ = A′} p x) = TyExt (lift-sub-typing (idSub≃-Ty p)) (TyConv (TyVar zero) (reflexive≈ty (sym≃ty (trans≃ty (apply-lifted-sub-ty-≃ A (idSub≃ p)) (lift-ty-≃ (trans≃ty (idSub≃-on-ty p A) x))))))
  where
    open Reasoning ty-setoid

    lem : lift-ty A′ ≃ty (A [ lift-sub (idSub≃ p) ]ty)
    lem = begin
      < lift-ty A′ >ty ≈˘⟨ lift-ty-≃ x ⟩
      < lift-ty A >ty ≈˘⟨ lift-ty-≃ (idSub≃-on-ty p A) ⟩
      < lift-ty (A [ idSub≃ p ]ty) >ty ≈˘⟨ apply-lifted-sub-ty-≃ A (idSub≃ p) ⟩
      < A [ lift-sub (idSub≃ p) ]ty >ty ∎

‼-Ty : Typing-Ctx Γ → (i : Fin n) → Typing-Ty Γ (Γ ‼ i)
‼-Ty (TyAdd Γty Aty) zero = lift-ty-typing Aty
‼-Ty (TyAdd Γty Aty) (suc i) = lift-ty-typing (‼-Ty Γty i)
