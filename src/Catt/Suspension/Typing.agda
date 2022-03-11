open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Suspension.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Support
open import Catt.Syntax.SyntacticEquality
open P index rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open import Catt.Pasting
open import Catt.Suspension.Pasting

suspCtxTy : Typing-Ctx Γ → Typing-Ctx (suspCtx Γ)
suspTyTy : Typing-Ty Γ A → Typing-Ty (suspCtx Γ) (suspTy A)
suspTmTy : Typing-Tm Γ t A → Typing-Tm (suspCtx Γ) (suspTm t) (suspTy A)
suspSubTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) (suspCtx Δ) (suspSub σ)
getFstTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getFst) ⋆
getSndTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getSnd) ⋆

suspTyEq : A ≈[ Γ ]ty B → suspTy A ≈[ suspCtx Γ ]ty suspTy B
suspTmEq : s ≈[ Γ ]tm t → suspTm s ≈[ suspCtx Γ ]tm suspTm t
suspSubEq : σ ≈[ Γ ]s τ → suspSub σ ≈[ suspCtx Γ ]s suspSub τ

suspCtxTy TyEmp = TyAdd (TyAdd TyEmp TyStar) TyStar
suspCtxTy (TyAdd ty x) = TyAdd (suspCtxTy ty) (suspTyTy x)

suspTyTy TyStar = TyArr getFstTy TyStar getSndTy
suspTyTy (TyArr p q r) = TyArr (suspTmTy p) (suspTyTy q) (suspTmTy r)

suspTmTy {Γ = Γ , A} (TyVarZ {Γ = Γ} {A = A} x y) = TyVarZ (suspTyTy x) (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift A))) (suspTyEq y))
suspTmTy (TyVarS i tvi x) = TyVarS (inject₁ (inject₁ i)) (suspTmTy tvi) (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift _))) (suspTyEq x))
suspTmTy (TyCoh Aty σty b sc p) = TyCoh ⦃ susp-pd it ⦄ (suspTyTy Aty) (suspSubTy σty) b (suspSuppCondition sc) (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty _ _))) (suspTyEq p))

suspSubTy (TyNull x) = TyExt (TyExt (TyNull TyStar) TyStar getFstTy) TyStar getSndTy
suspSubTy (TyExt p q r) = TyExt (suspSubTy p) (suspTyTy q) (term-conversion (suspTmTy r) (reflexive≈ty (susp-functorial-ty _ _)))

getFstTy {Γ = ∅} = TyVarS zero (TyVarZ TyStar Star≈) Star≈
getFstTy {Γ = Γ , A} = lift-tm-typing getFstTy

getSndTy {Γ = ∅} = TyVarZ TyStar Star≈
getSndTy {Γ = Γ , A} = lift-tm-typing getSndTy

suspTyEq Star≈ = refl≈ty
suspTyEq (Arr≈ q r s) = Arr≈ (suspTmEq q) (suspTyEq r) (suspTmEq s)
suspTmEq (Var≈ x) = Var≈ (begin
  toℕ (inject₁ (inject₁ _)) ≡⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ _) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ _ ≡⟨ x ⟩
  toℕ _ ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ _) ≡˘⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ (inject₁ _)) ∎)
  where
    open ≡-Reasoning

suspTmEq (Sym≈ eq) = Sym≈ (suspTmEq eq)
suspTmEq (Trans≈ eq eq′) = Trans≈ (suspTmEq eq) (suspTmEq eq′)
suspTmEq (Coh≈ q r) = Coh≈ (suspTyEq q) (suspSubEq r)
suspTmEq (Rule≈ i a tc) = susp-rule i a (suspTmTy tc)

suspSubEq (Null≈ x) = refl≈s
suspSubEq (Ext≈ p x) = Ext≈ (suspSubEq p) (suspTmEq x)

unrestrictTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) Δ (unrestrict σ)
unrestrictTy (TyNull (TyArr p q r)) = TyExt (TyExt (TyNull q) TyStar p) TyStar r
unrestrictTy (TyExt σty Aty x) = TyExt (unrestrictTy σty) (suspTyTy Aty) (term-conversion x (reflexive≈ty (unrestrict-comp-ty _ _)))
