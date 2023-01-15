open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Suspension.Typing {index : Set}
                              (rule : index → Rule)
                              (lift-rule : ∀ i → P.LiftRule rule i)
                              (susp-rule : ∀ i → P.SuspRule rule i) where

open import Catt.Prelude.Properties
open import Catt.Typing rule
open import Catt.Syntax
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Support
open import Catt.Syntax.SyntacticEquality
open P rule
open import Catt.Typing.Properties.Lifting rule lift-rule
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

suspTmTy (TyConv tty p) = TyConv (suspTmTy tty) (suspTyEq p)
suspTmTy {Γ = Γ} (TyVar i) = TyConv (TyVar (inject₁ (inject₁ i))) (reflexive≈ty (susp-‼ Γ i))
suspTmTy (TyCoh Aty σty b sc) = TyConv (TyCoh ⦃ susp-pd it ⦄ (suspTyTy Aty) (suspSubTy σty) b (suspSuppCondition sc)) (reflexive≈ty (sym≃ty (susp-functorial-ty _ _)))

suspSubTy (TyNull x) = TyExt (TyExt (TyNull TyStar) getFstTy) getSndTy
suspSubTy (TyExt p r) = TyExt (suspSubTy p) (TyConv (suspTmTy r) (reflexive≈ty (susp-functorial-ty _ _)))

getFstTy {Γ = ∅} = TyVar (suc zero)
getFstTy {Γ = Γ , A} = lift-tm-typing getFstTy

getSndTy {Γ = ∅} = TyVar zero
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
suspTmEq (Rule≈ i tc) = susp-rule i (suspTmTy tc)

suspSubEq (Null≈ x) = refl≈s
suspSubEq (Ext≈ p x) = Ext≈ (suspSubEq p) (suspTmEq x)

unrestrictTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) Δ (unrestrict σ)
unrestrictTy (TyNull (TyArr p q r)) = TyExt (TyExt (TyNull q) p) r
unrestrictTy (TyExt σty x) = TyExt (unrestrictTy σty) (TyConv x (reflexive≈ty (sym≃ty (unrestrict-comp-ty _ _))))
