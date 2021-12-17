{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.Properties.Lifting (index : ℕ)
                                      (rule : Fin index → Rule)
                                      (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open P index rule
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning

lift-ty-typing : Typing-Ty Γ A → Typing-Ty (Γ , B) (liftType A)
lift-tm-typing : Typing-Tm Γ t A → Typing-Tm (Γ , B) (liftTerm t) (liftType A)
lift-sub-typing : Typing-Sub Γ Δ σ → Typing-Sub Γ (Δ , B) (liftSub σ)

lift-ty-equality : B ≈[ Γ ]ty C → (liftType B) ≈[ Γ , A ]ty (liftType C)
lift-tm-equality : s ≈[ Γ ]tm t → (liftTerm s) ≈[ Γ , A ]tm (liftTerm t)
lift-sub-equality : σ ≈[ Γ ]s τ → (liftSub σ) ≈[ Γ , A ]s (liftSub τ)

lift-ty-typing TyStar = TyStar
lift-ty-typing (TyArr p q r) = TyArr (lift-tm-typing p) (lift-ty-typing q) (lift-tm-typing r)

lift-tm-typing (TyVarZ x y) = TyVarS zero (TyVarZ x y) refl≈ty
lift-tm-typing (TyVarS i tvi x) = TyVarS (suc i) (TyVarS i tvi x) refl≈ty
lift-tm-typing (TyCoh {A = A} Aty σty b sc p) = TyCoh Aty (lift-sub-typing σty) b sc (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ A _)) (lift-ty-equality p))

lift-sub-typing (TyNull x) = TyNull (lift-ty-typing x)
lift-sub-typing (TyExt {A = A} p q r) = TyExt (lift-sub-typing p) q (term-conversion (lift-tm-typing r) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ A _))))

lift-ty-equality Star≈ = Star≈
lift-ty-equality (Arr≈ q r s) = Arr≈ (lift-tm-equality q) (lift-ty-equality r) (lift-tm-equality s)

lift-tm-equality (Var≈ x) = Var≈ (cong suc x)
lift-tm-equality (Sym≈ eq) = Sym≈ (lift-tm-equality eq)
lift-tm-equality (Trans≈ eq eq′) = Trans≈ (lift-tm-equality eq) (lift-tm-equality eq′)

lift-tm-equality (Coh≈ r s) = Coh≈ r (lift-sub-equality s)
lift-tm-equality {A = A} (Rule≈ i a tc) = lift-rule i a (lift-tm-typing tc)

lift-sub-equality (Null≈ x) = Null≈ (lift-ty-equality x)
lift-sub-equality (Ext≈ eq x) = Ext≈ (lift-sub-equality eq) (lift-tm-equality x)

id-Ty : Typing-Ctx Γ → Typing-Sub Γ Γ idSub
id-Ty TyEmp = TyNull TyStar
id-Ty (TyAdd Γty x) = TyExt (lift-sub-typing (id-Ty Γty)) x (TyVarZ x (reflexive≈ty (trans≃ty (sym≃ty (id-on-ty (liftType _))) (lift-sub-comp-lem-ty (liftSub idSub) _))))

idSub≃-Ty : (p : Γ ≃c Δ) → Typing-Ctx Γ → Typing-Sub Γ Δ (idSub≃ p)
idSub≃-Ty Emp≃ Γty = TyNull TyStar
idSub≃-Ty (Add≃ {A = A} {A′ = A′} p x) (TyAdd Γty y) = TyExt (lift-sub-typing (idSub≃-Ty p Γty)) y (TyVarZ (transport-typing-ty y p x) (reflexive≈ty lem))
  where
    open Reasoning ty-setoid

    lem : liftType A′ ≃ty (A [ liftSub (idSub≃ p) ]ty)
    lem = begin
      < liftType A′ >ty ≈˘⟨ lift-ty-≃ x ⟩
      < liftType A >ty ≈˘⟨ lift-ty-≃ (idSub≃-on-ty p A) ⟩
      < liftType (A [ idSub≃ p ]ty) >ty ≈˘⟨ apply-lifted-sub-ty-≃ A (idSub≃ p) ⟩
      < A [ liftSub (idSub≃ p) ]ty >ty ∎

‼-Ty : Typing-Ctx Γ → (i : Fin n) → Typing-Ty Γ (Γ ‼ i)
‼-Ty (TyAdd Γty Aty) zero = lift-ty-typing Aty
‼-Ty (TyAdd Γty Aty) (suc i) = lift-ty-typing (‼-Ty Γty i)
