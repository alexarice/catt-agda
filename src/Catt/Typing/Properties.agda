{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat

module Catt.Typing.Properties (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing.Properties.Base index rule public

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Properties using (toℕ-injective)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles

term-conversion : Typing-Tm Γ t A → A ≈[ Γ ]ty B → Typing-Tm Γ t B
-- term-conversion (TyVar i x) eq = TyVar i (trans≈ty x eq)
term-conversion (TyVarZ x) eq = TyVarZ (trans≈ty x eq)
term-conversion (TyVarS i tvi x) eq = TyVarS i tvi (trans≈ty x eq)
term-conversion (TyCoh p q r s t) eq = TyCoh p q r s (trans≈ty t eq)
term-conversion (TyComp pd p q r s t) eq = TyComp pd p q r s (trans≈ty t eq)

-- type-conversion : Typing-Ty Γ A → A ≈[ Γ ]ty B → Typing-Ty Γ B
-- type-conversion TyStar Star≈ = TyStar
-- type-conversion (TyArr sty Aty tty) (Arr≈ p q r) = TyArr {!!} {!!} {!!}

lift-ty-typing : Typing-Ty Γ A → Typing-Ty (Γ , B) (liftType A)
lift-tm-typing : Typing-Tm Γ t A → Typing-Tm (Γ , B) (liftTerm t) (liftType A)
lift-sub-typing : Typing-Sub Γ Δ σ → Typing-Sub Γ (Δ , B) (liftSub σ)

lift-ty-equality : B ≈[ Γ ]ty C → (liftType B) ≈[ Γ , A ]ty (liftType C)
lift-tm-equality : s ≈[ Γ ]tm t → (liftTerm s) ≈[ Γ , A ]tm (liftTerm t)
lift-sub-equality : σ ≈[ Γ ]s τ → (liftSub σ) ≈[ Γ , A ]s (liftSub τ)

lift-ty-typing TyStar = TyStar
lift-ty-typing (TyArr p q r) = TyArr (lift-tm-typing p) (lift-ty-typing q) (lift-tm-typing r)

-- lift-tm-typing (TyVar i x) = TyVar (suc i) (lift-ty-equality x)
lift-tm-typing (TyVarZ x) = TyVarS zero (TyVarZ x) refl≈ty
lift-tm-typing (TyVarS i tvi x) = TyVarS (suc i) (TyVarS i tvi x) refl≈ty
lift-tm-typing (TyCoh pd q r s t) = TyCoh pd q (lift-sub-typing r) s (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ _ _)) (lift-ty-equality t))
lift-tm-typing (TyComp {s = s} {A = A} {t = t} pd p q r u v) = TyComp pd p (lift-sub-typing q) r u (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ (s ─⟨ A ⟩⟶ t) _)) (lift-ty-equality v))

lift-sub-typing TyNull = TyNull
lift-sub-typing (TyExt p r) = TyExt (lift-sub-typing p) (term-conversion (lift-tm-typing r) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ _ _))))

lift-ty-equality Star≈ = Star≈
lift-ty-equality (Arr≈ q r s) = Arr≈ (lift-tm-equality q) (lift-ty-equality r) (lift-tm-equality s)

lift-tm-equality (Var≈ x) = Var≈ (cong suc x)
lift-tm-equality (Sym≈ eq) = Sym≈ (lift-tm-equality eq)
lift-tm-equality (Trans≈ eq eq′) = Trans≈ (lift-tm-equality eq) (lift-tm-equality eq′)

lift-tm-equality (Coh≈ r s) = Coh≈ r (lift-sub-equality s)
lift-tm-equality {A = A} (Rule≈ i a eqt tc) = props i .lift-rule a (λ j → lift-tm-equality (eqt j)) (lift-tm-typing tc)

lift-sub-equality Null≈ = Null≈
lift-sub-equality (Ext≈ eq x) = Ext≈ (lift-sub-equality eq) (lift-tm-equality x)

apply-sub-ty-typing : Typing-Ty Γ A → Typing-Sub Γ Δ σ → Typing-Ty Δ (A [ σ ]ty)
apply-sub-tm-typing : Typing-Tm Γ t A → Typing-Sub Γ Δ σ → Typing-Tm Δ (t [ σ ]tm) (A [ σ ]ty)
apply-sub-sub-typing : Typing-Sub Υ Γ τ → Typing-Sub Γ Δ σ → Typing-Sub Υ Δ (σ ∘ τ)
apply-sub-ty-eq : Typing-Sub Γ Δ σ → A ≈[ Γ ]ty B → A [ σ ]ty ≈[ Δ ]ty B [ σ ]ty
apply-sub-tm-eq : Typing-Sub Γ Δ σ → s ≈[ Γ ]tm t → s [ σ ]tm ≈[ Δ ]tm t [ σ ]tm
apply-sub-sub-eq : Typing-Sub Γ Δ σ → τ ≈[ Γ ]s μ → σ ∘ τ ≈[ Δ ]s σ ∘ μ

apply-sub-ty-typing TyStar σty = TyStar
apply-sub-ty-typing (TyArr sty Aty tty) σty = TyArr (apply-sub-tm-typing sty σty) (apply-sub-ty-typing Aty σty) (apply-sub-tm-typing tty σty)

apply-sub-tm-typing (TyVarZ x) (TyExt {t = t} σty tty) = term-conversion tty (trans≈ty (sym≈ty (reflexive≈ty (lift-sub-comp-lem-ty {t = t} _ _))) (apply-sub-ty-eq (TyExt σty tty) x))
apply-sub-tm-typing (TyVarS i tvi x) (TyExt {t = t} σty tty) = term-conversion (apply-sub-tm-typing tvi σty) (trans≈ty (sym≈ty (reflexive≈ty (lift-sub-comp-lem-ty {t = t} _ _))) (apply-sub-ty-eq (TyExt σty tty) x))
apply-sub-tm-typing (TyCoh pd w x y z) σty = TyCoh pd w (apply-sub-sub-typing x σty) y (trans≈ty (reflexive≈ty (assoc-ty _ _ _)) (apply-sub-ty-eq σty z))
apply-sub-tm-typing (TyComp {s = s} {t = t} pd v w x y z) σty = TyComp pd v (apply-sub-sub-typing w σty) x y (trans≈ty (reflexive≈ty (assoc-ty _ _ (s ─⟨ _ ⟩⟶ t))) (apply-sub-ty-eq σty z))

apply-sub-sub-typing TyNull σty = TyNull
apply-sub-sub-typing {Υ = Υ} {Γ = Γ} {Δ = Δ} (TyExt τty tty) σty = TyExt (apply-sub-sub-typing τty σty) (term-conversion (apply-sub-tm-typing tty σty) (sym≈ty (reflexive≈ty (assoc-ty _ _ _))))

apply-sub-ty-eq σty Star≈ = Star≈
apply-sub-ty-eq σty (Arr≈ p q r) = Arr≈ (apply-sub-tm-eq σty p) (apply-sub-ty-eq σty q) (apply-sub-tm-eq σty r)

apply-sub-tm-eq σty (Var≈ x) with toℕ-injective x
... | refl = refl≈tm
apply-sub-tm-eq σty (Sym≈ p) = Sym≈ (apply-sub-tm-eq σty p)
apply-sub-tm-eq σty (Trans≈ p q) = Trans≈ (apply-sub-tm-eq σty p) (apply-sub-tm-eq σty q)
apply-sub-tm-eq σty (Coh≈ q r) = Coh≈ q (apply-sub-sub-eq σty r)
apply-sub-tm-eq σty (Rule≈ i args eqt tc) = props i .sub-rule args (λ j σty → apply-sub-tm-eq σty (eqt j)) σty (apply-sub-tm-typing tc σty)

apply-sub-sub-eq σty Null≈ = Null≈
apply-sub-sub-eq σty (Ext≈ p x) = Ext≈ (apply-sub-sub-eq σty p) (apply-sub-tm-eq σty x)

apply-sub-eq-ty : (A : Ty n d) → σ ≈[ Γ ]s τ → A [ σ ]ty ≈[ Γ ]ty A [ τ ]ty
apply-sub-eq-tm : (t : Tm n) → σ ≈[ Γ ]s τ → t [ σ ]tm ≈[ Γ ]tm t [ τ ]tm
apply-sub-eq-sub : (μ : Sub n m) → σ ≈[ Γ ]s τ → σ ∘ μ ≈[ Γ ]s τ ∘ μ

apply-sub-eq-ty ⋆ eq = Star≈
apply-sub-eq-ty (s ─⟨ A ⟩⟶ t) eq = Arr≈ (apply-sub-eq-tm s eq) (apply-sub-eq-ty A eq) (apply-sub-eq-tm t eq)

apply-sub-eq-tm (Var zero) (Ext≈ eq x) = x
apply-sub-eq-tm (Var (suc i)) (Ext≈ eq x) = apply-sub-eq-tm (Var i) eq
apply-sub-eq-tm (Coh Δ A σ) eq = Coh≈ refl≈ty (apply-sub-eq-sub σ eq)

apply-sub-eq-sub ⟨⟩ eq = Null≈
apply-sub-eq-sub ⟨ μ , t ⟩ eq = Ext≈ (apply-sub-eq-sub μ eq) (apply-sub-eq-tm t eq)

id-Ty : {Γ : Ctx n} → Typing-Sub Γ Γ (idSub n)
id-Ty {Γ = ∅} = TyNull
id-Ty {Γ = Γ , A} = TyExt (lift-sub-typing id-Ty) (TyVarZ (reflexive≈ty (trans≃ty (sym≃ty (id-on-ty (liftType _))) (lift-sub-comp-lem-ty (liftSub (idSub _)) _))))

idSub≃-Ty : (p : Γ ≃c Δ) → Typing-Sub Γ Δ (idSub≃ p)
idSub≃-Ty Emp≃ = TyNull
idSub≃-Ty (Add≃ {A = A} {A′ = A′} p x) = TyExt (lift-sub-typing (idSub≃-Ty p)) (TyVarZ (reflexive≈ty lem))
  where
    open Reasoning ty-setoid

    lem : liftType A′ ≃ty (A [ liftSub (idSub≃ p) ]ty)
    lem = begin
      < liftType A′ >ty ≈˘⟨ lift-ty-≃ x ⟩
      < liftType A >ty ≈˘⟨ lift-ty-≃ (idSub≃-on-ty p A) ⟩
      < liftType (A [ idSub≃ p ]ty) >ty ≈˘⟨ apply-lifted-sub-ty-≃ A (idSub≃ p) ⟩
      < A [ liftSub (idSub≃ p) ]ty >ty ∎

ty-base-Ty : Typing-Ty Γ A → Typing-Ty Γ (ty-base A)
ty-base-Ty (TyArr sty Aty tty) = Aty

ty-src-Ty : Typing-Ty Γ A → Typing-Tm Γ (ty-src A) (ty-base A)
ty-src-Ty (TyArr sty Aty tty) = sty

ty-tgt-Ty : Typing-Ty Γ A → Typing-Tm Γ (ty-tgt A) (ty-base A)
ty-tgt-Ty (TyArr sty Aty tty) = tty
