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

term-conversion : Typing-Tm Γ t A → A ≈ty B → Typing-Tm Γ t B
term-conversion (TyVar i x) eq = TyVar i (trans≈ty x eq)
term-conversion (TyCoh p q r s t) eq = TyCoh p q r s (trans≈ty t eq)
term-conversion (TyComp pd p q r s t) eq = TyComp pd p q r s (trans≈ty t eq)

lift-ty-typing : Typing-Ty Γ A → Typing-Ty (Γ , B) (liftType A)
lift-tm-typing : Typing-Tm Γ t A → Typing-Tm (Γ , B) (liftTerm t) (liftType A)
lift-sub-typing : Typing-Sub Γ Δ σ → Typing-Sub Γ (Δ , B) (liftSub σ)

lift-ty-equality : B ≈ty C → (liftType B) ≈ty (liftType C)
lift-tm-equality : s ≈tm t → (liftTerm s) ≈tm (liftTerm t)
lift-sub-equality : σ ≈s τ → (liftSub σ) ≈s (liftSub τ)

lift-ty-typing TyStar = TyStar
lift-ty-typing (TyArr p q r) = TyArr (lift-tm-typing p) (lift-ty-typing q) (lift-tm-typing r)

lift-tm-typing (TyVar i x) = TyVar (suc i) (lift-ty-equality x)
lift-tm-typing (TyCoh pd q r s t) = TyCoh pd q (lift-sub-typing r) s (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ _ _)) (lift-ty-equality t))
lift-tm-typing (TyComp {s = s} {A = A} {t = t} pd p q r u v) = TyComp pd p (lift-sub-typing q) r u (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ (s ─⟨ A ⟩⟶ t) _)) (lift-ty-equality v))

lift-sub-typing TyNull = TyNull
lift-sub-typing (TyExt p q r) = TyExt (lift-sub-typing p) q (term-conversion (lift-tm-typing r) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ _ _))))

lift-ty-equality Star≈ = Star≈
lift-ty-equality (Arr≈ q r s) = Arr≈ (lift-tm-equality q) (lift-ty-equality r) (lift-tm-equality s)

lift-tm-equality (Var≈ x) = Var≈ (cong suc x)
lift-tm-equality (Sym≈ eq) = Sym≈ (lift-tm-equality eq)
lift-tm-equality (Trans≈ eq eq′) = Trans≈ (lift-tm-equality eq) (lift-tm-equality eq′)

lift-tm-equality (Coh≈ q r s) = Coh≈ q r (lift-sub-equality s)
lift-tm-equality (Rule≈ i a tc eqt) = props i .lift-rule a (λ j {A} → lift-tm-typing (tc j)) λ j → lift-tm-equality (eqt j)

lift-sub-equality Null≈ = Null≈
lift-sub-equality (Ext≈ eq x) = Ext≈ (lift-sub-equality eq) (lift-tm-equality x)

apply-sub-ty-typing : Typing-Ty Γ A → Typing-Sub Γ Δ σ → Typing-Ty Δ (A [ σ ]ty)
apply-sub-tm-typing : Typing-Tm Γ t A → Typing-Sub Γ Δ σ → Typing-Tm Δ (t [ σ ]tm) (A [ σ ]ty)
apply-sub-sub-typing : Typing-Sub Υ Γ τ → Typing-Sub Γ Δ σ → Typing-Sub Υ Δ (σ ∘ τ)

apply-sub-ty-typing TyStar σty = TyStar
apply-sub-ty-typing (TyArr sty Aty tty) σty = TyArr (apply-sub-tm-typing sty σty) (apply-sub-ty-typing Aty σty) (apply-sub-tm-typing tty σty)

apply-sub-tm-typing (TyVar zero x) (TyExt σty Aty tty) = term-conversion tty {!!}
apply-sub-tm-typing (TyVar (suc i) x) (TyExt σty Aty tty) = term-conversion (apply-sub-tm-typing (TyVar i refl≈ty) σty) {!!}
apply-sub-tm-typing (TyCoh pd w x y z) σty = TyCoh pd w (apply-sub-sub-typing x σty) y {!!}
apply-sub-tm-typing (TyComp pd v w x y z) σty = TyComp pd v (apply-sub-sub-typing w σty) x y {!!}

apply-sub-sub-typing TyNull σty = TyNull
apply-sub-sub-typing {Υ = Υ} {Γ = Γ} {Δ = Δ} (TyExt τty Aty tty) σty = TyExt (apply-sub-sub-typing τty σty) Aty (term-conversion (apply-sub-tm-typing tty σty) (sym≈ty (reflexive≈ty (assoc-ty _ _ _))))

apply-sub-ty-eq : A ≈ty B → A [ σ ]ty ≈ty B [ σ ]ty
apply-sub-tm-eq : s ≈tm t → s [ σ ]tm ≈tm t [ σ ]tm
apply-sub-sub-eq : τ ≈s μ → σ ∘ τ ≈s σ ∘ μ

apply-sub-ty-eq Star≈ = Star≈
apply-sub-ty-eq (Arr≈ p q r) = Arr≈ (apply-sub-tm-eq p) (apply-sub-ty-eq q) (apply-sub-tm-eq r)

apply-sub-tm-eq (Var≈ x) = ?
apply-sub-tm-eq (Sym≈ p) = ?
apply-sub-tm-eq (Trans≈ p p₁) = ?
apply-sub-tm-eq (Coh≈ x x₁ x₂) = ?
apply-sub-tm-eq (Rule≈ i a tct₁ eqt) = ?

apply-sub-sub-eq p = {!!}
