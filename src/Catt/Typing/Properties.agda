{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base

module Catt.Typing.Properties (Index : Set) (rule : Index → Rule) (props : (i : Index) → Catt.Typing.Properties.Base.Props Index rule i) where

open import Catt.Typing.Properties.Base Index rule public

open import Catt.Typing Index rule
open import Catt.Syntax
open import Data.Fin using (Fin; zero; suc)
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Relation.Binary.PropositionalEquality

term-conversion : Typing-Tm Γ t A → A ≈ty B → Typing-Tm Γ t B
term-conversion (TyVar i x) eq = TyVar i (trans≈ty x eq)
term-conversion (TyCoh p q r s t) eq = TyCoh p q r s (trans≈ty t eq)
term-conversion (TyComp pd p q r s t) eq = TyComp pd p q r s (trans≈ty t eq)

≈tm-preserve-ctx : {s : Tm Γ} {t : Tm Δ} → s ≈tm t → Γ ≈c Δ
≈tm-preserve-ctx (Var≈ x x₁) = x
≈tm-preserve-ctx (Sym≈ p) = sym≈c (≈tm-preserve-ctx p)
≈tm-preserve-ctx (Trans≈ p q) = trans≈c (≈tm-preserve-ctx p) (≈tm-preserve-ctx q)
≈tm-preserve-ctx (Coh≈ p q r) = ≈s-to-codomain-≈c r
≈tm-preserve-ctx (Rule≈ i a tct eqt) = props i .ctx-eq a tct eqt

idSub≈ : Γ ≈c Δ → Sub Γ Δ
idSub≈ Emp≈ = ⟨⟩
idSub≈ (Add≈ p x) = ⟨ (liftSub (idSub≈ p)) , 0V ⟩

idSub≈-on-ty : (p : Γ ≈c Δ) → (A : Ty Γ d) → A [ idSub≈ p ]ty ≈ty A
idSub≈-on-tm : (p : Γ ≈c Δ) → (s : Tm Γ) → s [ idSub≈ p ]tm ≈tm s
idSub≈-on-sub : (p : Γ ≈c Δ) → (σ : Sub Υ Γ) → idSub≈ p ∘ σ ≈s σ

lift-ty-typing : Typing-Ty Γ A → Typing-Ty (Γ , B) (liftType A)
lift-tm-typing : Typing-Tm Γ t A → Typing-Tm (Γ , B) (liftTerm t) (liftType A)
lift-sub-typing : Typing-Sub Γ Δ σ → Typing-Sub Γ (Δ , B) (liftSub σ)

lift-ty-equality : A ≈ty A′ → B ≈ty C → (liftType {A = A} B) ≈ty (liftType {A = A′} C)
lift-tm-equality : A ≈ty B → s ≈tm t → (liftTerm {A = A} s) ≈tm (liftTerm {A = B} t)
lift-sub-equality : A ≈ty B → σ ≈s τ → (liftSub {A = A} σ) ≈s (liftSub {A = B} τ)

idSub≈-on-ty p ⋆ = Star≈ (sym≈c p)
idSub≈-on-ty p (s ─⟨ A ⟩⟶ t) = Arr≈ (idSub≈-on-tm p s) (idSub≈-on-ty p A) (idSub≈-on-tm p t)

idSub≈-on-tm p (Var i) = lem p i
  where
    lem : (p : Γ ≈c Δ) → (i : Fin (ctxLength Γ)) → Var i [ idSub≈ p ]tm ≈tm Var {Γ = Γ} i
    lem (Add≈ p x) zero = Var≈ (sym≈c (Add≈ p x)) refl
    lem (Add≈ p x) (suc i) = trans≈tm (reflexive≈tm (apply-lifted-sub-tm-≃ (Var i) (idSub≈ p))) (lift-tm-equality (sym≈ty x) (lem p i))
idSub≈-on-tm p (Coh Δ A σ) = Coh≈ refl≈c refl≈ty (idSub≈-on-sub p σ)

idSub≈-on-sub p ⟨⟩ = Null≈ (sym≈c p)
idSub≈-on-sub p ⟨ σ , t ⟩ = Ext≈ (idSub≈-on-sub p σ) (idSub≈-on-tm p t)

lift-ty-typing TyStar = TyStar
lift-ty-typing (TyArr p q r) = TyArr (lift-tm-typing p) (lift-ty-typing q) (lift-tm-typing r)

lift-tm-typing (TyVar i x) = TyVar (suc i) (lift-ty-equality refl≈ty x)
lift-tm-typing (TyCoh pd q r s t) = TyCoh pd q (lift-sub-typing r) s (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ _ _)) (lift-ty-equality refl≈ty t))
lift-tm-typing (TyComp {s = s} {A = A} {t = t} pd p q r u v) = TyComp pd p (lift-sub-typing q) r u (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ (s ─⟨ A ⟩⟶ t) _)) (lift-ty-equality refl≈ty v))

lift-sub-typing TyNull = TyNull
lift-sub-typing (TyExt p q r) = TyExt (lift-sub-typing p) q (term-conversion (lift-tm-typing r) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ _ _))))

lift-ty-equality p (Star≈ x) = Star≈ (Add≈ x p)
lift-ty-equality p (Arr≈ q r s) = Arr≈ (lift-tm-equality p q) (lift-ty-equality p r) (lift-tm-equality p s)

lift-tm-equality p (Var≈ x y) = Var≈ (Add≈ x p) (cong suc y)
lift-tm-equality p (Sym≈ eq) = Sym≈ (lift-tm-equality (sym≈ty p) eq)
lift-tm-equality {A = A} p (Trans≈ eq eq′) = Trans≈ (lift-tm-equality {B = A [ idSub≈ (≈tm-preserve-ctx eq) ]ty} (sym≈ty (idSub≈-on-ty (≈tm-preserve-ctx eq) A)) eq) (lift-tm-equality (trans≈ty (idSub≈-on-ty (≈tm-preserve-ctx eq) A) p) eq′)

lift-tm-equality p (Coh≈ q r s) = Coh≈ q r (lift-sub-equality p s)
lift-tm-equality p (Rule≈ i a tc eqt) = props i .lift-rule a (λ j {A} → lift-tm-typing (tc j)) λ j {A} {B} → lift-tm-equality {!!} (eqt j)

lift-sub-equality p (Null≈ x) = Null≈ (Add≈ x p)
lift-sub-equality p (Ext≈ eq x) = Ext≈ (lift-sub-equality p eq) (lift-tm-equality p x)
