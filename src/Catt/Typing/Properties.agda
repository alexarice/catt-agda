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

lift-ty-typing : Typing-Ty Γ A → Typing-Ty (Γ , B) (liftType A)
lift-tm-typing : Typing-Tm Γ t A → Typing-Tm (Γ , B) (liftTerm t) (liftType A)
lift-sub-typing : Typing-Sub Γ Δ σ → Typing-Sub Γ (Δ , B) (liftSub σ)

lift-ty-equality : A ≈ty B → (liftType {A = C} A) ≈ty (liftType {A = C} B)
lift-tm-equality : s ≈tm t → (liftTerm {A = A} s) ≈tm (liftTerm {A = B} t)
lift-sub-equality : σ ≈s τ → (liftSub {A = A} σ) ≈s (liftSub {A = B} τ)

lift-ty-typing TyStar = TyStar
lift-ty-typing (TyArr p q r) = TyArr (lift-tm-typing p) (lift-ty-typing q) (lift-tm-typing r)

lift-tm-typing (TyVar i x) = TyVar (suc i) (lift-ty-equality x)
lift-tm-typing (TyCoh pd q r s t) = TyCoh pd q (lift-sub-typing r) s (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ _ _)) (lift-ty-equality t))
lift-tm-typing (TyComp {s = s} {A = A} {t = t} pd p q r u v) = TyComp pd p (lift-sub-typing q) r u (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ (s ─⟨ A ⟩⟶ t) _)) (lift-ty-equality v))

lift-sub-typing TyNull = TyNull
lift-sub-typing (TyExt p q r) = TyExt (lift-sub-typing p) q (term-conversion (lift-tm-typing r) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ _ _))))

lift-ty-equality Star≈ = Star≈
lift-ty-equality (Arr≈ p q r) = Arr≈ (lift-tm-equality p) (lift-ty-equality q) (lift-tm-equality r)

lift-tm-equality (Var≈ i) = Var≈ (cong suc i)
lift-tm-equality (Sym≈ eq) = Sym≈ (lift-tm-equality eq)
lift-tm-equality (Trans≈ eq eq′) = Trans≈ (lift-tm-equality {B = ⋆} eq) (lift-tm-equality eq′)
lift-tm-equality (Coh≈ p q r) = Coh≈ p q (lift-sub-equality r)
lift-tm-equality (Rule≈ i a tc eqt) = props i .lift-rule a (λ j {A} → lift-tm-typing (tc j)) λ j {A} {B} → lift-tm-equality (eqt j)

lift-sub-equality Null≈ = Null≈
lift-sub-equality (Ext≈ eq x) = Ext≈ (lift-sub-equality eq) (lift-tm-equality x)
