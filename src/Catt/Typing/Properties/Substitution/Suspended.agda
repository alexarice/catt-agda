
open import Catt.Typing.Rule

module Catt.Typing.Properties.Substitution.Suspended {index : Set}
                              (rule : index → Rule)
                              (lift-rule : ∀ i → LiftRule rule (rule i))
                              (susp-rule : ∀ i → SuspRule rule (rule i))
                              (sub-rule : ∀ i → SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule
open import Catt.Typing.Properties.Substitution rule lift-rule sub-rule as S hiding (apply-sub-ty-typing;apply-sub-tm-typing;apply-sub-sub-typing;apply-sub-ty-eq;apply-sub-tm-eq;apply-sub-sub-eq) public
open import Catt.Suspension
open import Catt.Suspension.Typing rule lift-rule susp-rule




apply-sub-ty-typing : {σ : Sub n m B} → Typing-Ty Γ A → Typing-Sub Γ Δ σ → Typing-Ty Δ (A [ σ ]ty)
apply-sub-tm-typing : {σ : Sub n m B} → Typing-Tm Γ t A → Typing-Sub Γ Δ σ → Typing-Tm Δ (t [ σ ]tm) (A [ σ ]ty)
apply-sub-sub-typing : {σ : Sub n m B} → Typing-Sub Υ Γ τ → Typing-Sub Γ Δ σ → Typing-Sub Υ Δ (σ ● τ)
apply-sub-ty-eq : Typing-Sub Γ Δ σ → A ≈[ Γ ]ty B → A [ σ ]ty ≈[ Δ ]ty B [ σ ]ty
apply-sub-tm-eq : {σ : Sub n m A} → Typing-Sub Γ Δ σ → s ≈[ Γ ]tm t → s [ σ ]tm ≈[ Δ ]tm t [ σ ]tm
apply-sub-sub-eq : Typing-Sub Γ Δ σ → τ ≈[ Γ ]s μ → σ ● τ ≈[ Δ ]s σ ● μ

apply-sub-ty-typing TyStar σty = sub-typing-implies-ty-typing σty
apply-sub-ty-typing (TyArr sty Aty tty) σty = TyArr (apply-sub-tm-typing sty σty) (apply-sub-ty-typing Aty σty) (apply-sub-tm-typing tty σty)

apply-sub-tm-typing {B = ⋆} tty σty = S.apply-sub-tm-typing tty σty
apply-sub-tm-typing {B = u ─⟨ B ⟩⟶ v} {t = t} {σ = σ} tty σty = transport-typing-full (apply-sub-tm-typing (susp-tmTy tty) (unrestrictTy σty)) (unrestrict-comp-tm t σ) (unrestrict-comp-ty _ σ)

apply-sub-sub-typing (TyNull x) σty = TyNull (apply-sub-ty-typing x σty)
apply-sub-sub-typing (TyExt {A = A} τty tty) σty = TyExt (apply-sub-sub-typing τty σty) (TyConv (apply-sub-tm-typing tty σty) (sym≈ty (reflexive≈ty (assoc-ty _ _ A))))

apply-sub-ty-eq σty Star≈ = refl≈ty
apply-sub-ty-eq σty (Arr≈ p q r) = Arr≈ (apply-sub-tm-eq σty p) (apply-sub-ty-eq σty q) (apply-sub-tm-eq σty r)

apply-sub-tm-eq {A = ⋆} σty p = S.apply-sub-tm-eq σty p
apply-sub-tm-eq {A = u ─⟨ A ⟩⟶ v} {Δ = Δ} {s = s} {t = t} {σ = σ} σty p = begin
  s [ σ ]tm
    ≈˘⟨ reflexive≈tm (unrestrict-comp-tm s σ) ⟩
  susp-tm s [ unrestrict σ ]tm
    ≈⟨ apply-sub-tm-eq (unrestrictTy σty) (susp-tmEq p) ⟩
  susp-tm t [ unrestrict σ ]tm
    ≈⟨ reflexive≈tm (unrestrict-comp-tm t σ) ⟩
  t [ σ ]tm ∎
  where
    open Reasoning (tm-setoid-≈ Δ)

apply-sub-sub-eq σty (Null≈ x) = Null≈ (apply-sub-ty-eq σty x)
apply-sub-sub-eq σty (Ext≈ p x) = Ext≈ (apply-sub-sub-eq σty p) (apply-sub-tm-eq σty x)
