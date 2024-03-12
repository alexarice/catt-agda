
open import Catt.Typing.Rule

module Catt.Typing.Properties.Substitution.Suspended
  (ops : Op)
  (rules : RuleSet)
  (tame : Tame ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Suspension

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Substitution ops rules sub-cond as S hiding (apply-sub-ty-typing;apply-sub-tm-typing;apply-sub-sub-typing;apply-sub-ty-eq;apply-sub-tm-eq;apply-sub-sub-eq) public
open import Catt.Suspension.Typing ops susp-op rules wk-cond susp-cond

apply-sub-ty-typing : {σ : Sub n m B} → Typing-Ty Γ A → Typing-Sub Γ Δ σ → Typing-Ty Δ (A [ σ ]ty)
apply-sub-tm-typing : {σ : Sub n m B} → Typing-Tm Γ t A → Typing-Sub Γ Δ σ → Typing-Tm Δ (t [ σ ]tm) (A [ σ ]ty)
apply-sub-sub-typing : {σ : Sub n m B} → Typing-Sub Υ Γ τ → Typing-Sub Γ Δ σ → Typing-Sub Υ Δ (τ ● σ)
apply-sub-ty-eq : Typing-Sub Γ Δ σ → A ≈[ Γ ]ty B → A [ σ ]ty ≈[ Δ ]ty B [ σ ]ty
apply-sub-tm-eq : {σ : Sub n m A} → Typing-Sub Γ Δ σ → s ≈[ Γ ]tm t → s [ σ ]tm ≈[ Δ ]tm t [ σ ]tm
apply-sub-sub-eq : Typing-Sub Γ Δ σ → τ ≈[ Γ ]s μ → τ ● σ ≈[ Δ ]s μ ● σ

apply-sub-ty-typing TyStar σty = sub-typing-implies-ty-typing σty
apply-sub-ty-typing (TyArr sty Aty tty) σty = TyArr (apply-sub-tm-typing sty σty) (apply-sub-ty-typing Aty σty) (apply-sub-tm-typing tty σty)

apply-sub-tm-typing {B = ⋆} tty σty = S.apply-sub-tm-typing tty σty
apply-sub-tm-typing {B = u ─⟨ B ⟩⟶ v} {t = t} {σ = σ} tty σty = transport-typing-full (apply-sub-tm-typing (susp-tmTy tty) (↓-Ty σty)) refl≃c (↓-comp-tm t σ) (↓-comp-ty _ σ)

apply-sub-sub-typing (TyNull x) σty = TyNull (apply-sub-ty-typing x σty)
apply-sub-sub-typing (TyExt {A = A} τty tty) σty = TyExt (apply-sub-sub-typing τty σty) (TyConv (apply-sub-tm-typing tty σty) (sym≈ty (reflexive≈ty (assoc-ty _ _ A))))

apply-sub-ty-eq σty Star≈ = refl≈ty
apply-sub-ty-eq σty (Arr≈ p q r) = Arr≈ (apply-sub-tm-eq σty p) (apply-sub-ty-eq σty q) (apply-sub-tm-eq σty r)

apply-sub-tm-eq {A = ⋆} σty p = S.apply-sub-tm-eq σty p
apply-sub-tm-eq {A = u ─⟨ A ⟩⟶ v} {Δ = Δ} {s = s} {t = t} {σ = σ} σty p = begin
  s [ σ ]tm
    ≈˘⟨ reflexive≈tm (↓-comp-tm s σ) ⟩
  susp-tm s [ ↓ σ ]tm
    ≈⟨ apply-sub-tm-eq (↓-Ty σty) (susp-tmEq p) ⟩
  susp-tm t [ ↓ σ ]tm
    ≈⟨ reflexive≈tm (↓-comp-tm t σ) ⟩
  t [ σ ]tm ∎
  where
    open Reasoning (tm-setoid-≈ Δ)

apply-sub-sub-eq σty (Null≈ x) = Null≈ (apply-sub-ty-eq σty x)
apply-sub-sub-eq σty (Ext≈ p x) = Ext≈ (apply-sub-sub-eq σty p) (apply-sub-tm-eq σty x)
