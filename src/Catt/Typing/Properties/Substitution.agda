open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Typing.Properties.Substitution (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open P index rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open import Catt.Suspension

sub-typing-implies-ty-typing : {σ : Sub n m A} → Typing-Sub Γ Δ σ → Typing-Ty Δ A
sub-typing-implies-ty-typing (TyNull x) = x
sub-typing-implies-ty-typing (TyExt σty x) = sub-typing-implies-ty-typing σty

sub-eq-implies-ty-eq : {σ : Sub n m A} → {τ : Sub n m B} → σ ≈[ Δ ]s τ → A ≈[ Δ ]ty B
sub-eq-implies-ty-eq (Null≈ x) = x
sub-eq-implies-ty-eq (Ext≈ eq x) = sub-eq-implies-ty-eq eq

apply-sub-ty-typing : {σ : Sub n m ⋆} → Typing-Ty Γ A → Typing-Sub Γ Δ σ → Typing-Ty Δ (A [ σ ]ty)
apply-sub-tm-typing : {σ : Sub n m ⋆} → Typing-Tm Γ t A → Typing-Sub Γ Δ σ → Typing-Tm Δ (t [ σ ]tm) (A [ σ ]ty)
apply-sub-sub-typing : {σ : Sub n m ⋆} → Typing-Sub Υ Γ τ → Typing-Sub Γ Δ σ → Typing-Sub Υ Δ (σ ● τ)
apply-sub-ty-eq : {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → A ≈[ Γ ]ty B → A [ σ ]ty ≈[ Δ ]ty B [ σ ]ty
apply-sub-tm-eq : {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → s ≈[ Γ ]tm t → s [ σ ]tm ≈[ Δ ]tm t [ σ ]tm
apply-sub-sub-eq : {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → τ ≈[ Γ ]s μ → σ ● τ ≈[ Δ ]s σ ● μ

apply-sub-ty-typing TyStar σty = sub-typing-implies-ty-typing σty
apply-sub-ty-typing (TyArr sty Aty tty) σty = TyArr (apply-sub-tm-typing sty σty) (apply-sub-ty-typing Aty σty) (apply-sub-tm-typing tty σty)

apply-sub-tm-typing (TyConv tty p) σty = TyConv (apply-sub-tm-typing tty σty) (apply-sub-ty-eq σty p)
apply-sub-tm-typing (TyVar zero) (TyExt {σ = σ} {A = A} σty x) = TyConv x (reflexive≈ty (sym≃ty (lift-sub-comp-lem-ty σ A)))
apply-sub-tm-typing {Γ = Γ , _} (TyVar (suc i)) (TyExt {σ = σ} σty x) = TyConv (apply-sub-tm-typing (TyVar i) σty) (reflexive≈ty (sym≃ty (lift-sub-comp-lem-ty σ (Γ ‼ i))))
apply-sub-tm-typing (TyCoh {A = A} Aty τty b sc) σty = TyConv (TyCoh Aty (apply-sub-sub-typing τty σty) b sc) (reflexive≈ty (assoc-ty _ _ A))

apply-sub-sub-typing (TyNull x) σty = TyNull (apply-sub-ty-typing x σty)
apply-sub-sub-typing (TyExt {A = A} τty tty) σty = TyExt (apply-sub-sub-typing τty σty) (TyConv (apply-sub-tm-typing tty σty) (sym≈ty (reflexive≈ty (assoc-ty _ _ A))))

apply-sub-ty-eq σty Star≈ = refl≈ty
apply-sub-ty-eq σty (Arr≈ p q r) = Arr≈ (apply-sub-tm-eq σty p) (apply-sub-ty-eq σty q) (apply-sub-tm-eq σty r)

apply-sub-tm-eq σty (Var≈ x) with toℕ-injective x
... | refl = refl≈tm
apply-sub-tm-eq σty (Sym≈ p) = Sym≈ (apply-sub-tm-eq σty p)
apply-sub-tm-eq σty (Trans≈ p q) = Trans≈ (apply-sub-tm-eq σty p) (apply-sub-tm-eq σty q)
apply-sub-tm-eq σty (Coh≈ q r) = Coh≈ q (apply-sub-sub-eq σty r)
apply-sub-tm-eq σty (Rule≈ i args tc) = sub-rule i args σty (apply-sub-tm-typing tc σty)

apply-sub-sub-eq σty (Null≈ x) = Null≈ (apply-sub-ty-eq σty x)
apply-sub-sub-eq σty (Ext≈ p x) = Ext≈ (apply-sub-sub-eq σty p) (apply-sub-tm-eq σty x)

apply-sub-eq-ty : (A : Ty n) → σ ≈[ Γ ]s τ → A [ σ ]ty ≈[ Γ ]ty A [ τ ]ty
apply-sub-eq-tm : {σ : Sub n m A} → {τ : Sub n m B} → (t : Tm n) → σ ≈[ Γ ]s τ → t [ σ ]tm ≈[ Γ ]tm t [ τ ]tm
apply-sub-eq-sub : (μ : Sub n m ⋆) → σ ≈[ Γ ]s τ → σ ● μ ≈[ Γ ]s τ ● μ

apply-sub-eq-ty ⋆ eq = sub-eq-implies-ty-eq eq
apply-sub-eq-ty (s ─⟨ A ⟩⟶ t) eq = Arr≈ (apply-sub-eq-tm s eq) (apply-sub-eq-ty A eq) (apply-sub-eq-tm t eq)

apply-sub-eq-tm (Var zero) (Ext≈ eq x) = x
apply-sub-eq-tm (Var (suc i)) (Ext≈ eq x) = apply-sub-eq-tm (Var i) eq
apply-sub-eq-tm {A = ⋆} {B = ⋆} (Coh T C τ) eq = Coh≈ refl≈ty (apply-sub-eq-sub τ eq)
apply-sub-eq-tm {A = ⋆} {B = s ─⟨ B ⟩⟶ t} (Coh T C τ) eq with sub-eq-implies-ty-eq eq
... | ()
apply-sub-eq-tm {A = s ─⟨ A ⟩⟶ t} {B = ⋆} (Coh T C τ) eq with sub-eq-implies-ty-eq eq
... | ()
apply-sub-eq-tm {A = s ─⟨ A ⟩⟶ t} {B = s₁ ─⟨ B ⟩⟶ t₁} (Coh Δ C τ) eq = apply-sub-eq-tm (Coh (suspCtx Δ) (suspTy C) (suspSub τ)) (unrestrictEq eq)

apply-sub-eq-sub ⟨⟩ eq = Null≈ (sub-eq-implies-ty-eq eq)
apply-sub-eq-sub ⟨ μ , t ⟩ eq = Ext≈ (apply-sub-eq-sub μ eq) (apply-sub-eq-tm t eq)
