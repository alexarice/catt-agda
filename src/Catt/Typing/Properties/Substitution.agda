open import Catt.Typing.Rule

module Catt.Typing.Properties.Substitution
  (rules : RuleSet)
  (lift-cond : LiftCond rules)
  (sub-cond : SubCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Suspension

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules
open import Catt.Typing.Properties.Lifting rules lift-cond

sub-typing-implies-ty-typing : {σ : Sub n m A} → Typing-Sub Γ Δ σ → Typing-Ty Δ A
sub-typing-implies-ty-typing (TyNull x) = x
sub-typing-implies-ty-typing (TyExt σty x) = sub-typing-implies-ty-typing σty

sub-eq-implies-ty-eq : {σ : Sub n m A} → {τ : Sub n m B} → σ ≈[ Δ ]s τ → A ≈[ Δ ]ty B
sub-eq-implies-ty-eq (Null≈ x) = x
sub-eq-implies-ty-eq (Ext≈ eq x) = sub-eq-implies-ty-eq eq

apply-sub-ty-typing : {σ : Sub n m ⋆} → Typing-Ty Γ A → Typing-Sub Γ Δ σ → Typing-Ty Δ (A [ σ ]ty)
apply-sub-tm-typing : {σ : Sub n m ⋆} → Typing-Tm Γ t A → Typing-Sub Γ Δ σ → Typing-Tm Δ (t [ σ ]tm) (A [ σ ]ty)
apply-sub-sub-typing : {σ : Sub n m ⋆} → Typing-Sub Υ Γ τ → Typing-Sub Γ Δ σ → Typing-Sub Υ Δ (τ ● σ)
apply-sub-ty-eq : {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → A ≈[ Γ ]ty B → A [ σ ]ty ≈[ Δ ]ty B [ σ ]ty
apply-sub-tm-eq : {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → s ≈[ Γ ]tm t → s [ σ ]tm ≈[ Δ ]tm t [ σ ]tm
apply-sub-sub-eq : {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → τ ≈[ Γ ]s μ → τ ● σ ≈[ Δ ]s μ ● σ

apply-sub-ty-typing TyStar σty = sub-typing-implies-ty-typing σty
apply-sub-ty-typing (TyArr sty Aty tty) σty = TyArr (apply-sub-tm-typing sty σty) (apply-sub-ty-typing Aty σty) (apply-sub-tm-typing tty σty)

apply-sub-tm-typing (TyConv tty p) σty = TyConv (apply-sub-tm-typing tty σty) (apply-sub-ty-eq σty p)
apply-sub-tm-typing (TyVar zero) (TyExt {σ = σ} {A = A} σty x)
  = TyConv x (reflexive≈ty (sym≃ty (apply-sub-lifted-ty-≃ A ⟨ σ , _ ⟩)))
apply-sub-tm-typing {Γ = Γ , _} (TyVar (suc i)) (TyExt {σ = σ} σty x)
  = TyConv (apply-sub-tm-typing (TyVar i) σty) (reflexive≈ty (sym≃ty (apply-sub-lifted-ty-≃ (Γ ‼ i) ⟨ σ , _ ⟩)))
apply-sub-tm-typing (TyCoh {A = A} Aty τty) σty = TyConv (TyCoh Aty (apply-sub-sub-typing τty σty)) (reflexive≈ty (assoc-ty _ _ A))

apply-sub-sub-typing (TyNull x) σty = TyNull (apply-sub-ty-typing x σty)
apply-sub-sub-typing (TyExt {A = A} τty tty) σty = TyExt (apply-sub-sub-typing τty σty) (TyConv (apply-sub-tm-typing tty σty) (sym≈ty (reflexive≈ty (assoc-ty _ _ A))))

apply-sub-ty-eq σty Star≈ = refl≈ty
apply-sub-ty-eq σty (Arr≈ p q r) = Arr≈ (apply-sub-tm-eq σty p) (apply-sub-ty-eq σty q) (apply-sub-tm-eq σty r)

apply-sub-tm-eq σty (Var≈ x) with toℕ-injective x
... | refl = refl≈tm
apply-sub-tm-eq σty (Sym≈ p) = Sym≈ (apply-sub-tm-eq σty p)
apply-sub-tm-eq σty (Trans≈ p q) = Trans≈ (apply-sub-tm-eq σty p) (apply-sub-tm-eq σty q)
apply-sub-tm-eq σty (Coh≈ q r) = Coh≈ q (apply-sub-sub-eq σty r)
apply-sub-tm-eq {σ = σ} σty (Rule≈ r p tc) = Rule≈ (sub-rule r _ _)
                                                   (sub-cond _ σty p)
                                                   (apply-sub-tm-typing tc σty)

apply-sub-sub-eq σty (Null≈ x) = Null≈ (apply-sub-ty-eq σty x)
apply-sub-sub-eq σty (Ext≈ p x) = Ext≈ (apply-sub-sub-eq σty p) (apply-sub-tm-eq σty x)

apply-sub-eq-ty : (A : Ty n) → σ ≈[ Γ ]s τ → A [ σ ]ty ≈[ Γ ]ty A [ τ ]ty
apply-sub-eq-tm : {σ : Sub n m A} → {τ : Sub n m B} → (t : Tm n) → σ ≈[ Γ ]s τ → t [ σ ]tm ≈[ Γ ]tm t [ τ ]tm
apply-sub-eq-sub : (μ : Sub n m ⋆) → σ ≈[ Γ ]s τ → μ ● σ ≈[ Γ ]s μ ● τ

apply-sub-eq-ty ⋆ eq = sub-eq-implies-ty-eq eq
apply-sub-eq-ty (s ─⟨ A ⟩⟶ t) eq = Arr≈ (apply-sub-eq-tm s eq) (apply-sub-eq-ty A eq) (apply-sub-eq-tm t eq)

apply-sub-eq-tm (Var zero) (Ext≈ eq x) = x
apply-sub-eq-tm (Var (suc i)) (Ext≈ eq x) = apply-sub-eq-tm (Var i) eq
apply-sub-eq-tm {A = ⋆} {B = ⋆} (Coh T C τ) eq = Coh≈ refl≈ty (apply-sub-eq-sub τ eq)
apply-sub-eq-tm {A = ⋆} {B = s ─⟨ B ⟩⟶ t} (Coh T C τ) eq with sub-eq-implies-ty-eq eq
... | ()
apply-sub-eq-tm {A = s ─⟨ A ⟩⟶ t} {B = ⋆} (Coh T C τ) eq with sub-eq-implies-ty-eq eq
... | ()
apply-sub-eq-tm {A = s ─⟨ A ⟩⟶ t} {B = s₁ ─⟨ B ⟩⟶ t₁} (Coh Δ C τ) eq = apply-sub-eq-tm (Coh (susp-ctx Δ) (susp-ty C) (susp-sub τ)) (↓-≈ eq)

apply-sub-eq-sub ⟨ _ ⟩′ eq = Null≈ (sub-eq-implies-ty-eq eq)
apply-sub-eq-sub ⟨ μ , t ⟩ eq = Ext≈ (apply-sub-eq-sub μ eq) (apply-sub-eq-tm t eq)
