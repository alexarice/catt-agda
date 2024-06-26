open import Catt.Typing.Rule

module Catt.Typing.Properties.Preservation (ops : Op)
                                           (rules : RuleSet)
                                           (sub-cond : SubCond ops rules)
                                           (supp-cond : SupportCond ops rules)
                                           (pres-cond : PresCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Substitution ops rules sub-cond
open import Catt.Globular.Typing ops rules
open import Catt.Typing.Properties.Support ops rules supp-cond

open import Function.Bundles
open import Function.Construct.Identity
open import Function.Construct.Composition
open import Function.Construct.Symmetry

module E = Equivalence

term-preservation′ : s ≈[ Γ ]tm t → Typing-Tm Γ s A ⇔ Typing-Tm Γ t A
type-preservation′ : A ≈[ Γ ]ty B → Typing-Ty Γ A ⇔ Typing-Ty Γ B
sub-preservation′ : σ ≈[ Δ ]s τ → Typing-Sub Γ Δ σ ⇔ Typing-Sub Γ Δ τ
full-term-pres′ : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → Typing-Tm Γ s A ⇔ Typing-Tm Γ t B

term-preservation′ (Var≈ x)  with toℕ-injective x
... | refl = ⇔-id _
term-preservation′ (Sym≈ p) = ⇔-sym (term-preservation′ p)
term-preservation′ (Trans≈ p q) = term-preservation′ q ⇔-∘ term-preservation′ p
term-preservation′ {A = C} (Coh≈ {A = A} {Δ = Δ} {B = B} {σ = σ} {Γ = Γ} {τ = τ} p q) = mk⇔ (f C) (g C)
  where
    f : ∀ C → Typing-Tm Γ (Coh Δ A σ) C → Typing-Tm Γ (Coh Δ B τ) C
    f C (TyConv tty p) = TyConv (f _ tty) p
    f C (TyCoh supp Aty σty) = TyConv (TyCoh ⦃ nz = NonZero-subst (ty-dim-≈ p) it ⦄
                                             (subst₂ (ops Δ)
                                                     (EqSuppTm (ty-src-≈ p))
                                                     (EqSuppTm (ty-tgt-≈ p))
                                                     supp)
                                             (E.to (type-preservation′ p) Aty)
                                             (E.to (sub-preservation′ q) σty))
                                      lem
      where
        open Reasoning (ty-setoid-≈ Γ)
        lem : (B [ τ ]ty) ≈[ Γ ]ty A [ σ ]ty
        lem = begin
          B [ τ ]ty
            ≈˘⟨ apply-sub-eq-ty B q ⟩
          B [ σ ]ty
            ≈˘⟨ apply-sub-ty-eq σty p ⟩
          A [ σ ]ty ∎

    g : ∀ C → Typing-Tm Γ (Coh Δ B τ) C → Typing-Tm Γ (Coh Δ A σ) C
    g C (TyConv tty p) = TyConv (g _ tty) p
    g C (TyCoh supp Bty τty) = TyConv (TyCoh ⦃ nz = NonZero-subst (sym (ty-dim-≈ p)) it ⦄
                                             (subst₂ (ops Δ)
                                                     (EqSuppTm (ty-src-≈ (sym≈ty p)))
                                                     (EqSuppTm (ty-tgt-≈ (sym≈ty p)))
                                                     supp)
                                             (E.from (type-preservation′ p) Bty)
                                             (E.from (sub-preservation′ q) τty))
                                             lem
      where
        open Reasoning (ty-setoid-≈ Γ)
        lem : (A [ σ ]ty) ≈[ Γ ]ty B [ τ ]ty
        lem = begin
          A [ σ ]ty
            ≈⟨ apply-sub-eq-ty A q ⟩
          A [ τ ]ty
            ≈⟨ apply-sub-ty-eq τty p ⟩
          B [ τ ]ty ∎

term-preservation′ (Rule≈ r p tty) = mk⇔ f g
  where
    open Rule r
    f : Typing-Tm tgtCtx lhs _ →
          Typing-Tm tgtCtx rhs _
    f tty′ = pres-cond p tty′

    g : Typing-Tm tgtCtx rhs _ →
          Typing-Tm tgtCtx lhs _
    g tty′ = TyConv tty (Ty-unique (pres-cond p tty) tty′)

type-preservation′ Star≈ = ⇔-id (Typing-Ty _ ⋆)
type-preservation′ (Arr≈ p q r) = mk⇔ f g
  where
    f : Typing-Ty _ (_ ─⟨ _ ⟩⟶ _) → Typing-Ty _ (_ ─⟨ _ ⟩⟶ _)
    f (TyArr sty Aty tty) = TyArr (E.to (full-term-pres′ p q) sty)
                                  (E.to (type-preservation′ q) Aty)
                                  (E.to (full-term-pres′ r q) tty)

    g : Typing-Ty _ (_ ─⟨ _ ⟩⟶ _) → Typing-Ty _ (_ ─⟨ _ ⟩⟶ _)
    g (TyArr sty Aty tty) = TyArr (E.from (full-term-pres′ p q) sty)
                                  (E.from (type-preservation′ q) Aty)
                                  (E.from (full-term-pres′ r q) tty)

sub-preservation′ (Null≈ x) = mk⇔ (λ where (TyNull y) → TyNull (E.to (type-preservation′ x) y))
                                (λ where (TyNull y) → TyNull (E.from (type-preservation′ x) y))
sub-preservation′ (Ext≈ p x) = mk⇔ f g
  where
    f : Typing-Sub _ _ ⟨ _ , _ ⟩ → Typing-Sub _ _ ⟨ _ , _ ⟩
    f (TyExt {A = A} σty tty) = TyExt (E.to (sub-preservation′ p) σty)
                                      (E.to (full-term-pres′ x (apply-sub-eq-ty A p)) tty)

    g : Typing-Sub _ _ ⟨ _ , _ ⟩ → Typing-Sub _ _ ⟨ _ , _ ⟩
    g (TyExt {A = A} σty tty) = TyExt (E.from (sub-preservation′ p) σty)
                                      (E.from (full-term-pres′ x (apply-sub-eq-ty A p)) tty)

full-term-pres′ p eq = (term-preservation′ p) ⇔-∘ (mk⇔ (λ tty → TyConv tty eq) (λ tty → TyConv tty (sym≈ty eq)))

type-preservation : A ≈[ Γ ]ty B → Typing-Ty Γ A → Typing-Ty Γ B
sub-preservation : σ ≈[ Δ ]s τ → Typing-Sub Γ Δ σ → Typing-Sub Γ Δ τ
term-preservation : s ≈[ Γ ]tm t → Typing-Tm Γ s A → Typing-Tm Γ t A
full-term-pres : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → Typing-Tm Γ s A → Typing-Tm Γ t B

type-preservation p = E.to (type-preservation′ p)

sub-preservation p = E.to (sub-preservation′ p)

term-preservation p = E.to (term-preservation′ p)

full-term-pres p q = E.to (full-term-pres′ p q)

Ty-unique-≈ : s ≈[ Γ ]tm t → Typing-Tm Γ s A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique-≈ p sty tty = Ty-unique (term-preservation p sty) tty
