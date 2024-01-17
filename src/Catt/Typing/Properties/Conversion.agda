open import Catt.Typing.Rule
open import Catt.Typing.Rule.Typed

module Catt.Typing.Properties.Conversion (rules : RuleSet)
                                         (tame : Tame rules)
                                         (conv-rule : ConvCond rules rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax

open import Catt.Typing rules
open import Catt.Typing.Properties rules tame
open import Catt.Globular.Typing rules lift-cond

open import Function.Bundles
open import Function.Construct.Identity
open import Function.Construct.Composition
open import Function.Construct.Symmetry

module E = Equivalence

term-conversion′ : s ≈[ Γ ]tm t → Typing-Tm Γ s A ⇔ Typing-Tm Γ t A
type-conversion′ : A ≈[ Γ ]ty B → Typing-Ty Γ A ⇔ Typing-Ty Γ B
sub-conversion′ : σ ≈[ Δ ]s τ → Typing-Sub Γ Δ σ ⇔ Typing-Sub Γ Δ τ
full-term-conv′ : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → Typing-Tm Γ s A ⇔ Typing-Tm Γ t B

term-conversion′ (Var≈ x)  with toℕ-injective x
... | refl = ⇔-id _
term-conversion′ (Sym≈ p) = ⇔-sym (term-conversion′ p)
term-conversion′ (Trans≈ p q) = term-conversion′ q ⇔-∘ term-conversion′ p
term-conversion′ {A = C} (Coh≈ {A = A} {Δ = Δ} {B = B} {σ = σ} {Γ = Γ} {τ = τ} p q) = mk⇔ (f C) (g C)
  where
    f : ∀ C → Typing-Tm Γ (Coh Δ A σ) C → Typing-Tm Γ (Coh Δ B τ) C
    f C (TyConv tty p) = TyConv (f _ tty) p
    f C (TyCoh Aty σty) = TyConv (TyCoh (E.to (type-conversion′ p) Aty)
                                   (E.to (sub-conversion′ q) σty))
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
    g C (TyCoh Bty τty) = TyConv (TyCoh (E.from (type-conversion′ p) Bty)
                                     (E.from (sub-conversion′ q) τty))
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

term-conversion′ (Rule≈ r p tty) = mk⇔ f g
  where
    open Rule r
    f : Typing-Tm tgtCtx lhs _ →
          Typing-Tm tgtCtx rhs _
    f tty′ = conv-rule p tty′

    g : Typing-Tm tgtCtx rhs _ →
          Typing-Tm tgtCtx lhs _
    g tty′ = TyConv tty (Ty-unique (conv-rule p tty) tty′)

type-conversion′ Star≈ = ⇔-id (Typing-Ty _ ⋆)
type-conversion′ (Arr≈ p q r) = mk⇔ f g
  where
    f : Typing-Ty _ (_ ─⟨ _ ⟩⟶ _) → Typing-Ty _ (_ ─⟨ _ ⟩⟶ _)
    f (TyArr sty Aty tty) = TyArr (E.to (full-term-conv′ p q) sty)
                                  (E.to (type-conversion′ q) Aty)
                                  (E.to (full-term-conv′ r q) tty)

    g : Typing-Ty _ (_ ─⟨ _ ⟩⟶ _) → Typing-Ty _ (_ ─⟨ _ ⟩⟶ _)
    g (TyArr sty Aty tty) = TyArr (E.from (full-term-conv′ p q) sty)
                                  (E.from (type-conversion′ q) Aty)
                                  (E.from (full-term-conv′ r q) tty)

sub-conversion′ (Null≈ x) = mk⇔ (λ where (TyNull y) → TyNull (E.to (type-conversion′ x) y))
                                (λ where (TyNull y) → TyNull (E.from (type-conversion′ x) y))
sub-conversion′ (Ext≈ p x) = mk⇔ f g
  where
    f : Typing-Sub _ _ ⟨ _ , _ ⟩ → Typing-Sub _ _ ⟨ _ , _ ⟩
    f (TyExt {A = A} σty tty) = TyExt (E.to (sub-conversion′ p) σty)

                                    (E.to (full-term-conv′ x (apply-sub-eq-ty A p)) tty)

    g : Typing-Sub _ _ ⟨ _ , _ ⟩ → Typing-Sub _ _ ⟨ _ , _ ⟩
    g (TyExt {A = A} σty tty) = TyExt (E.from (sub-conversion′ p) σty)

                                    (E.from (full-term-conv′ x (apply-sub-eq-ty A p)) tty)

full-term-conv′ p eq = (term-conversion′ p) ⇔-∘ (mk⇔ (λ tty → TyConv tty eq) (λ tty → TyConv tty (sym≈ty eq)))

type-conversion : A ≈[ Γ ]ty B → Typing-Ty Γ A → Typing-Ty Γ B
sub-conversion : σ ≈[ Δ ]s τ → Typing-Sub Γ Δ σ → Typing-Sub Γ Δ τ
full-term-conv : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → Typing-Tm Γ s A → Typing-Tm Γ t B

type-conversion p = E.to (type-conversion′ p)

sub-conversion p = E.to (sub-conversion′ p)

full-term-conv p q = E.to (full-term-conv′ p q)
