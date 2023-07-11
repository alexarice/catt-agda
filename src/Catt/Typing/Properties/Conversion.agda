open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Typing.Properties.Conversion {index : Set}
                                         (rule : index → Rule)
                                         (lift-rule : ∀ i → P.LiftRule rule (rule i))
                                         (susp-rule : ∀ i → P.SuspRule rule (rule i))
                                         (sub-rule : ∀ i → P.SubRule rule (rule i))
                                         (supp-rule : ∀ i → P.SupportRule rule (rule i))
                                         (conv-rule : ∀ i → P.ConvRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Typing rule
open import Catt.Typing.Properties.Support rule supp-rule
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing rule lift-rule
open import Function
open import Function.Construct.Identity
open import Function.Construct.Composition
open import Function.Construct.Symmetry

module E = Equivalence

term-conversion′ : s ≈[ Γ ]tm t → Typing-Tm Γ s A ⇔ Typing-Tm Γ t A
type-conversion′ : A ≈[ Γ ]ty B → Typing-Ty Γ A ⇔ Typing-Ty Γ B
sub-conversion′ : σ ≈[ Δ ]s τ → Typing-Sub Γ Δ σ ⇔ Typing-Sub Γ Δ τ
full-term-conv′ : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → Typing-Tm Γ s A ⇔ Typing-Tm Γ t B

term-conversion′ (Var≈ x)  with toℕ-injective x
... | refl = id-⇔ _
term-conversion′ (Sym≈ p) = sym-⇔ (term-conversion′ p)
term-conversion′ (Trans≈ p q) = (term-conversion′ p) ∘-⇔ (term-conversion′ q)
term-conversion′ {A = C} (Coh≈ {A = A} {Δ = Δ} {B = B} {σ = σ} {Γ = Γ} {τ = τ} p q) = mk⇔ (f C) (g C)
  where
    f : ∀ C → Typing-Tm Γ (Coh Δ A σ) C → Typing-Tm Γ (Coh Δ B τ) C
    f C (TyConv tty p) = TyConv (f _ tty) p
    f C (TyCoh Aty σty) = TyConv (TyCoh (E.f (type-conversion′ p) Aty)
                                   (E.f (sub-conversion′ q) σty))
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
    g C (TyCoh Bty τty) = TyConv (TyCoh (E.g (type-conversion′ p) Bty)
                                     (E.g (sub-conversion′ q) τty))
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

term-conversion′ (Rule≈ i tty) = mk⇔ f g
  where
    f : Typing-Tm (rule i .Rule.tgtCtx) (rule i .Rule.lhs) _ →
          Typing-Tm (rule i .Rule.tgtCtx) (rule i .Rule.rhs) _
    f tty′ = conv-rule i tty′

    g : Typing-Tm (rule i .Rule.tgtCtx) (rule i .Rule.rhs) _ →
          Typing-Tm (rule i .Rule.tgtCtx) (rule i .Rule.lhs) _
    g tty′ = TyConv tty (Ty-unique (conv-rule i tty) tty′)

type-conversion′ Star≈ = id-⇔ (Typing-Ty _ ⋆)
type-conversion′ (Arr≈ p q r) = mk⇔ f g
  where
    f : Typing-Ty _ (_ ─⟨ _ ⟩⟶ _) → Typing-Ty _ (_ ─⟨ _ ⟩⟶ _)
    f (TyArr sty Aty tty) = TyArr (E.f (full-term-conv′ p q) sty)
                                  (E.f (type-conversion′ q) Aty)
                                  (E.f (full-term-conv′ r q) tty)

    g : Typing-Ty _ (_ ─⟨ _ ⟩⟶ _) → Typing-Ty _ (_ ─⟨ _ ⟩⟶ _)
    g (TyArr sty Aty tty) = TyArr (E.g (full-term-conv′ p q) sty)
                                  (E.g (type-conversion′ q) Aty)
                                  (E.g (full-term-conv′ r q) tty)

sub-conversion′ (Null≈ x) = mk⇔ (λ where (TyNull y) → TyNull (E.f (type-conversion′ x) y))
                                (λ where (TyNull y) → TyNull (E.g (type-conversion′ x) y))
sub-conversion′ (Ext≈ p x) = mk⇔ f g
  where
    f : Typing-Sub _ _ ⟨ _ , _ ⟩ → Typing-Sub _ _ ⟨ _ , _ ⟩
    f (TyExt {A = A} σty tty) = TyExt (E.f (sub-conversion′ p) σty)

                                    (E.f (full-term-conv′ x (apply-sub-eq-ty A p)) tty)

    g : Typing-Sub _ _ ⟨ _ , _ ⟩ → Typing-Sub _ _ ⟨ _ , _ ⟩
    g (TyExt {A = A} σty tty) = TyExt (E.g (sub-conversion′ p) σty)

                                    (E.g (full-term-conv′ x (apply-sub-eq-ty A p)) tty)

full-term-conv′ p eq = (term-conversion′ p) ∘-⇔ (mk⇔ (λ tty → TyConv tty eq) (λ tty → TyConv tty (sym≈ty eq)))

type-conversion : A ≈[ Γ ]ty B → Typing-Ty Γ A → Typing-Ty Γ B
sub-conversion : σ ≈[ Δ ]s τ → Typing-Sub Γ Δ σ → Typing-Sub Γ Δ τ
full-term-conv : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → Typing-Tm Γ s A → Typing-Tm Γ t B

type-conversion p = E.f (type-conversion′ p)

sub-conversion p = E.f (sub-conversion′ p)

full-term-conv p q = E.f (full-term-conv′ p q)
