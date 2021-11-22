{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.Properties.Conversion (index : ℕ)
                                         (rule : Fin index → Rule)
                                         (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                         (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                         (sub-rule : ∀ i a → P.SubRule index rule {i} a)
                                         (supp-rule : ∀ i a → P.SupportRule index rule {i} a)
                                         (conv-rule : ∀ i a → P.ConvRule index rule {i} a) where

open import Catt.Syntax
open import Catt.Typing index rule
open import Catt.Typing.Properties.Support index rule supp-rule
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing index rule lift-rule
open import Data.Fin.Properties using (toℕ-injective)
open import Relation.Binary.PropositionalEquality
open import Function
open import Function.Construct.Identity
open import Function.Construct.Composition
open import Function.Construct.Symmetry
import Relation.Binary.Reasoning.Setoid as Reasoning

module E = Equivalence

term-conversion′ : s ≈[ Γ ]tm t → Typing-Tm Γ s A ⇔ Typing-Tm Γ t A
type-conversion′ : A ≈[ Γ ]ty B → Typing-Ty Γ A ⇔ Typing-Ty Γ B
sub-conversion′ : σ ≈[ Δ ]s τ → Typing-Sub Γ Δ σ ⇔ Typing-Sub Γ Δ τ
full-term-conv′ : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → Typing-Tm Γ s A ⇔ Typing-Tm Γ t B

term-conversion′ (Var≈ x)  with toℕ-injective x
... | refl = id-⇔ _
term-conversion′ (Sym≈ p) = sym-⇔ (term-conversion′ p)
term-conversion′ (Trans≈ p q) = (term-conversion′ p) ∘-⇔ (term-conversion′ q)
term-conversion′ (Coh≈ {A = A} {B = B} {σ = σ} {Γ = Γ} {τ = τ} p q) = mk⇔ f g
  where
    f : Typing-Tm _ (Coh _ _ _) _ → Typing-Tm _ (Coh _ _ _) _
    f (TyCoh {B = C} Aty σty b sc x) = TyCoh (E.f (type-conversion′ p) Aty)
                                     (E.f (sub-conversion′ q) σty)
                                     b
                                     (supp-condition-preserved b p Aty (E.f (type-conversion′ p) Aty) sc)
                                     lem
      where
        open Reasoning (ty-setoid-≈ Γ)
        lem : (B [ τ ]ty) ≈[ Γ ]ty C
        lem = begin
          B [ τ ]ty
            ≈˘⟨ apply-sub-eq-ty B q ⟩
          B [ σ ]ty
            ≈˘⟨ apply-sub-ty-eq σty p ⟩
          A [ σ ]ty
            ≈⟨ x ⟩
          C ∎

    g : Typing-Tm _ (Coh _ _ _) _ → Typing-Tm _ (Coh _ _ _) _
    g (TyCoh {B = C} Bty τty b sc x) = TyCoh (E.g (type-conversion′ p) Bty)
                                     (E.g (sub-conversion′ q) τty)
                                     b
                                     (supp-condition-preserved b (sym≈ty p) Bty (E.g (type-conversion′ p) Bty) sc)
                                     lem
      where
        open Reasoning (ty-setoid-≈ Γ)
        lem : (A [ σ ]ty) ≈[ Γ ]ty C
        lem = begin
          A [ σ ]ty
            ≈⟨ apply-sub-eq-ty A q ⟩
          A [ τ ]ty
            ≈⟨ apply-sub-ty-eq τty p ⟩
          B [ τ ]ty
            ≈⟨ x ⟩
          C ∎

term-conversion′ (Rule≈ i a tty) = mk⇔ f g
  where
    f : Typing-Tm (rule i .Rule.tgtCtx a) (rule i .Rule.lhs a) _ →
          Typing-Tm (rule i .Rule.tgtCtx a) (rule i .Rule.rhs a) _
    f tty′ = conv-rule i a tty′

    g : Typing-Tm (rule i .Rule.tgtCtx a) (rule i .Rule.rhs a) _ →
          Typing-Tm (rule i .Rule.tgtCtx a) (rule i .Rule.lhs a) _
    g tty′ = term-conversion tty (Ty-unique (conv-rule i a tty) tty′)

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
    f (TyExt {A = A} σty Aty tty) = TyExt (E.f (sub-conversion′ p) σty)
                                    Aty
                                    (E.f (full-term-conv′ x (apply-sub-eq-ty A p)) tty)

    g : Typing-Sub _ _ ⟨ _ , _ ⟩ → Typing-Sub _ _ ⟨ _ , _ ⟩
    g (TyExt {A = A} σty Aty tty) = TyExt (E.g (sub-conversion′ p) σty)
                                    Aty
                                    (E.g (full-term-conv′ x (apply-sub-eq-ty A p)) tty)

full-term-conv′ p eq = (term-conversion′ p) ∘-⇔ (mk⇔ (λ tty → term-conversion tty eq) (λ tty → term-conversion tty (sym≈ty eq)))

type-conversion : A ≈[ Γ ]ty B → Typing-Ty Γ A → Typing-Ty Γ B
sub-conversion : σ ≈[ Δ ]s τ → Typing-Sub Γ Δ σ → Typing-Sub Γ Δ τ
full-term-conv : s ≈[ Γ ]tm t → A ≈[ Γ ]ty B → Typing-Tm Γ s A → Typing-Tm Γ t B

type-conversion p = E.f (type-conversion′ p)

sub-conversion p = E.f (sub-conversion′ p)

full-term-conv p q = E.f (full-term-conv′ p q)
