{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Globular.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open P index rule
open import Catt.Syntax
open import Catt.Globular
open import Catt.Globular.Properties
open import Relation.Binary.PropositionalEquality
open import Catt.Syntax.SyntacticEquality
open import Data.Nat.Properties
open import Catt.Support
open import Catt.Support.Properties
open import Data.Vec
open import Data.Bool using (false) renaming (T to Truth)
open import Data.Empty
open import Data.Sum

tm-to-ty-prop : Typing-Tm Γ t A → tm-to-ty Γ t ≈[ Γ ]ty A
tm-to-ty-prop (TyVarZ x y) = y
tm-to-ty-prop (TyVarS i tty x) = trans≈ty (lift-ty-equality (tm-to-ty-prop tty)) x
tm-to-ty-prop (TyCoh v w x y z) = z

tm-to-ty-Ty : Typing-Tm Γ t A → Typing-Tm Γ t (tm-to-ty Γ t)
tm-to-ty-Ty (TyVarZ x y) = TyVarZ x refl≈ty
tm-to-ty-Ty (TyVarS i tty x) = TyVarS i (tm-to-ty-Ty tty) refl≈ty
tm-to-ty-Ty (TyCoh v w x y z) = TyCoh v w x y refl≈ty

Ty-unique : Typing-Tm Γ t A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique (TyVarZ x y) (TyVarZ w z) = trans≈ty (sym≈ty y) z
Ty-unique (TyVarS _ tty x) (TyVarS _ tty2 y) = trans≈ty (trans≈ty (sym≈ty x) (lift-ty-equality (Ty-unique tty tty2))) y
Ty-unique (TyCoh _ _ _ _ x) (TyCoh _ _ _ _ y) = trans≈ty (sym≈ty x) y

Ty-unique-≃ : s ≃tm t → Typing-Tm Γ s A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique-≃ p tty tty2 with ≃tm-to-≡ p
... | refl = Ty-unique tty tty2

tm-height-is-ty-dim : Typing-Tm Δ t A → tm-height Δ t ≡ ty-dim A
tm-height-is-ty-dim tty = ≈ty-preserve-height (tm-to-ty-prop tty)

sub-tm-height : (t : Tm n) → (Γ : Ctx n) → {σ : Sub n m A} → Typing-Sub Γ Δ σ → tm-height Γ t + ty-dim A ≡ tm-height Δ (t [ σ ]tm)
sub-tm-height {A = A} {Δ = Δ} (Var zero) (Γ , B) (TyExt {σ = σ} {t = t} σty Aty x) = begin
  ty-dim (liftType B) + ty-dim A
    ≡⟨ cong (_+ ty-dim A) (lift-ty-dim B) ⟩
  ty-dim B + ty-dim A
    ≡⟨ sub-dim′ σ B ⟩
  ty-dim (B [ σ ]ty)
    ≡˘⟨ tm-height-is-ty-dim x ⟩
  tm-height Δ (Var zero [ ⟨ σ , t ⟩ ]tm) ∎
  where
    open ≡-Reasoning
sub-tm-height {A = A} (Var (suc i)) (Γ , B) (TyExt {σ = σ} {t = t} σty Aty x) = begin
  ty-dim (liftType (Γ ‼ i)) + ty-dim A
    ≡⟨ cong (_+ ty-dim A) (lift-ty-dim (Γ ‼ i)) ⟩
  ty-dim (Γ ‼ i) + ty-dim A
    ≡⟨ sub-tm-height (Var i) Γ σty ⟩
  tm-height _ (Var (suc i) [ ⟨ σ , t ⟩ ]tm) ∎
  where
    open ≡-Reasoning
sub-tm-height {A = A} (Coh S B τ) Γ {σ} σty = begin
  ty-dim (B [ τ ]ty) + ty-dim A
    ≡⟨ sub-dim′ σ (B [ τ ]ty) ⟩
  ty-dim ((B [ τ ]ty) [ σ ]ty)
    ≡˘⟨ cong ty-dim (≃ty-to-≡ (assoc-ty σ τ B)) ⟩
  ty-dim (B [ σ ∘ τ ]ty)
    ≡˘⟨ cong ty-dim (≃ty-to-≡ (tm-to-ty-coh-sub S B τ _ σ)) ⟩
  tm-height _ (Coh S B τ [ σ ]tm) ∎
  where
    open ≡-Reasoning

sub-tm-height-0 : (t : Tm n) → (Γ : Ctx n) → {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → tm-height Γ t ≡ tm-height Δ (t [ σ ]tm)
sub-tm-height-0 t Γ σty = trans (sym (+-identityʳ _)) (sub-tm-height t Γ σty)

-- ctx-dim : Ctx n → ℕ
-- ctx-dim ∅ = 0
-- ctx-dim (Γ , A) = ctx-dim Γ ⊔ ty-dim A

-- dim-from-support-ty : {A : Ty n} → Typing-Ty Γ A → (i : Fin n) → Truth (lookup (FVTy A) i) → ty-dim (Γ ‼ i) < ty-dim A
-- dim-from-support-tm : Typing-Tm Γ t A → (i : Fin n) → Truth (lookup (FVTm t) i) → ty-dim (Γ ‼ i) ≤ (ty-dim A)

-- lookup-empty : (i : Fin n) → lookup empty i ≡ false
-- lookup-empty zero = refl
-- lookup-empty (suc i) = lookup-empty i

-- dim-from-support-ty TyStar i truth = ⊥-elim (subst Truth (lookup-empty i) truth)
-- dim-from-support-ty (TyArr {s = s} {A = A} {t = t} sty Aty tty) i truth with ∪-Truth (FVTy A ∪ FVTm s) (FVTm t) i truth
-- ... | inj₂ y = s≤s (dim-from-support-tm tty i y)
-- ... | inj₁ x with ∪-Truth (FVTy A) (FVTm s) i x
-- ... | inj₁ z = ≤-trans (dim-from-support-ty Aty i z) (n≤1+n (ty-dim A))
-- ... | inj₂ y = s≤s (dim-from-support-tm sty i y)

-- dim-from-support-tm (TyVarZ x y) zero truth = ≤-reflexive (≈ty-preserve-height y)
-- dim-from-support-tm (TyVarZ x y) (suc i) truth = ⊥-elim (subst Truth (lookup-empty i) truth)
-- dim-from-support-tm (TyVarS j tty x) (suc i) truth = ≤-trans (≤-reflexive (lift-ty-dim _)) (≤-trans (dim-from-support-tm (tm-to-ty-Ty tty) i truth) (≤-reflexive (trans (≈ty-preserve-height (tm-to-ty-prop tty)) (trans (sym (lift-ty-dim _)) (≈ty-preserve-height x)))))
-- dim-from-support-tm (TyCoh {A = A} Aty σty b x₂ x₃) i truth = {!!}

-- Ty-is-Bounded-Tm : Typing-Tm Γ t A → BoundedTm (ty-dim A) Γ t
-- Ty-is-Bounded-Ty : Typing-Ty Γ A → BoundedTy (ty-dim A) Γ A
-- Ty-is-Bounded-Sub : Typing-Sub Γ Δ σ → BoundedSub (ctx-dim Γ) Δ σ

-- Ty-is-Bounded-Tm (TyVarZ x y) = VarBoundZ (subst (λ - → BoundedTy - _ _) (trans (sym (lift-ty-dim _)) (≈ty-preserve-height y)) (Ty-is-Bounded-Ty x))
-- Ty-is-Bounded-Tm (TyVarS i tty x) = VarBoundS i (subst (λ - → BoundedTm - _ _) (trans (sym (lift-ty-dim _)) (≈ty-preserve-height x)) (Ty-is-Bounded-Tm tty))
-- Ty-is-Bounded-Tm (TyCoh Aty σty b sc p)
--   = CohBound _
--              (subst (λ - → BoundedTy - _ _) (trans (sub-dim _ _) (≈ty-preserve-height p)) (Ty-is-Bounded-Ty Aty))
--              (subst (λ - → BoundedSub - _ _) {!!} (Ty-is-Bounded-Sub σty))

-- Ty-is-Bounded-Ty = {!!}

-- Ty-is-Bounded-Sub = {!!}

-- BoundedSubTm : {σ : Sub n m ⋆} → BoundedTm d Γ t → Typing-Sub Γ Δ σ → BoundedTm d Δ (t [ σ ]tm)

-- BoundedSubTm (VarBoundZ x) (TyExt σty Aty y) = {!!}
-- BoundedSubTm (VarBoundS i b) σty = {!!}
-- BoundedSubTm (CohBound S p q) σty = {!!}

ty-src-Ty : Typing-Ty Γ A → (ty-dim A > 0) → Typing-Tm Γ (ty-src A) (ty-base A)
ty-src-Ty (TyArr sty Aty tty) p = sty

ty-tgt-Ty : Typing-Ty Γ A → (ty-dim A > 0) → Typing-Tm Γ (ty-tgt A) (ty-base A)
ty-tgt-Ty (TyArr sty Aty tty) p = tty

ty-base-Ty : Typing-Ty Γ A → (ty-dim A > 0) → Typing-Ty Γ (ty-base A)
ty-base-Ty (TyArr sty Aty tty) p = Aty
