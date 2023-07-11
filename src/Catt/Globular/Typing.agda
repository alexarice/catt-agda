open import Catt.Typing.Rule

module Catt.Globular.Typing {index : Set}
                            (rule : index → Rule)
                            (lift-rule : ∀ i → LiftRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Typing.Properties.Lifting rule lift-rule
open import Catt.Typing.Properties.Base rule
open import Catt.Globular
open import Catt.Globular.Properties

tm-to-ty-prop : Typing-Tm Γ t A → tm-to-ty Γ t ≈[ Γ ]ty A
tm-to-ty-prop (TyConv tty p) = trans≈ty (tm-to-ty-prop tty) p
tm-to-ty-prop (TyVar i) = refl≈ty
tm-to-ty-prop (TyCoh v w) = refl≈ty

tm-to-ty-Ty : Typing-Tm Γ t A → Typing-Tm Γ t (tm-to-ty Γ t)
tm-to-ty-Ty (TyConv tty p) = tm-to-ty-Ty tty
tm-to-ty-Ty (TyVar i) = TyVar i
tm-to-ty-Ty (TyCoh v w) = TyCoh v w

Ty-unique : Typing-Tm Γ t A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique tty1 tty2 = trans≈ty (sym≈ty (tm-to-ty-prop tty1)) (tm-to-ty-prop tty2)

Ty-unique-≃ : s ≃tm t → Typing-Tm Γ s A → Typing-Tm Γ t B → A ≈[ Γ ]ty B
Ty-unique-≃ p tty tty2 with ≃tm-to-≡ p
... | refl = Ty-unique tty tty2

tm-height-is-ty-dim : Typing-Tm Δ t A → tm-height Δ t ≡ ty-dim A
tm-height-is-ty-dim tty = ≈ty-preserve-height (tm-to-ty-prop tty)

sub-tm-height : (t : Tm n) → (Γ : Ctx n) → {σ : Sub n m A} → Typing-Sub Γ Δ σ → tm-height Γ t + ty-dim A ≡ tm-height Δ (t [ σ ]tm)
sub-tm-height {A = A} {Δ = Δ} (Var zero) (Γ , B) (TyExt {σ = σ} {t = t} σty x) = begin
  ty-dim (lift-ty B) + ty-dim A
    ≡⟨ cong (_+ ty-dim A) (lift-ty-dim B) ⟩
  ty-dim B + ty-dim A
    ≡⟨ sub-dim′ σ B ⟩
  ty-dim (B [ σ ]ty)
    ≡˘⟨ tm-height-is-ty-dim x ⟩
  tm-height Δ (Var zero [ ⟨ σ , t ⟩ ]tm) ∎
  where
    open ≡-Reasoning
sub-tm-height {A = A} (Var (suc i)) (Γ , B) (TyExt {σ = σ} {t = t} σty x) = begin
  ty-dim (lift-ty (Γ ‼ i)) + ty-dim A
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
  ty-dim (B [ σ ● τ ]ty)
    ≡˘⟨ cong ty-dim (≃ty-to-≡ (tm-to-ty-coh-sub S B τ _ σ)) ⟩
  tm-height _ (Coh S B τ [ σ ]tm) ∎
  where
    open ≡-Reasoning

sub-tm-height-0 : (t : Tm n) → (Γ : Ctx n) → {σ : Sub n m ⋆} → Typing-Sub Γ Δ σ → tm-height Γ t ≡ tm-height Δ (t [ σ ]tm)
sub-tm-height-0 t Γ σty = trans (sym (+-identityʳ _)) (sub-tm-height t Γ σty)

ty-src-Ty : Typing-Ty Γ A → .⦃ _ : NonZero (ty-dim A) ⦄ → Typing-Tm Γ (ty-src A) (ty-base A)
ty-src-Ty (TyArr sty Aty tty) = sty

ty-tgt-Ty : Typing-Ty Γ A → .⦃ _ : NonZero (ty-dim A) ⦄ → Typing-Tm Γ (ty-tgt A) (ty-base A)
ty-tgt-Ty (TyArr sty Aty tty) = tty

ty-base-Ty : Typing-Ty Γ A → .⦃ _ : NonZero (ty-dim A) ⦄ → Typing-Ty Γ (ty-base A)
ty-base-Ty (TyArr sty Aty tty) = Aty

ty-tgt′-Ty : Typing-Ty Γ A → .⦃ _ : NonZero (ty-dim A) ⦄ → Typing-Tm Γ (ty-tgt′ A) (ty-base A)
ty-tgt′-Ty (TyArr sty Aty tty) = tty

ty-src-≈ : (p : A ≈[ Γ ]ty B) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-src A ≈[ Γ ]tm ty-src B ⦃ NonZero-subst (ty-dim-≈ p) it ⦄
ty-src-≈ Star≈ = refl≈tm
ty-src-≈ (Arr≈ p q r) = p

ty-tgt-≈ : (p : A ≈[ Γ ]ty B) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-tgt A ≈[ Γ ]tm ty-tgt B ⦃ NonZero-subst (ty-dim-≈ p) it ⦄
ty-tgt-≈ Star≈ = refl≈tm
ty-tgt-≈ (Arr≈ p q r) = r

ty-base-≈ : A ≈[ Γ ]ty B → ty-base A ≈[ Γ ]ty ty-base B
ty-base-≈ Star≈ = refl≈ty
ty-base-≈ (Arr≈ p q r) = q
