module Catt.Globular.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree

tm-to-ty-≃ : Γ ≃c Δ → s ≃tm t → tm-to-ty Γ s ≃ty tm-to-ty Δ t
tm-to-ty-≃ p (Var≃ x y) = ‼-≃ _ _ y p
tm-to-ty-≃ p (Coh≃ q r s) = sub-action-≃-ty r s

sub-dim : (σ : Sub n m ⋆) → (A : Ty n) → ty-dim A ≡ ty-dim (A [ σ ]ty)
sub-dim σ ⋆ = refl
sub-dim σ (s ─⟨ A ⟩⟶ t) = cong suc (sub-dim σ A)

sub-dim′ : (σ : Sub n m B) → (A : Ty n) → ty-dim A + ty-dim B ≡ ty-dim (A [ σ ]ty)
sub-dim′ σ ⋆ = refl
sub-dim′ σ (s ─⟨ A ⟩⟶ t) = cong suc (sub-dim′ σ A)

ty-dim-≃ : A ≃ty B → ty-dim A ≡ ty-dim B
ty-dim-≃ (Star≃ x) = refl
ty-dim-≃ (Arr≃ _ p _) = cong suc (ty-dim-≃ p)

susp-dim : (A : Ty n) → ty-dim (susp-ty A) ≡ suc (ty-dim A)
susp-dim ⋆ = refl
susp-dim (s ─⟨ A ⟩⟶ t) = cong suc (susp-dim A)

susp-ctx-dim : (Γ : Ctx n) → .⦃ NonZero n ⦄ → ctx-dim (susp-ctx Γ) ≡ suc (ctx-dim Γ)
susp-ctx-dim (∅ , A) = susp-dim A
susp-ctx-dim (Γ , B , A) = cong₂ _⊔_ (susp-ctx-dim (Γ , B)) (susp-dim A)

connect-ctx-dim : (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m)) → ctx-dim (connect Γ t Δ) ≡ ctx-dim Γ ⊔ ctx-dim Δ
connect-ctx-dim Γ t (∅ , ⋆) = sym (⊔-identityʳ (ctx-dim Γ))
connect-ctx-dim Γ t (∅ , s ─⟨ A ⟩⟶ t₁) = ⊥-elim (no-term-in-empty-context s)
connect-ctx-dim Γ t (Δ , B , A) = begin
  ctx-dim (connect Γ t (Δ , B)) ⊔ ty-dim (A [ connect-inc-right t (ctxLength Δ) ]ty)
    ≡⟨ cong₂ _⊔_ (connect-ctx-dim Γ t (Δ , B)) (sym (sub-dim (connect-inc-right t (ctxLength Δ)) A)) ⟩
  ctx-dim Γ ⊔ ctx-dim (Δ , B) ⊔ ty-dim A
    ≡⟨ ⊔-assoc (ctx-dim Γ) (ctx-dim (Δ , B)) (ty-dim A) ⟩
  ctx-dim Γ ⊔ (ctx-dim (Δ , B) ⊔ ty-dim A) ∎
  where
    open ≡-Reasoning

connect-susp-ctx-dim : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → ctx-dim (connect-susp Γ Δ) ≡ suc (ctx-dim Γ) ⊔ ctx-dim Δ
connect-susp-ctx-dim Γ Δ = begin
  ctx-dim (connect-susp Γ Δ)
    ≡⟨ connect-ctx-dim (susp-ctx Γ) get-snd Δ ⟩
  ctx-dim (susp-ctx Γ) ⊔ ctx-dim Δ
    ≡⟨ cong (_⊔ ctx-dim Δ) (susp-ctx-dim Γ) ⟩
  suc (ctx-dim Γ) ⊔ ctx-dim Δ ∎
  where
    open ≡-Reasoning

tree-dim-ctx-dim : (T : Tree n) → ctx-dim (tree-to-ctx T) ≡ tree-dim T
tree-dim-ctx-dim Sing = refl
tree-dim-ctx-dim (Join S T) = begin
  ctx-dim (connect-susp (tree-to-ctx S) (tree-to-ctx T))
    ≡⟨ connect-susp-ctx-dim (tree-to-ctx S) (tree-to-ctx T) ⟩
  suc (ctx-dim (tree-to-ctx S)) ⊔ ctx-dim (tree-to-ctx T)
    ≡⟨ cong₂ (λ a → suc a ⊔_) (tree-dim-ctx-dim S) (tree-dim-ctx-dim T) ⟩
  suc (tree-dim S) ⊔ tree-dim T
    ≡⟨ ⊔-lem (tree-dim S) (tree-dim T) ⟩
  suc (pred (tree-dim T) ⊔ tree-dim S) ∎
  where
    open ≡-Reasoning

lift-ty-dim : (A : Ty n) → ty-dim (lift-ty A) ≡ ty-dim A
lift-ty-dim ⋆ = refl
lift-ty-dim (s ─⟨ A ⟩⟶ t) = cong suc (lift-ty-dim A)

ty-dim-ty-base : (A : Ty n) → ty-dim (ty-base A) ≡ pred (ty-dim A)
ty-dim-ty-base ⋆ = refl
ty-dim-ty-base (s ─⟨ A ⟩⟶ t) = refl

tm-to-ty-coh-sub : (Δ : Ctx (suc n)) → (B : Ty (suc n)) → (τ : Sub (suc n) m ⋆) → (Γ : Ctx l) → (σ : Sub m l A) → tm-to-ty Γ (Coh Δ B τ [ σ ]tm) ≃ty B [ σ ● τ ]ty
tm-to-ty-coh-sub {A = ⋆} Δ B τ Γ σ = refl≃ty
tm-to-ty-coh-sub {A = s ─⟨ A ⟩⟶ t} Δ B τ Γ σ = begin
  < tm-to-ty Γ (Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ unrestrict σ ]tm) >ty
    ≈⟨ tm-to-ty-coh-sub (susp-ctx Δ) (susp-ty B) (susp-sub τ) Γ (unrestrict σ) ⟩
  < susp-ty B [ unrestrict σ ● susp-sub τ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (refl≃ty {A = susp-ty B}) (unrestrict-comp σ τ) ⟩
  < susp-ty B [ unrestrict (σ ● τ) ]ty >ty
    ≈⟨ unrestrict-comp-ty B (σ ● τ) ⟩
  < B [ σ ● τ ]ty >ty ∎
  where
    open Reasoning ty-setoid

susp-tm-height : (t : Tm n) → (Δ : Ctx n) → tm-height (susp-ctx Δ) (susp-tm t) ≡ suc (tm-height Δ t)
susp-tm-height (Var zero) (Δ , A) = begin
  ty-dim (lift-ty (susp-ty A))
    ≡⟨ lift-ty-dim (susp-ty A) ⟩
  ty-dim (susp-ty A)
    ≡⟨ susp-dim A ⟩
  suc (ty-dim A)
    ≡˘⟨ cong suc (lift-ty-dim A) ⟩
  suc (ty-dim (lift-ty A)) ∎
  where
    open ≡-Reasoning
susp-tm-height (Var (suc i)) (Δ , A) = begin
  ty-dim (lift-ty (susp-ctx Δ ‼ inject₁ (inject₁ i)))
    ≡⟨ lift-ty-dim (susp-ctx Δ ‼ inject₁ (inject₁ i)) ⟩
  ty-dim (susp-ctx Δ ‼ inject₁ (inject₁ i))
    ≡⟨ susp-tm-height (Var i) Δ ⟩
  suc (ty-dim (Δ ‼ i))
    ≡˘⟨ cong suc (lift-ty-dim (Δ ‼ i)) ⟩
  suc (ty-dim (lift-ty (Δ ‼ i))) ∎
  where
    open ≡-Reasoning
susp-tm-height (Coh S A σ) Δ = begin
  ty-dim (susp-ty A [ susp-sub σ ]ty)
    ≡˘⟨ cong ty-dim (≃ty-to-≡ (susp-functorial-ty σ A)) ⟩
  ty-dim (susp-ty (A [ σ ]ty))
    ≡⟨ susp-dim (A [ σ ]ty) ⟩
  suc (ty-dim (A [ σ ]ty)) ∎
  where
    open ≡-Reasoning

tm-height-≃ : (Γ : Ctx n) → s ≃tm t → tm-height Γ s ≡ tm-height Γ t
tm-height-≃ Γ p with ≃tm-to-≡ p
... | refl = refl

ty-src-≃ : (p : A ≃ty B) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-src A ≃tm ty-src B ⦃ NonZero-subst (ty-dim-≃ p) it ⦄
ty-src-≃ (Arr≃ p q r) = p

ty-tgt-≃ : (p : A ≃ty B) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-tgt A ≃tm ty-tgt B ⦃ NonZero-subst (ty-dim-≃ p) it ⦄
ty-tgt-≃ (Arr≃ p q r) = r

ty-base-≃ : A ≃ty B → ty-base A ≃ty ty-base B
ty-base-≃ (Star≃ p) = Star≃ p
ty-base-≃ (Arr≃ p q r) = q

ty-src′-≃ : A ≃ty B → ty-src′ A ≃tm ty-src′ B
ty-src′-≃ (Star≃ p) = Var≃ p refl
ty-src′-≃ (Arr≃ p q r) = p

ty-tgt′-≃ : A ≃ty B → ty-tgt′ A ≃tm ty-tgt′ B
ty-tgt′-≃ (Star≃ p) = Var≃ p refl
ty-tgt′-≃ (Arr≃ p q r) = r

ty-base-lift : (A : Ty n) → ty-base (lift-ty A) ≃ty lift-ty (ty-base A)
ty-base-lift ⋆ = refl≃ty
ty-base-lift (s ─⟨ A ⟩⟶ t) = refl≃ty

ty-base-sub : (A : Ty n) → (σ : Sub n m ⋆) → ty-base A [ σ ]ty ≃ty ty-base (A [ σ ]ty)
ty-base-sub ⋆ σ = refl≃ty
ty-base-sub (s ─⟨ A ⟩⟶ t) σ = refl≃ty

ty-src-sub : (A : Ty n) → (σ : Sub n m ⋆) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-src A [ σ ]tm ≃tm ty-src (A [ σ ]ty) ⦃ NonZero-subst (sub-dim σ A) it ⦄
ty-src-sub (s ─⟨ A ⟩⟶ t) σ = refl≃tm

ty-tgt-sub : (A : Ty n) → (σ : Sub n m ⋆) → .⦃ _ : NonZero (ty-dim A) ⦄ → ty-tgt A [ σ ]tm ≃tm ty-tgt (A [ σ ]ty) ⦃ NonZero-subst (sub-dim σ A) it ⦄
ty-tgt-sub (s ─⟨ A ⟩⟶ t) σ = refl≃tm

ty-src′-sub : (A : Ty (suc n)) → (σ : Sub (suc n) (suc m) ⋆) → .⦃ NonZero (ty-dim A) ⦄ → ty-src′ A [ σ ]tm ≃tm ty-src′ (A [ σ ]ty)
ty-src′-sub (s ─⟨ A ⟩⟶ t) σ = refl≃tm

ty-tgt′-sub : (A : Ty (suc n)) → (σ : Sub (suc n) (suc m) ⋆) → .⦃ NonZero (ty-dim A) ⦄ → ty-tgt′ A [ σ ]tm ≃tm ty-tgt′ (A [ σ ]ty)
ty-tgt′-sub (s ─⟨ A ⟩⟶ t) σ = refl≃tm

ty-base-dim : (A : Ty n) → ty-dim (ty-base A) ≡ pred (ty-dim A)
ty-base-dim ⋆ = refl
ty-base-dim (s ─⟨ A ⟩⟶ t) = refl

truncate-≤ : (d : ℕ) → (A : Ty n) → d ≤ ty-dim A → truncate d (s ─⟨ A ⟩⟶ t) ≃ty truncate d A
truncate-≤ d A p
  rewrite +-∸-assoc 1 p = refl≃ty

susp-ty-truncate : (A : Ty n) → truncate 1 (susp-ty A) ≃ty get-fst {n = n} ─⟨ ⋆ ⟩⟶ get-snd
susp-ty-truncate ⋆ = refl≃ty
susp-ty-truncate (s ─⟨ A ⟩⟶ t) = trans≃ty (truncate-≤ 1 (susp-ty A) (≤-trans (s≤s z≤n) (≤-reflexive (sym (susp-dim A))))) (susp-ty-truncate A)

truncate′-≃ : d ≡ d′ → A ≃ty A′ → truncate′ d A ≃ty truncate′ d′ A′
truncate′-≃ {d = zero} refl p = p
truncate′-≃ {d = suc d} refl p = truncate′-≃ {d = d} refl (ty-base-≃ p)

truncate-≃ : d ≡ d′ → A ≃ty A′ → truncate d A ≃ty truncate d′ A′
truncate-≃ {d} {d′} {A = A} {A′ = A′} refl p = truncate′-≃ {d = ty-dim A ∸ d} {d′ = ty-dim A′ ∸ d} (cong (_∸ d) (≃ty-preserve-height p)) p

truncate′-sub : (d : ℕ) → (A : Ty n) → (σ : Sub n m B) → d ≤ ty-dim A → truncate′ d (A [ σ ]ty) ≃ty truncate′ d A [ σ ]ty
truncate′-sub zero A σ p = refl≃ty
truncate′-sub (suc d) (s ─⟨ A ⟩⟶ t) σ p = truncate′-sub d A σ (≤-pred p)

truncate-sub : (d : ℕ) → (A : Ty n) → (σ : Sub n m B) → truncate (d + ty-dim B) (A [ σ ]ty) ≃ty truncate d A [ σ ]ty
truncate-sub {B = B} d A σ = begin
  < truncate (d + ty-dim B) (A [ σ ]ty) >ty ≡⟨⟩
  < truncate′ (ty-dim (A [ σ ]ty) ∸ (d + ty-dim B)) (A [ σ ]ty) >ty
    ≈⟨ truncate′-≃ lem refl≃ty ⟩
  < truncate′ (ty-dim A ∸ d) (A [ σ ]ty) >ty
    ≈⟨ truncate′-sub (ty-dim A ∸ d) A σ (m∸n≤m (ty-dim A) d) ⟩
  < truncate′ (ty-dim A ∸ d) A [ σ ]ty >ty ≡⟨⟩
  < truncate d A [ σ ]ty >ty ∎
  where
    lem : ty-dim (A [ σ ]ty) ∸ (d + ty-dim B) ≡ ty-dim A ∸ d
    lem = begin
      ty-dim (A [ σ ]ty) ∸ (d + ty-dim B)
        ≡˘⟨ cong₂ _∸_ (sub-dim′ σ A) (+-comm (ty-dim B) d) ⟩
      ty-dim A + ty-dim B ∸ (ty-dim B + d)
        ≡˘⟨ ∸-+-assoc (ty-dim A + ty-dim B) (ty-dim B) d ⟩
      ty-dim A + ty-dim B ∸ ty-dim B ∸ d
        ≡⟨ cong (_∸ d) (+-∸-assoc (ty-dim A) {n = ty-dim B} ≤-refl) ⟩
      ty-dim A + (ty-dim B ∸ ty-dim B) ∸ d
        ≡⟨ cong (λ - → ty-dim A + - ∸ d) (n∸n≡0 (ty-dim B)) ⟩
      ty-dim A + 0 ∸ d
        ≡⟨ cong (_∸ d) (+-identityʳ (ty-dim A)) ⟩
      ty-dim A ∸ d ∎
      where
        open ≡-Reasoning

    open Reasoning ty-setoid

truncate′-lift : (n : ℕ) → (A : Ty m) → truncate′ n (lift-ty A) ≃ty lift-ty (truncate′ n A)
truncate′-lift zero A = refl≃ty
truncate′-lift (suc n) A = trans≃ty (truncate′-≃ {d = n} refl (ty-base-lift A)) (truncate′-lift n (ty-base A))
