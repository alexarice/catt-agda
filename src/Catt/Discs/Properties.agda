module Catt.Discs.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Discs

disc-≡ : .(d ≡ d′) → Disc d ≃c Disc d′
disc-≡ p with recompute (_ ≟ _) p
... | refl = refl≃c

disc-susp : (n : ℕ) → susp-ctx (Disc n) ≃c Disc (suc n)
sphere-susp : (n : ℕ) → susp-ctx (Sphere n) ≃c Sphere (suc n)
sphere-type-susp : (n : ℕ) → susp-ty (sphere-type n) ≃ty sphere-type (suc n)

disc-susp zero = refl≃c
disc-susp (suc n) = Add≃ (sphere-susp (suc n)) (sphere-type-susp (suc n))

sphere-susp zero = refl≃c
sphere-susp (suc n) = Add≃ (disc-susp n) (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n)))

sphere-type-susp zero = refl≃ty
sphere-type-susp (suc n) = Arr≃ (refl≃tm) (trans≃ty (susp-ty-lift (lift-ty (sphere-type n))) (lift-ty-≃ (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n))))) (refl≃tm)

sub-from-sphere-prop : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → sphere-type d [ sub-from-sphere d A p ]ty ≃ty A
sub-from-sphere-prop zero ⋆ p = refl≃ty
sub-from-sphere-prop (suc d) (s ─⟨ A ⟩⟶ t) p = Arr≃ refl≃tm (trans≃ty (lift-sub-comp-lem-ty ⟨ sub-from-sphere d A (cong pred p) , s ⟩ (lift-ty (sphere-type _))) (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere d A (cong pred p)) (sphere-type _)) (sub-from-sphere-prop d A (cong pred p)))) refl≃tm

sub-from-disc-≃ : (d₁ d₂ : ℕ) → A ≃ty B → .(p : ty-dim A ≡ d₁) → .(q : ty-dim B ≡ d₂) → s ≃tm t → sub-from-disc d₁ A p s ≃s sub-from-disc d₂ B q t
sub-from-sphere-≃ : (d₁ d₂ : ℕ) → A ≃ty B → .(p : ty-dim A ≡ d₁) → .(q : ty-dim B ≡ d₂) → sub-from-sphere d₁ A p ≃s sub-from-sphere d₂ B q

sub-from-disc-≃ d₁ d₂ a b c d = Ext≃ (sub-from-sphere-≃ d₁ d₂ a b c) d

sub-from-sphere-≃ zero zero (Star≃ x) p q = Null≃ (Star≃ x)
sub-from-sphere-≃ (suc d₁) (suc d₂) (Arr≃ a b c) p q = Ext≃ (Ext≃ (sub-from-sphere-≃ d₁ d₂ b (cong pred p) (cong pred q)) a) c

sub-from-sphere-sub : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (σ : Sub n m ⋆) → sub-from-sphere d (A [ σ ]ty) (trans (sym (sub-dim σ A)) p) ≃s (σ ● sub-from-sphere d A p)
sub-from-sphere-sub zero ⋆ p σ = refl≃s
sub-from-sphere-sub (suc d) (s ─⟨ A ⟩⟶ t) p σ = Ext≃ (Ext≃ (sub-from-sphere-sub d A (cong pred p) σ) refl≃tm) refl≃tm

sub-from-disc-sub : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (s : Tm n) → (σ : Sub n m ⋆) → sub-from-disc d (A [ σ ]ty) (trans (sym (sub-dim σ A)) p) (s [ σ ]tm) ≃s σ ● sub-from-disc d A p s
sub-from-disc-sub d A p s σ = Ext≃ (sub-from-sphere-sub d A p σ) refl≃tm

identity-≃ : n ≡ m → σ ≃s τ → identity n σ ≃tm identity m τ
identity-≃ refl p = Coh≃ refl≃c refl≃ty p

identity-term-≃ : A ≃ty B → s ≃tm t → identity-term A s ≃tm identity-term B t
identity-term-≃ p q = identity-≃ (ty-dim-≃ p) (sub-from-disc-≃ (ty-dim _) (ty-dim _) p refl refl q)

lift-sub-from-sphere : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → lift-sub (sub-from-sphere d A p) ≃s sub-from-sphere d (lift-ty A) (trans (lift-ty-dim A) p)
lift-sub-from-sphere zero ⋆ p = refl≃s
lift-sub-from-sphere (suc d) (s ─⟨ A ⟩⟶ t) p = Ext≃ (Ext≃ (lift-sub-from-sphere d A (cong pred p)) refl≃tm) refl≃tm

lift-sub-from-disc : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (t : Tm n) → lift-sub (sub-from-disc d A p t) ≃s sub-from-disc d (lift-ty A) (trans (lift-ty-dim A) p) (lift-tm t)
lift-sub-from-disc d A p t = Ext≃ (lift-sub-from-sphere d A p) refl≃tm

susp-sub-from-sphere : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → susp-sub (sub-from-sphere d A p) ≃s sub-from-sphere (suc d) (susp-ty A) (trans (susp-dim A) (cong suc p))
susp-sub-from-sphere zero ⋆ p = refl≃s
susp-sub-from-sphere (suc d) (s ─⟨ A ⟩⟶ t) p = Ext≃ (Ext≃ (susp-sub-from-sphere d A (cong pred p)) refl≃tm) refl≃tm

susp-sub-from-disc : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (t : Tm n) → susp-sub (sub-from-disc d A p t) ≃s sub-from-disc (suc d) (susp-ty A) (trans (susp-dim A) (cong suc p)) (susp-tm t)
susp-sub-from-disc d A p t = Ext≃ (susp-sub-from-sphere d A p) refl≃tm

sub-from-sphere-type-dim : (σ : Sub (sphere-size n) m ⋆) → ty-dim (sub-from-sphere-type σ) ≡ n
sub-from-sphere-type-dim {n = zero} σ = refl
sub-from-sphere-type-dim {n = suc n} ⟨ ⟨ σ , s ⟩ , t ⟩ = cong suc (sub-from-sphere-type-dim σ)

prop-sub-from-sphere : (σ : Sub (sphere-size n) m ⋆) → σ ≃s sub-from-sphere n (sub-from-sphere-type σ) (sub-from-sphere-type-dim σ)
prop-sub-from-sphere {n = zero} ⟨⟩ = refl≃s
prop-sub-from-sphere {n = suc n} ⟨ ⟨ σ , s ⟩ , t ⟩ = Ext≃ (Ext≃ (prop-sub-from-sphere σ) refl≃tm) refl≃tm

sub-from-disc-type-dim : (σ : Sub (disc-size n) m ⋆) → ty-dim (sub-from-disc-type σ) ≡ n
sub-from-disc-type-dim ⟨ σ , t ⟩ = sub-from-sphere-type-dim σ

prop-sub-from-disc : (σ : Sub (disc-size n) m ⋆) → σ ≃s sub-from-disc n (sub-from-disc-type σ) (sub-from-disc-type-dim σ) (sub-from-disc-term σ)
prop-sub-from-disc ⟨ σ , t ⟩ = Ext≃ (prop-sub-from-sphere σ) refl≃tm

sub-from-disc-term-unrestrict : (σ : Sub (disc-size n) m (s ─⟨ A ⟩⟶ t)) → sub-from-disc-term (unrestrict σ) ≃tm sub-from-disc-term σ
sub-from-disc-term-unrestrict ⟨ σ , t ⟩ = refl≃tm

sub-from-sphere-type-unrestrict : (σ : Sub (sphere-size n) m (s ─⟨ A ⟩⟶ t)) → sub-from-sphere-type (unrestrict σ) ≃ty sub-from-sphere-type σ
sub-from-sphere-type-unrestrict {n = zero} ⟨⟩ = refl≃ty
sub-from-sphere-type-unrestrict {n = suc n} ⟨ ⟨ σ , s ⟩ , t ⟩ = Arr≃ refl≃tm (sub-from-sphere-type-unrestrict σ) refl≃tm

sub-from-disc-type-unrestrict : (σ : Sub (disc-size n) m (s ─⟨ A ⟩⟶ t)) → sub-from-disc-type (unrestrict σ) ≃ty sub-from-disc-type σ
sub-from-disc-type-unrestrict ⟨ σ , t ⟩ = sub-from-sphere-type-unrestrict σ

identity-term-sub : (A : Ty m) → (s : Tm m) → (σ : Sub m l ⋆) → identity-term A s [ σ ]tm ≃tm identity-term (A [ σ ]ty) (s [ σ ]tm)
identity-term-sub A s σ = begin
  < identity-term A s [ σ ]tm >tm
    ≈⟨ sub-action-≃-tm (identity-≃ (sub-dim σ A) (sub-from-disc-≃ (ty-dim A) (ty-dim (A [ σ ]ty)) refl≃ty refl (sub-dim σ A) (refl≃tm {s = s}))) (refl≃s {σ = σ}) ⟩
  < (identity (ty-dim (A [ σ ]ty)) (σ ● sub-from-disc (ty-dim (A [ σ ]ty)) A _ s)) >tm
    ≈˘⟨ identity-≃ refl (sub-from-disc-sub (ty-dim (A [ σ ]ty)) A (sub-dim σ A) s σ) ⟩
  < identity-term (A [ σ ]ty) (s [ σ ]tm) >tm ∎
  where open Reasoning tm-setoid
