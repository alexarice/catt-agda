module Catt.Dyck.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Wedge
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Dyck

infix 4 _≃d_
data _≃d_ : Dyck n d → Dyck n′ d′ → Set where
  ⊝≃ : ⊝ ≃d ⊝
  ⇑≃ : dy ≃d ey → ⇑ dy ≃d ⇑ ey
  ⇓≃ : dy ≃d ey → ⇓ dy ≃d ⇓ ey

refl≃d : dy ≃d dy
refl≃d {dy = ⊝} = ⊝≃
refl≃d {dy = ⇑ dy} = ⇑≃ refl≃d
refl≃d {dy = ⇓ dy} = ⇓≃ refl≃d

sym≃d : dy ≃d ey → ey ≃d dy
sym≃d ⊝≃ = ⊝≃
sym≃d (⇑≃ p) = ⇑≃ (sym≃d p)
sym≃d (⇓≃ p) = ⇓≃ (sym≃d p)

trans≃d : dy ≃d ey → ey ≃d fy → dy ≃d fy
trans≃d ⊝≃ ⊝≃ = ⊝≃
trans≃d (⇑≃ p) (⇑≃ q) = ⇑≃ (trans≃d p q)
trans≃d (⇓≃ p) (⇓≃ q) = ⇓≃ (trans≃d p q)

reflexive≃d : dy ≡ ey → dy ≃d ey
reflexive≃d refl = refl≃d

≃d-to-≡ : dy ≃d ey → dy ≡ ey
≃d-to-≡ ⊝≃ = refl
≃d-to-≡ (⇑≃ p) = cong ⇑ (≃d-to-≡ p)
≃d-to-≡ (⇓≃ p) with ≃d-to-≡ p
... | refl = refl

record DYCK : Set where
  constructor <_>d
  field
    {dyck-n} : ℕ
    {dyck-d} : ℕ
    dyck : Dyck dyck-n dyck-d

open DYCK public

dyck-setoid : Setoid _ _
dyck-setoid = record { Carrier = DYCK
                     ; _≈_ = λ x y → dyck x ≃d dyck y
                     ; isEquivalence = record { refl = refl≃d
                                              ; sym = sym≃d
                                              ; trans = trans≃d
                                              }
                     }


wedge-dyck-≃ : {gy : Dyck n d} → (p : dy ≃d ey) → fy ≃d gy → wedge-dyck dy fy ≃d wedge-dyck ey gy
wedge-dyck-≃ p ⊝≃ = p
wedge-dyck-≃ p (⇑≃ q) = ⇑≃ (wedge-dyck-≃ p q)
wedge-dyck-≃ p (⇓≃ q) = ⇓≃ (wedge-dyck-≃ p q)

susp-dyck-≃ : dy ≃d ey → susp-dyck dy ≃d susp-dyck ey
susp-dyck-≃ ⊝≃ = refl≃d
susp-dyck-≃ (⇑≃ p) = ⇑≃ (susp-dyck-≃ p)
susp-dyck-≃ (⇓≃ p) = ⇓≃ (susp-dyck-≃ p)

dyck-pre-type-dim : (dy : Dyck n d) → ty-dim (dyck-pre-type dy) ≡ d
dyck-type-dim : (dy : Dyck n d) → ty-dim (dyck-type dy) ≡ d

dyck-pre-type-dim ⊝ = refl
dyck-pre-type-dim (⇑ dy) = cong suc (trans (wk-ty-dim (dyck-type dy)) (dyck-type-dim dy))
dyck-pre-type-dim (⇓ dy) = trans (ty-dim-ty-base (dyck-pre-type dy)) (cong pred (dyck-pre-type-dim dy))

dyck-type-dim d = trans (wk-ty-dim (dyck-pre-type d)) (dyck-pre-type-dim d)

dyck-dim-to-ctx : (dy : Dyck n d) → ctx-dim ⌊ dy ⌋d ≡ dyck-dim dy
dyck-dim-to-ctx ⊝ = refl
dyck-dim-to-ctx (⇑ {d = d} dy) = begin
  ctx-dim ⌊ dy ⌋d ⊔ ty-dim (dyck-type dy) ⊔ suc (ty-dim (wk-ty (dyck-type dy)))
    ≡⟨ cong₃ (λ a b c → a ⊔ b ⊔ suc c)
             (dyck-dim-to-ctx dy)
             (dyck-type-dim dy)
             (trans (wk-ty-dim (dyck-type dy)) (dyck-type-dim dy)) ⟩
  dyck-dim dy ⊔ d ⊔ suc d
    ≡⟨ ⊔-assoc (dyck-dim dy) d (suc d) ⟩
  dyck-dim dy ⊔ (d ⊔ suc d)
    ≡⟨ cong (dyck-dim dy ⊔_) (m≤n⇒m⊔n≡n (n≤1+n d)) ⟩
  dyck-dim dy ⊔ suc d ∎
  where
    open ≡-Reasoning
dyck-dim-to-ctx (⇓ dy) = dyck-dim-to-ctx dy

dyck-zero-lem : ¬ (Dyck zero (suc d))
dyck-zero-lem (⇓ dy) = dyck-zero-lem dy

≃d-to-same-n : {dy : Dyck n d} → {ey : Dyck m d′} → dy ≃d ey → n ≡ m
≃d-to-same-n ⊝≃ = refl
≃d-to-same-n (⇑≃ p) = cong suc (≃d-to-same-n p)
≃d-to-same-n (⇓≃ p) = ≃d-to-same-n p

≃d-to-same-d : {dy : Dyck n d} → {ey : Dyck m d′} → dy ≃d ey → d ≡ d′
≃d-to-same-d ⊝≃ = refl
≃d-to-same-d (⇑≃ p) = cong suc (≃d-to-same-d p)
≃d-to-same-d (⇓≃ p) = cong pred (≃d-to-same-d p)

dyck-pre-type-≃ : dy ≃d ey → dyck-pre-type dy ≃ty dyck-pre-type ey
dyck-type-≃ : dy ≃d ey → dyck-type dy ≃ty dyck-type ey
dyck-term-≃ : dy ≃d ey → dyck-term dy ≃tm dyck-term ey

dyck-pre-type-≃ ⊝≃ = refl≃ty
dyck-pre-type-≃ (⇑≃ p) = Arr≃ (wk-tm-≃ (dyck-term-≃ p)) (wk-ty-≃ (dyck-type-≃ p)) (Var≃ (cong (λ - → 2 + - * 2) (≃d-to-same-n p)) refl)
dyck-pre-type-≃ (⇓≃ p) = ty-base-≃ (dyck-pre-type-≃ p)

dyck-type-≃ p = wk-ty-≃ (dyck-pre-type-≃ p)

dyck-term-≃ ⊝≃ = refl≃tm
dyck-term-≃ (⇑≃ p) = Var≃ (cong (λ - → 3 + - * 2) (≃d-to-same-n p)) refl
dyck-term-≃ (⇓≃ p) = ty-tgt′-≃ (dyck-type-≃ p)

⌊⌋d-≃ : dy ≃d ey → ⌊ dy ⌋d ≃c ⌊ ey ⌋d
⌊⌋d-≃ ⊝≃ = refl≃c
⌊⌋d-≃ (⇑≃ p) = Add≃ (Add≃ (⌊⌋d-≃ p) (dyck-type-≃ p)) (dyck-pre-type-≃ (⇑≃ p))
⌊⌋d-≃ (⇓≃ p) = ⌊⌋d-≃ p

susp-dyck-pre-type : (d : Dyck n d) → dyck-pre-type (susp-dyck d) ≃ty susp-ty (dyck-pre-type d)
susp-dyck-type : (d : Dyck n d) → dyck-type (susp-dyck d) ≃ty susp-ty (dyck-type d)
susp-dyck-term : (d : Dyck n d) → dyck-term (susp-dyck d) ≃tm susp-tm (dyck-term d)

susp-dyck-pre-type ⊝ = refl≃ty
susp-dyck-pre-type (⇑ d)
  = Arr≃ (trans≃tm (wk-tm-≃ (susp-dyck-term d)) (sym≃tm (susp-tm-wk (dyck-term d))))
         (trans≃ty (wk-ty-≃ (susp-dyck-type d)) (sym≃ty (susp-ty-wk (dyck-type d))))
         refl≃tm
susp-dyck-pre-type (⇓ d) = trans≃ty (ty-base-≃ (susp-dyck-pre-type d)) (ty-base-susp (dyck-pre-type d) ⦃ NonZero-subst (sym (dyck-pre-type-dim d)) it ⦄)

susp-dyck-type d = begin
  < dyck-type (susp-dyck d) >ty
    ≈⟨ wk-ty-≃ (susp-dyck-pre-type d) ⟩
  < wk-ty (susp-ty (dyck-pre-type d)) >ty
    ≈˘⟨ susp-ty-wk (dyck-pre-type d) ⟩
  < susp-ty (dyck-type d) >ty ∎
  where
    open Reasoning ty-setoid

susp-dyck-term ⊝ = refl≃tm
susp-dyck-term (⇑ d) = refl≃tm
susp-dyck-term (⇓ d) = trans≃tm (ty-tgt′-≃ (susp-dyck-type d)) (ty-tgt′-susp (dyck-type d) ⦃ NonZero-subst (sym (dyck-type-dim d)) it ⦄)

susp-⌊⌋d : (d : Dyck n d) → ⌊ susp-dyck d ⌋d ≃c susp-ctx ⌊ d ⌋d
susp-⌊⌋d ⊝ = refl≃c
susp-⌊⌋d (⇑ d)
  = Add≃ (Add≃ (susp-⌊⌋d d) (susp-dyck-type d))
         (susp-dyck-pre-type (⇑ d))
susp-⌊⌋d (⇓ d) = susp-⌊⌋d d

susp-peak-term : (p : Peak dy) → peak-term (susp-peak p) ≃tm susp-tm (peak-term p)
susp-peak-term (⇕pk dy) = refl≃tm
susp-peak-term (⇑pk p) = begin
  < wk-tm (wk-tm (peak-term (susp-peak p))) >tm
    ≈⟨ wk-tm-≃ (wk-tm-≃ (susp-peak-term p)) ⟩
  < wk-tm (wk-tm (susp-tm (peak-term p))) >tm
    ≈˘⟨ wk-tm-≃ (susp-tm-wk (peak-term p)) ⟩
  < wk-tm (susp-tm (wk-tm (peak-term p))) >tm
    ≈˘⟨ susp-tm-wk (wk-tm (peak-term p)) ⟩
  < susp-tm (peak-term (⇑pk p)) >tm ∎
  where
    open Reasoning tm-setoid
susp-peak-term (⇓pk p) = susp-peak-term p

dyck-0-is-0-d : (dy : Dyck 0 (suc d)) → ⊥
dyck-0-is-0-d (⇓ dy) = dyck-0-is-0-d dy

wedge-dyck-pre-type : (dy : Dyck n 0) → (ey : Dyck (suc m) d)
                    → dyck-pre-type (wedge-dyck dy ey)
                      ≃ty
                      dyck-pre-type ey [ wedge-inc-right (dyck-term dy) _ ]ty
wedge-dyck-type : (dy : Dyck n 0) → (ey : Dyck m d)
                → dyck-type (wedge-dyck dy ey)
                  ≃ty
                  dyck-type ey [ wedge-inc-right (dyck-term dy) _ ]ty
wedge-dyck-term : (dy : Dyck n 0) → (ey : Dyck m d)
                → dyck-term (wedge-dyck dy ey)
                  ≃tm
                  dyck-term ey [ wedge-inc-right (dyck-term dy) _ ]tm

wedge-dyck-pre-type {n = n} {m = m} dy (⇑ ey)
  = Arr≃ l1 l2 (Var≃ (cong 2+ (*-distribʳ-+ 2 m n)) refl)
  where
    l1 : wk-tm (dyck-term (wedge-dyck dy ey))
         ≃tm
         wk-tm (dyck-term ey) [ wedge-inc-right (dyck-term dy) _ ]tm
    l1 = begin
      < wk-tm (dyck-term (wedge-dyck dy ey)) >tm
        ≈⟨ wk-tm-≃ (wedge-dyck-term dy ey) ⟩
      < wk-tm (dyck-term ey [ wedge-inc-right (dyck-term dy) _ ]tm) >tm
        ≈˘⟨ apply-wk-sub-tm-≃ (dyck-term ey) (wedge-inc-right (dyck-term dy) _) ⟩
      < dyck-term ey [ wk-sub (wedge-inc-right (dyck-term dy) _) ]tm >tm
        ≈˘⟨ apply-sub-wk-tm-≃ (dyck-term ey) (wedge-inc-right (dyck-term dy) _) ⟩
      < wk-tm (dyck-term ey) [ wedge-inc-right (dyck-term dy) _ ]tm >tm ∎
     where
       open Reasoning tm-setoid

    l2 : wk-ty (dyck-type (wedge-dyck dy ey))
         ≃ty
         wk-ty (dyck-type ey) [ wedge-inc-right (dyck-term dy) _ ]ty
    l2 = begin
      < wk-ty (dyck-type (wedge-dyck dy ey)) >ty
        ≈⟨ wk-ty-≃ (wedge-dyck-type dy ey) ⟩
      < wk-ty (dyck-type ey [ wedge-inc-right (dyck-term dy) _ ]ty) >ty
        ≈˘⟨ apply-wk-sub-ty-≃ (dyck-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
      < dyck-type ey [ wk-sub (wedge-inc-right (dyck-term dy) _) ]ty >ty
        ≈˘⟨ apply-sub-wk-ty-≃ (dyck-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
      < wk-ty (dyck-type ey) [ wedge-inc-right (dyck-term dy) _ ]ty >ty ∎
      where
        open Reasoning ty-setoid
wedge-dyck-pre-type dy (⇓ ey) = begin
  < ty-base (dyck-pre-type (wedge-dyck dy ey)) >ty
    ≈⟨ ty-base-≃ (wedge-dyck-pre-type dy ey) ⟩
  < ty-base (dyck-pre-type ey [ wedge-inc-right (dyck-term dy) _ ]ty) >ty
    ≈˘⟨ ty-base-sub (dyck-pre-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
  < ty-base (dyck-pre-type ey) [ wedge-inc-right (dyck-term dy) _ ]ty >ty ∎
  where
    open Reasoning ty-setoid

wedge-dyck-type {m = zero} dy ⊝ = ⋆-is-only-0-d-ty ⦃ IsZero-subst (sym (dyck-type-dim dy)) it ⦄
wedge-dyck-type {m = zero} dy (⇓ ey) = ⊥-elim (dyck-0-is-0-d ey)
wedge-dyck-type {m = suc m} dy ey = begin
  < dyck-type (wedge-dyck dy ey) >ty
    ≈⟨ wk-ty-≃ (wedge-dyck-pre-type dy ey) ⟩
  < wk-ty (dyck-pre-type ey [ wedge-inc-right (dyck-term dy) _ ]ty) >ty
    ≈˘⟨ apply-wk-sub-ty-≃ (dyck-pre-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
  < dyck-pre-type ey [ wk-sub (wedge-inc-right (dyck-term dy) _) ]ty >ty
    ≈˘⟨ apply-sub-wk-ty-≃ (dyck-pre-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
  < dyck-type ey [ wedge-inc-right (dyck-term dy) _ ]ty >ty ∎
  where
    open Reasoning ty-setoid

wedge-dyck-term dy ⊝ = refl≃tm
wedge-dyck-term {n = n} dy (⇑ {n = m} ey) = Var≃ (cong (3 +_) (*-distribʳ-+ 2 m n)) refl
wedge-dyck-term dy (⇓ ey) = begin
  < ty-tgt′ (dyck-type (wedge-dyck dy ey)) >tm
    ≈⟨ ty-tgt′-≃ (wedge-dyck-type dy ey) ⟩
  < ty-tgt′ (dyck-type ey [ wedge-inc-right (dyck-term dy) _ ]ty) >tm
    ≈˘⟨ ty-tgt′-sub (dyck-type ey) (wedge-inc-right (dyck-term dy) _) ⦃ NonZero-subst (sym (dyck-type-dim ey)) it ⦄ ⟩
  < ty-tgt′ (dyck-type ey) [ wedge-inc-right (dyck-term dy) _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

wedge-⌊⌋d : (dy : Dyck n 0) → (ey : Dyck m d) → ⌊ wedge-dyck dy ey ⌋d ≃c wedge ⌊ dy ⌋d (dyck-term dy) ⌊ ey ⌋d
wedge-⌊⌋d dy ⊝ = refl≃c
wedge-⌊⌋d dy (⇑ ey)
  = Add≃ (Add≃ (wedge-⌊⌋d dy ey) (wedge-dyck-type dy ey)) (wedge-dyck-pre-type dy (⇑ ey))
wedge-⌊⌋d dy (⇓ ey)
  = wedge-⌊⌋d dy ey
