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
  End≃ : End ≃d End
  ⇑≃ : dy ≃d ey → ⇑ dy ≃d ⇑ ey
  ⇓≃ : dy ≃d ey → ⇓ dy ≃d ⇓ ey

refl≃d : dy ≃d dy
refl≃d {dy = End} = End≃
refl≃d {dy = ⇑ dy} = ⇑≃ refl≃d
refl≃d {dy = ⇓ dy} = ⇓≃ refl≃d

sym≃d : dy ≃d ey → ey ≃d dy
sym≃d End≃ = End≃
sym≃d (⇑≃ p) = ⇑≃ (sym≃d p)
sym≃d (⇓≃ p) = ⇓≃ (sym≃d p)

trans≃d : dy ≃d ey → ey ≃d fy → dy ≃d fy
trans≃d End≃ End≃ = End≃
trans≃d (⇑≃ p) (⇑≃ q) = ⇑≃ (trans≃d p q)
trans≃d (⇓≃ p) (⇓≃ q) = ⇓≃ (trans≃d p q)

reflexive≃d : dy ≡ ey → dy ≃d ey
reflexive≃d refl = refl≃d

≃d-to-≡ : dy ≃d ey → dy ≡ ey
≃d-to-≡ End≃ = refl
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
wedge-dyck-≃ p End≃ = p
wedge-dyck-≃ p (⇑≃ q) = ⇑≃ (wedge-dyck-≃ p q)
wedge-dyck-≃ p (⇓≃ q) = ⇓≃ (wedge-dyck-≃ p q)

susp-dyck-≃ : dy ≃d ey → susp-dyck dy ≃d susp-dyck ey
susp-dyck-≃ End≃ = refl≃d
susp-dyck-≃ (⇑≃ p) = ⇑≃ (susp-dyck-≃ p)
susp-dyck-≃ (⇓≃ p) = ⇓≃ (susp-dyck-≃ p)

dyck-pre-type-dim : (dy : Dyck n d) → ty-dim (dyck-pre-type dy) ≡ d
dyck-type-dim : (dy : Dyck n d) → ty-dim (dyck-type dy) ≡ d

dyck-pre-type-dim End = refl
dyck-pre-type-dim (⇑ dy) = cong suc (trans (lift-ty-dim (dyck-type dy)) (dyck-type-dim dy))
dyck-pre-type-dim (⇓ dy) = trans (ty-dim-ty-base (dyck-pre-type dy)) (cong pred (dyck-pre-type-dim dy))

dyck-type-dim d = trans (lift-ty-dim (dyck-pre-type d)) (dyck-pre-type-dim d)

dyck-zero-lem : ¬ (Dyck zero (suc d))
dyck-zero-lem (⇓ dy) = dyck-zero-lem dy

≃d-to-same-n : {dy : Dyck n d} → {ey : Dyck m d′} → dy ≃d ey → n ≡ m
≃d-to-same-n End≃ = refl
≃d-to-same-n (⇑≃ p) = cong suc (≃d-to-same-n p)
≃d-to-same-n (⇓≃ p) = ≃d-to-same-n p

≃d-to-same-d : {dy : Dyck n d} → {ey : Dyck m d′} → dy ≃d ey → d ≡ d′
≃d-to-same-d End≃ = refl
≃d-to-same-d (⇑≃ p) = cong suc (≃d-to-same-d p)
≃d-to-same-d (⇓≃ p) = cong pred (≃d-to-same-d p)

dyck-pre-type-≃ : dy ≃d ey → dyck-pre-type dy ≃ty dyck-pre-type ey
dyck-type-≃ : dy ≃d ey → dyck-type dy ≃ty dyck-type ey
dyck-term-≃ : dy ≃d ey → dyck-term dy ≃tm dyck-term ey

dyck-pre-type-≃ End≃ = refl≃ty
dyck-pre-type-≃ (⇑≃ p) = Arr≃ (lift-tm-≃ (dyck-term-≃ p)) (lift-ty-≃ (dyck-type-≃ p)) (Var≃ (cong (λ - → 2 + - * 2) (≃d-to-same-n p)) refl)
dyck-pre-type-≃ (⇓≃ p) = ty-base-≃ (dyck-pre-type-≃ p)

dyck-type-≃ p = lift-ty-≃ (dyck-pre-type-≃ p)

dyck-term-≃ End≃ = refl≃tm
dyck-term-≃ (⇑≃ p) = Var≃ (cong (λ - → 3 + - * 2) (≃d-to-same-n p)) refl
dyck-term-≃ (⇓≃ p) = ty-tgt′-≃ (dyck-type-≃ p)

⌊⌋d-≃ : dy ≃d ey → ⌊ dy ⌋d ≃c ⌊ ey ⌋d
⌊⌋d-≃ End≃ = refl≃c
⌊⌋d-≃ (⇑≃ p) = Add≃ (Add≃ (⌊⌋d-≃ p) (dyck-type-≃ p)) (dyck-pre-type-≃ (⇑≃ p))
⌊⌋d-≃ (⇓≃ p) = ⌊⌋d-≃ p

susp-dyck-pre-type : (d : Dyck n d) → dyck-pre-type (susp-dyck d) ≃ty susp-ty (dyck-pre-type d)
susp-dyck-type : (d : Dyck n d) → dyck-type (susp-dyck d) ≃ty susp-ty (dyck-type d)
susp-dyck-term : (d : Dyck n d) → dyck-term (susp-dyck d) ≃tm susp-tm (dyck-term d)

susp-dyck-pre-type End = refl≃ty
susp-dyck-pre-type (⇑ d)
  = Arr≃ (trans≃tm (lift-tm-≃ (susp-dyck-term d)) (sym≃tm (susp-tm-lift (dyck-term d))))
         (trans≃ty (lift-ty-≃ (susp-dyck-type d)) (sym≃ty (susp-ty-lift (dyck-type d))))
         refl≃tm
susp-dyck-pre-type (⇓ d) = trans≃ty (ty-base-≃ (susp-dyck-pre-type d)) (ty-base-susp (dyck-pre-type d) ⦃ NonZero-subst (sym (dyck-pre-type-dim d)) it ⦄)

susp-dyck-type d = begin
  < dyck-type (susp-dyck d) >ty
    ≈⟨ lift-ty-≃ (susp-dyck-pre-type d) ⟩
  < lift-ty (susp-ty (dyck-pre-type d)) >ty
    ≈˘⟨ susp-ty-lift (dyck-pre-type d) ⟩
  < susp-ty (dyck-type d) >ty ∎
  where
    open Reasoning ty-setoid

susp-dyck-term End = refl≃tm
susp-dyck-term (⇑ d) = refl≃tm
susp-dyck-term (⇓ d) = trans≃tm (ty-tgt′-≃ (susp-dyck-type d)) (ty-tgt′-susp (dyck-type d) ⦃ NonZero-subst (sym (dyck-type-dim d)) it ⦄)

susp-⌊⌋d : (d : Dyck n d) → ⌊ susp-dyck d ⌋d ≃c susp-ctx ⌊ d ⌋d
susp-⌊⌋d End = refl≃c
susp-⌊⌋d (⇑ d)
  = Add≃ (Add≃ (susp-⌊⌋d d) (susp-dyck-type d))
         (susp-dyck-pre-type (⇑ d))
susp-⌊⌋d (⇓ d) = susp-⌊⌋d d

susp-peak-term : (p : Peak dy) → peak-term (susp-peak p) ≃tm susp-tm (peak-term p)
susp-peak-term (⇕pk dy) = refl≃tm
susp-peak-term (⇑pk p) = begin
  < lift-tm (lift-tm (peak-term (susp-peak p))) >tm
    ≈⟨ lift-tm-≃ (lift-tm-≃ (susp-peak-term p)) ⟩
  < lift-tm (lift-tm (susp-tm (peak-term p))) >tm
    ≈˘⟨ lift-tm-≃ (susp-tm-lift (peak-term p)) ⟩
  < lift-tm (susp-tm (lift-tm (peak-term p))) >tm
    ≈˘⟨ susp-tm-lift (lift-tm (peak-term p)) ⟩
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
    l1 : lift-tm (dyck-term (wedge-dyck dy ey))
         ≃tm
         lift-tm (dyck-term ey) [ wedge-inc-right (dyck-term dy) _ ]tm
    l1 = begin
      < lift-tm (dyck-term (wedge-dyck dy ey)) >tm
        ≈⟨ lift-tm-≃ (wedge-dyck-term dy ey) ⟩
      < lift-tm (dyck-term ey [ wedge-inc-right (dyck-term dy) _ ]tm) >tm
        ≈˘⟨ apply-lifted-sub-tm-≃ (dyck-term ey) (wedge-inc-right (dyck-term dy) _) ⟩
      < dyck-term ey [ lift-sub (wedge-inc-right (dyck-term dy) _) ]tm >tm
        ≈˘⟨ apply-sub-lifted-tm-≃ (dyck-term ey) (wedge-inc-right (dyck-term dy) _) ⟩
      < lift-tm (dyck-term ey) [ wedge-inc-right (dyck-term dy) _ ]tm >tm ∎
     where
       open Reasoning tm-setoid

    l2 : lift-ty (dyck-type (wedge-dyck dy ey))
         ≃ty
         lift-ty (dyck-type ey) [ wedge-inc-right (dyck-term dy) _ ]ty
    l2 = begin
      < lift-ty (dyck-type (wedge-dyck dy ey)) >ty
        ≈⟨ lift-ty-≃ (wedge-dyck-type dy ey) ⟩
      < lift-ty (dyck-type ey [ wedge-inc-right (dyck-term dy) _ ]ty) >ty
        ≈˘⟨ apply-lifted-sub-ty-≃ (dyck-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
      < dyck-type ey [ lift-sub (wedge-inc-right (dyck-term dy) _) ]ty >ty
        ≈˘⟨ apply-sub-lifted-ty-≃ (dyck-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
      < lift-ty (dyck-type ey) [ wedge-inc-right (dyck-term dy) _ ]ty >ty ∎
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

wedge-dyck-type {m = zero} dy End = ⋆-is-only-0-d-ty ⦃ IsZero-subst (sym (dyck-type-dim dy)) it ⦄
wedge-dyck-type {m = zero} dy (⇓ ey) = ⊥-elim (dyck-0-is-0-d ey)
wedge-dyck-type {m = suc m} dy ey = begin
  < dyck-type (wedge-dyck dy ey) >ty
    ≈⟨ lift-ty-≃ (wedge-dyck-pre-type dy ey) ⟩
  < lift-ty (dyck-pre-type ey [ wedge-inc-right (dyck-term dy) _ ]ty) >ty
    ≈˘⟨ apply-lifted-sub-ty-≃ (dyck-pre-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
  < dyck-pre-type ey [ lift-sub (wedge-inc-right (dyck-term dy) _) ]ty >ty
    ≈˘⟨ apply-sub-lifted-ty-≃ (dyck-pre-type ey) (wedge-inc-right (dyck-term dy) _) ⟩
  < dyck-type ey [ wedge-inc-right (dyck-term dy) _ ]ty >ty ∎
  where
    open Reasoning ty-setoid

wedge-dyck-term dy End = refl≃tm
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
wedge-⌊⌋d dy End = refl≃c
wedge-⌊⌋d dy (⇑ ey)
  = Add≃ (Add≃ (wedge-⌊⌋d dy ey) (wedge-dyck-type dy ey)) (wedge-dyck-pre-type dy (⇑ ey))
wedge-⌊⌋d dy (⇓ ey)
  = wedge-⌊⌋d dy ey
