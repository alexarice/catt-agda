module Catt.Dyck.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Dyck

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


connect-dyck-≃ : {gy : Dyck n d} → (p : dy ≃d ey) → fy ≃d gy → connect-dyck dy fy ≃d connect-dyck ey gy
connect-dyck-≃ p End≃ = p
connect-dyck-≃ p (⇑≃ q) = ⇑≃ (connect-dyck-≃ p q)
connect-dyck-≃ p (⇓≃ q) = ⇓≃ (connect-dyck-≃ p q)

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

dyck-to-ctx-≃ : dy ≃d ey → dyck-to-ctx dy ≃c dyck-to-ctx ey
dyck-to-ctx-≃ End≃ = refl≃c
dyck-to-ctx-≃ (⇑≃ p) = Add≃ (Add≃ (dyck-to-ctx-≃ p) (dyck-type-≃ p)) (dyck-pre-type-≃ (⇑≃ p))
dyck-to-ctx-≃ (⇓≃ p) = dyck-to-ctx-≃ p

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
susp-dyck-term (⇓ d) = {!!}

susp-dyck-to-ctx : (d : Dyck n d) → dyck-to-ctx (susp-dyck d) ≃c susp-ctx (dyck-to-ctx d)
susp-dyck-to-ctx End = refl≃c
susp-dyck-to-ctx (⇑ d) = Add≃ (Add≃ (susp-dyck-to-ctx d) {!!}) {!!}
susp-dyck-to-ctx (⇓ d) = susp-dyck-to-ctx d
