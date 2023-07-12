module Catt.Dyck.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
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

dyck-type-dim : (dy : Dyck n d) → ty-dim (dyck-type dy) ≡ d
dyck-type-dim End = refl
dyck-type-dim (⇑ dy) = cong suc (trans (lift-ty-dim (lift-ty (dyck-type dy))) (trans (lift-ty-dim (dyck-type dy)) (dyck-type-dim dy)))
dyck-type-dim (⇓ dy) = trans (cong ty-dim (sym (≃ty-to-≡ (ty-base-lift (dyck-pre-type dy))))) (trans (ty-dim-ty-base (dyck-type dy)) (cong pred (dyck-type-dim dy)))

dyck-zero-lem : ¬ (Dyck zero (suc d))
dyck-zero-lem (⇓ dy) = dyck-zero-lem dy
