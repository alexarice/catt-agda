module Catt.Syntax.Equality.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Equality
open import Catt.Suspension

lift-ty-≃ : B ≃ty C → lift-ty B ≃ty lift-ty C
lift-ty-≃ = cong≃ lift-ty

lift-tm-≃ : s ≃tm t → lift-tm s ≃tm lift-tm t
lift-tm-≃ = cong≃ lift-tm

lift-sub-≃ : σ ≃s τ → lift-sub σ ≃s lift-sub τ
lift-sub-≃ = cong≃ lift-sub

susp-ctx-≃ : Γ ≃c Δ → susp-ctx Γ ≃c susp-ctx Δ
susp-ctx-≃ = cong≃ susp-ctx

susp-ty-≃ : A ≃ty B → susp-ty A ≃ty susp-ty B
susp-ty-≃ = cong≃ susp-ty

susp-tm-≃ : s ≃tm t → susp-tm s ≃tm susp-tm t
susp-tm-≃ = cong≃ susp-tm

susp-sub-≃ : σ ≃s τ → susp-sub σ ≃s susp-sub τ
susp-sub-≃ (refl ,, refl ,, refl ,, refl) = refl≃

unrestrict-≃ : σ ≃s τ → unrestrict σ ≃s unrestrict τ
unrestrict-≃ (refl ,, refl ,, refl ,, refl) = refl≃

restrict-≃ : σ ≃s τ → s ≃tm s′ → t ≃tm t′ → restrict σ s t ≃s restrict τ s′ t′
restrict-≃ (refl ,, refl ,, refl ,, refl) (refl ,, refl) (refl ,, refl) = refl≃

sub-action-≃-ty : A ≃ty B → σ ≃s τ → A [ σ ]ty ≃ty B [ τ ]ty
sub-action-≃-ty (refl ,, refl) (refl ,, r) = cong≃ (λ σ → _ [ σ ]ty) r
