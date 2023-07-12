module Catt.Discs.Support where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Globular
open import Catt.Discs

open import Catt.Support
open import Catt.Support.Properties

sphere-supp : (d : ℕ) → FVTy (sphere-type d) ≡ full
sphere-supp zero = refl
sphere-supp (suc d) = begin
  FVTy (lift-ty (lift-ty (sphere-type d))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ cong (λ - → - ∪ ewf (ewt empty) ∪ ewt empty) (supp-lift-ty (lift-ty (sphere-type d))) ⟩
  ewf (FVTy (lift-ty (sphere-type d))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ cong (λ - → ewf - ∪ ewf (ewt empty) ∪ ewt empty) (supp-lift-ty (sphere-type d)) ⟩
  ewf (ewf (FVTy (sphere-type d))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ cong (λ - → ewt (ewt -)) (∪-right-unit (FVTy (sphere-type d) ∪ empty)) ⟩
  ewt (ewt (FVTy (sphere-type d) ∪ empty))
    ≡⟨ cong (λ - → ewt (ewt -)) (∪-right-unit (FVTy (sphere-type d))) ⟩
  ewt (ewt (FVTy (sphere-type d)))
    ≡⟨ cong (λ - → ewt (ewt -)) (sphere-supp d) ⟩
  full ∎
  where
    open ≡-Reasoning

sub-from-sphere-supp : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → FVSub (sub-from-sphere d A p) ≡ FVTy A
sub-from-sphere-supp zero ⋆ p = refl
sub-from-sphere-supp (suc d) (s ─⟨ A ⟩⟶ t) p = cong (λ - → - ∪ FVTm s ∪ FVTm t) (sub-from-sphere-supp d A (cong pred p))

sub-from-disc-supp : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (t : Tm n) → FVSub (sub-from-disc d A p t) ≡ FVTy A ∪ FVTm t
sub-from-disc-supp d A p t = cong (_∪ FVTm t) (sub-from-sphere-supp d A p)
