module Catt.Discs.Support where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Discs
open import Catt.Support
open import Catt.Globular

sub-from-sphere-supp : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → FVSub (sub-from-sphere d A p) ≡ FVTy A
sub-from-sphere-supp zero ⋆ p = refl
sub-from-sphere-supp (suc d) (s ─⟨ A ⟩⟶ t) p = cong (λ - → - ∪ FVTm s ∪ FVTm t) (sub-from-sphere-supp d A (cong pred p))

sub-from-disc-supp : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (t : Tm n) → FVSub (sub-from-disc d A p t) ≡ FVTy A ∪ FVTm t
sub-from-disc-supp d A p t = cong (_∪ FVTm t) (sub-from-sphere-supp d A p)
