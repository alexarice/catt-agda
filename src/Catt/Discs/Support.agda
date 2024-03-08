module Catt.Discs.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Discs.Pasting

open import Catt.Support
open import Catt.Support.Properties

open ≡-Reasoning

Disc-src : (n : ℕ) → pd-bd-supp n (Disc (suc n)) ⦃ disc-pd (suc n) ⦄ false ≡ ewf (ewf full)
Disc-src n = let
  instance _ = disc-pd (suc n)
  instance _ = disc-pd n
  in begin
  pd-bd-supp n (Disc (suc n)) false
    ≡⟨ tri-case≡ (sym (trans (wk-ty-dim (sphere-type n)) (sphere-type-dim n)))
                 (<-cmp n (ty-dim (wk-ty (sphere-type n)))) _ _ _ ⟩
  ewf (ewf (pd-bd-supp n (Disc n) false))
    ≡⟨ cong (ewf ∘ ewf) (pd-bd-supp-full n (Disc n) false (≤-reflexive (disc-dim n))) ⟩
  ewf (ewf full) ∎

Disc-tgt : (n : ℕ) → pd-bd-supp n (Disc (suc n)) ⦃ disc-pd (suc n) ⦄ true ≡ ewf (ewt (ewf full))
Disc-tgt n = let
  instance _ = disc-pd (suc n)
  instance _ = disc-pd n
  in begin
  pd-bd-supp n (Disc (suc n)) true
    ≡⟨ tri-case≡ (sym (trans (wk-ty-dim (sphere-type n)) (sphere-type-dim n)))
                 (<-cmp n (ty-dim (wk-ty (sphere-type n)))) _ _ _ ⟩
  ewf (ewt (drop (pd-bd-supp n (Disc n) true)))
    ≡⟨ cong (ewf ∘ ewt ∘ drop) (pd-bd-supp-full n (Disc n) true (≤-reflexive (disc-dim n))) ⟩
  ewf (ewt (ewf full)) ∎

sphere-supp : (d : ℕ) → FVTy (sphere-type d) ≡ full
sphere-supp zero = refl
sphere-supp (suc d) = begin
  FVTy (wk-ty (wk-ty (sphere-type d))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ cong (λ - → - ∪ ewf (ewt empty) ∪ ewt empty) (supp-wk-ty (wk-ty (sphere-type d))) ⟩
  ewf (FVTy (wk-ty (sphere-type d))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ cong (λ - → ewf - ∪ ewf (ewt empty) ∪ ewt empty) (supp-wk-ty (sphere-type d)) ⟩
  ewf (ewf (FVTy (sphere-type d))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ cong (λ - → ewt (ewt -)) (∪-right-unit (FVTy (sphere-type d) ∪ empty)) ⟩
  ewt (ewt (FVTy (sphere-type d) ∪ empty))
    ≡⟨ cong (λ - → ewt (ewt -)) (∪-right-unit (FVTy (sphere-type d))) ⟩
  ewt (ewt (FVTy (sphere-type d)))
    ≡⟨ cong (λ - → ewt (ewt -)) (sphere-supp d) ⟩
  full ∎

var0-disc-full : (n : ℕ) → SuppTm (Disc n) 0V ≡ full
var0-disc-full n = cong ewt (begin
  DC (Sphere n) (empty ∪ FVTy (sphere-type n))
    ≡⟨ cong (DC (Sphere n)) (∪-left-unit (FVTy (sphere-type n))) ⟩
  DC (Sphere n) (FVTy (sphere-type n))
    ≡⟨ cong (DC (Sphere n)) (sphere-supp n) ⟩
  DC (Sphere n) full
    ≡⟨ DC-full (Sphere n) ⟩
  full ∎)

var1-disc-supp : (n : ℕ) → SuppTm (Disc (suc n)) 1V ≡ pd-bd-supp n (Disc (suc n)) ⦃ disc-pd (suc n) ⦄ true
var1-disc-supp n = let
  instance _ = disc-pd (suc n)
  instance _ = disc-pd n
  in begin
  SuppTm (Disc (suc n)) (Var 1F)
    ≡⟨ cong (ewf ∘ ewt ∘ DC (Disc n)) (∪-left-unit (FVTy (wk-ty (sphere-type n)))) ⟩
  ewf (ewt (DC (Disc n) (FVTy (wk-ty (sphere-type n)))))
    ≡⟨ cong (ewf ∘ ewt ∘ DC (Disc n)) (supp-wk-ty (sphere-type n)) ⟩
  ewf (ewt (ewf (DC (Sphere n) (FVTy (sphere-type n)))))
    ≡⟨ cong (ewf ∘ ewt ∘ ewf ∘ DC (Sphere n)) (sphere-supp n) ⟩
  ewf (ewt (ewf (DC (Sphere n) full)))
    ≡⟨ cong (ewf ∘ ewt ∘ ewf) (DC-full (Sphere n)) ⟩
  ewf (ewt (ewf full))
    ≡˘⟨ Disc-tgt n ⟩
  pd-bd-supp n (Disc (suc n)) true ∎

var2-disc-supp : (n : ℕ) → SuppTm (Disc (suc n)) 2V ≡ pd-bd-supp n (Disc (suc n)) ⦃ disc-pd (suc n) ⦄ false
var2-disc-supp n = let
  instance _ = disc-pd (suc n)
  in begin
  ewf (ewf (ewt (DC (Sphere n) (empty ∪ FVTy (sphere-type n)))))
    ≡⟨ cong (ewf ∘ ewf ∘ ewt ∘ DC (Sphere n)) (∪-left-unit (FVTy (sphere-type n))) ⟩
  ewf (ewf (ewt (DC (Sphere n) (FVTy (sphere-type n)))))
    ≡⟨ cong (ewf ∘ ewf ∘ ewt ∘ DC (Sphere n)) (sphere-supp n) ⟩
  ewf (ewf (ewt (DC (Sphere n) full)))
    ≡⟨ cong (ewf ∘ ewf ∘ ewt) (DC-full (Sphere n)) ⟩
  ewf (ewf (ewt full))
    ≡˘⟨ Disc-src n ⟩
  pd-bd-supp n (Disc (suc n)) false ∎

sub-from-sphere-supp : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → FVSub (sub-from-sphere d A p) ≡ FVTy A
sub-from-sphere-supp zero ⋆ p = refl
sub-from-sphere-supp (suc d) (s ─⟨ A ⟩⟶ t) p = cong (λ - → - ∪ FVTm s ∪ FVTm t) (sub-from-sphere-supp d A (cong pred p))

sub-from-disc-supp : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (t : Tm n) → FVSub (sub-from-disc d A p t) ≡ FVTy A ∪ FVTm t
sub-from-disc-supp d A p t = cong (_∪ FVTm t) (sub-from-sphere-supp d A p)

identity-term-supp : (A : Ty n) → (t : Tm n) → FVTm (identity-term A t) ≡ FVTy A ∪ FVTm t
identity-term-supp A t = sub-from-disc-supp (ty-dim A) A refl t
