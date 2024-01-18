module Catt.Dyck.Pruning.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Discs
open import Catt.Dyck
open import Catt.Dyck.Pruning

open import Catt.Support
open import Catt.Support.Properties

open import Tactic.MonoidSolver

open ≡-Reasoning

π-full : {dy : Dyck (suc n) d} → (p : Peak dy) → FVSub (π p) ≡ full
π-full {n = n} (⇕pk dy) = begin
  FVSub idSub ∪ FVTm (dyck-term dy) ∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))
    ≡⟨ cong (λ - → - ∪ FVTm (dyck-term dy) ∪ FVTm (identity-term (dyck-type dy) (dyck-term dy)))
            idSub-supp ⟩
  full ∪ FVTm (dyck-term dy) ∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))
    ≡⟨ cong (_∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))) (∪-left-zero (FVTm (dyck-term dy))) ⟩
  full ∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))
    ≡⟨ ∪-left-zero (FVTm (identity-term (dyck-type dy) (dyck-term dy))) ⟩
  full ∎
π-full {n = suc n} (⇑pk p) = begin
  FVSub (lift-sub (lift-sub (π p))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ cong (λ - → - ∪ ewf (ewt empty) ∪ ewt empty) (supp-lift-sub (lift-sub (π p))) ⟩
  ewt (FVSub (lift-sub (π p)) ∪ ewt empty ∪ empty)
    ≡⟨ cong (λ - → ewt (- ∪ ewt empty ∪ empty)) (supp-lift-sub (π p)) ⟩
  ewt (ewt (FVSub (π p) ∪ empty ∪ empty))
    ≡⟨ cong (ewt ∘ ewt) (solve (∪-monoid {n = suc (n * 2)})) ⟩
  ewt (ewt (FVSub (π p)))
    ≡⟨ cong (ewt ∘ ewt) (π-full p) ⟩
  full ∎
π-full (⇓pk p) = π-full p
