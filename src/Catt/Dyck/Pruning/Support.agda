module Catt.Dyck.Pruning.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular
open import Catt.Discs
open import Catt.Discs.Support
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pruning
open import Catt.Dyck.Support

open import Catt.Support
open import Catt.Support.Properties

open import Tactic.MonoidSolver

import Algebra.Solver.IdempotentCommutativeMonoid as Solver

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

π-drop : {dy : Dyck (suc n) m}
       → (pk : Peak dy)
       → (d : ℕ)
       → (d ≤ m)
       → TransportVarSet (drop (dyck-bd-supp d dy true)) (π pk)
         ≡
         drop (TransportVarSet ((dyck-bd-supp d dy true)) (π pk))
π-drop (⇕pk dy) d p with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = begin
  TransportVarSet (drop (dyck-bd-supp d dy true)) idSub
    ≡⟨ TransportVarSet-id (drop (dyck-bd-supp d dy true)) ⟩
  drop (dyck-bd-supp d dy true)
    ≡˘⟨ cong drop (TransportVarSet-id (dyck-bd-supp d dy true)) ⟩
  drop (TransportVarSet (dyck-bd-supp d dy true) idSub) ∎
... | tri≈ ¬a b ¬c = begin
  TransportVarSet (drop (dyck-bd-supp d dy true)) idSub
    ≡⟨ TransportVarSet-id (drop (dyck-bd-supp d dy true)) ⟩
  drop (dyck-bd-supp d dy true)
    ≡˘⟨ cong drop (dyck-bd-drop-≡ d dy (trans b (dyck-type-dim dy))) ⟩
  drop (drop (dyck-bd-supp d dy true) ∪ FVTm (dyck-term dy))
    ≡˘⟨ cong (λ - → drop (- ∪ FVTm (dyck-term dy))) (TransportVarSet-id (drop (dyck-bd-supp d dy true))) ⟩
  drop (TransportVarSet (drop (dyck-bd-supp d dy true)) idSub ∪ FVTm (dyck-term dy)) ∎
... | tri> ¬a ¬b c = ⊥-elim (1+n≰n (≤-trans (≤-trans (s≤s (≤-reflexive (sym (dyck-type-dim dy)))) c) p))
π-drop (⇑pk {dy = dy} pk) d p with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = begin
  TransportVarSet (drop (dyck-bd-supp d dy true)) (lift-sub (lift-sub (π pk)))
    ≡⟨ TransportVarSet-lift (drop (dyck-bd-supp d dy true)) (lift-sub (π pk)) ⟩
  ewf (TransportVarSet (drop (dyck-bd-supp d dy true)) (lift-sub (π pk)))
    ≡⟨ cong ewf (TransportVarSet-lift (drop (dyck-bd-supp d dy true)) (π pk)) ⟩
  ewf (ewf (TransportVarSet (drop (dyck-bd-supp d dy true)) (π pk)))
    ≡⟨ cong (ewf ∘ ewf) (π-drop pk d (≤-trans (n≤1+n d) (≤-trans a (≤-reflexive (dyck-type-dim dy))))) ⟩
  ewf (ewf (drop (TransportVarSet (dyck-bd-supp d dy true) (π pk))))
    ≡˘⟨ cong (drop ∘ ewf) (TransportVarSet-lift (dyck-bd-supp d dy true) (π pk)) ⟩
  drop (ewf (TransportVarSet (dyck-bd-supp d dy true) (lift-sub (π pk))))
    ≡˘⟨ cong drop (TransportVarSet-lift (dyck-bd-supp d dy true) (lift-sub (π pk))) ⟩
  drop (TransportVarSet (dyck-bd-supp d dy true) (lift-sub (lift-sub (π pk)))) ∎
... | tri≈ ¬a b ¬c = begin
  TransportVarSet (drop (dyck-bd-supp d dy true)) (lift-sub (lift-sub (π pk)))
    ≡⟨ TransportVarSet-lift (drop (dyck-bd-supp d dy true)) (lift-sub (π pk)) ⟩
  ewf (TransportVarSet (drop (dyck-bd-supp d dy true)) (lift-sub (π pk)))
    ≡⟨ cong ewf (TransportVarSet-lift (drop (dyck-bd-supp d dy true)) (π pk)) ⟩
  ewf (ewf (TransportVarSet (drop (dyck-bd-supp d dy true)) (π pk)))
    ≡˘⟨ cong (ewf ∘ ewf) (∪-right-unit (TransportVarSet (drop (dyck-bd-supp d dy true)) (π pk))) ⟩
  ewf (ewf (TransportVarSet (drop (dyck-bd-supp d dy true)) (π pk)) ∪ empty)
    ≡˘⟨ cong (λ - → drop (ewf (- ∪ ewt empty))) (TransportVarSet-lift (drop (dyck-bd-supp d dy true)) (π pk)) ⟩
  drop (ewf (TransportVarSet (drop (dyck-bd-supp d dy true)) (lift-sub (π pk)) ∪ ewt empty))
    ≡˘⟨ cong (λ - → drop (- ∪ ewf (ewt empty))) (TransportVarSet-lift (drop (dyck-bd-supp d dy true)) (lift-sub (π pk))) ⟩
  drop (TransportVarSet (drop (dyck-bd-supp d dy true)) (lift-sub (lift-sub (π pk))) ∪ ewf (ewt empty)) ∎
... | tri> ¬a ¬b c = begin
  TransportVarSet (dyck-bd-supp d dy true) (lift-sub (lift-sub (π pk))) ∪ ewf (ewt empty)
    ≡⟨ cong (_∪ ewf (ewt empty)) (TransportVarSet-lift (dyck-bd-supp d dy true) (lift-sub (π pk))) ⟩
  ewf (TransportVarSet (dyck-bd-supp d dy true) (lift-sub (π pk)) ∪ ewt empty)
    ≡˘⟨ cong ewf (∪-right-unit (TransportVarSet (dyck-bd-supp d dy true) (lift-sub (π pk)) ∪ ewt empty)) ⟩
  ewf (TransportVarSet (dyck-bd-supp d dy true) (lift-sub (π pk)) ∪ ewt empty ∪ empty)
    ≡˘⟨ cong (λ - → drop (- ∪ ewf (ewt empty) ∪ ewt empty)) (TransportVarSet-lift (dyck-bd-supp d dy true) (lift-sub (π pk))) ⟩
  drop (TransportVarSet (dyck-bd-supp d dy true) (lift-sub (lift-sub (π pk))) ∪ ewf (ewt empty) ∪ ewt empty) ∎
π-drop (⇓pk pk) d p = π-drop pk d (≤-trans p (n≤1+n _))

π-boundary-supp : {dy : Dyck (suc n) m}
                → (pk : Peak dy)
                → (d : ℕ)
                → (b : Bool)
                → TransportVarSet (dyck-bd-supp d dy b) (π pk) ≡ dyck-bd-supp d (dy // pk) b
π-boundary-supp (⇕pk dy) d b with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = TransportVarSet-id (dyck-bd-supp d dy b)
... | tri> ¬a ¬b c = begin
  TransportVarSet (dyck-bd-supp d dy b) idSub
  ∪ FVTm (dyck-term dy)
  ∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))
    ≡⟨ cong₂ (λ a b → a ∪ FVTm (dyck-term dy) ∪ b)
             (TransportVarSet-id (dyck-bd-supp d dy b))
             (identity-term-supp (dyck-type dy) (dyck-term dy)) ⟩
  dyck-bd-supp d dy b
    ∪ FVTm (dyck-term dy)
    ∪ (FVTy (dyck-type dy) ∪ FVTm (dyck-term dy))
    ≡⟨ prove 3 ((var 0F ⊕ var 1F) ⊕ (var 2F ⊕ var 1F))
               ((var 0F ⊕ var 2F) ⊕ var 1F)
               (dyck-bd-supp d dy b ∷ FVTm (dyck-term dy) ∷ FVTy (dyck-type dy) ∷ emp) ⟩
  dyck-bd-supp d dy b
    ∪ FVTy (dyck-type dy)
    ∪ FVTm (dyck-term dy)
    ≡˘⟨ cong (_∪ FVTm (dyck-term dy)) (dyck-bd-contains-ty′ 0 d dy b (≤-trans (≤-trans (n≤1+n _) (s≤s (≤-reflexive (sym (dyck-type-dim dy))))) c)) ⟩
  dyck-bd-supp d dy b ∪ FVTm (dyck-term dy)
    ≡˘⟨ dyck-bd-contains-tm d dy b (≤-trans (s≤s (≤-reflexive (sym (dyck-type-dim dy)))) c) ⟩
  dyck-bd-supp d dy b ∎
  where
    open Solver ∪-idempotentCommutativeMonoid
... | tri≈ ¬a b₁ ¬c with b
... | false = TransportVarSet-id (dyck-bd-supp d dy false)
... | true = begin
  TransportVarSet (drop (dyck-bd-supp d dy true)) idSub ∪ FVTm (dyck-term dy)
    ≡⟨ cong (_∪ FVTm (dyck-term dy)) (TransportVarSet-id (drop (dyck-bd-supp d dy true))) ⟩
  drop (dyck-bd-supp d dy true) ∪ FVTm (dyck-term dy)
    ≡⟨ dyck-bd-drop-≡ d dy (trans b₁ (dyck-type-dim dy)) ⟩
  dyck-bd-supp d dy true ∎
π-boundary-supp (⇑pk {dy = dy} pk) d b with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = begin
  TransportVarSet (dyck-bd-supp d dy b) (lift-sub (lift-sub (π pk)))
    ≡⟨ TransportVarSet-lift (dyck-bd-supp d dy b) (lift-sub (π pk)) ⟩
  ewf (TransportVarSet (dyck-bd-supp d dy b) (lift-sub (π pk)))
    ≡⟨ cong ewf (TransportVarSet-lift (dyck-bd-supp d dy b) (π pk)) ⟩
  ewf (ewf (TransportVarSet (dyck-bd-supp d dy b) (π pk)))
    ≡⟨ cong (ewf ∘ ewf) (π-boundary-supp pk d b) ⟩
  ewf (ewf (dyck-bd-supp d (dy // pk) b))
    ≡˘⟨ tri-case< (≤-trans a (≤-reflexive (trans (dyck-type-dim dy) (sym (dyck-type-dim (dy // pk))))))
                  (<-cmp d (ty-dim (dyck-type (dy // pk)))) _ _ _ ⟩
  _ ∎
... | tri> ¬a ¬b c = begin
  TransportVarSet (dyck-bd-supp d dy b) (lift-sub (lift-sub (π pk))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ ∪-assoc _ _ _ ⟩
  TransportVarSet (dyck-bd-supp d dy b) (lift-sub (lift-sub (π pk))) ∪ (ewt (ewt (empty ∪ empty)))
    ≡⟨ cong₂ _∪_ (TransportVarSet-lift (dyck-bd-supp d dy b) (lift-sub (π pk))) (cong (ewt ∘ ewt) (∪-left-unit empty)) ⟩
  ewt (TransportVarSet (dyck-bd-supp d dy b) (lift-sub (π pk)) ∪ ewt empty)
    ≡⟨ cong (λ a → ewt (a ∪ ewt empty)) (TransportVarSet-lift (dyck-bd-supp d dy b) (π pk)) ⟩
  ewt (ewt (TransportVarSet (dyck-bd-supp d dy b) (π pk)) ∪ empty)
    ≡⟨ cong (ewt ∘ ewt) (∪-right-unit (TransportVarSet (dyck-bd-supp d dy b) (π pk))) ⟩
  ewt (ewt (TransportVarSet (dyck-bd-supp d dy b) (π pk)))
    ≡⟨ cong (ewt ∘ ewt) (π-boundary-supp pk d b) ⟩
  ewt (ewt (dyck-bd-supp d (dy // pk) b))
    ≡˘⟨ tri-case> (≤-trans (≤-reflexive (cong suc (trans (dyck-type-dim (dy // pk)) (sym (dyck-type-dim dy))))) c)
                 (<-cmp d (ty-dim (dyck-type (dy // pk)))) _ _ _ ⟩
  _ ∎
... | tri≈ ¬a b₁ ¬c with b
... | false = begin
  TransportVarSet (dyck-bd-supp d dy false) (lift-sub (lift-sub (π pk)))
    ≡⟨ TransportVarSet-lift (dyck-bd-supp d dy false) (lift-sub (π pk)) ⟩
  ewf (TransportVarSet (dyck-bd-supp d dy false) (lift-sub (π pk)))
    ≡⟨ cong ewf (TransportVarSet-lift (dyck-bd-supp d dy false) (π pk)) ⟩
  ewf (ewf (TransportVarSet (dyck-bd-supp d dy false) (π pk)))
    ≡⟨ cong (ewf ∘ ewf) (π-boundary-supp pk d false) ⟩
  ewf (ewf (dyck-bd-supp d (dy // pk) false))
    ≡˘⟨ tri-case≡ (trans b₁ (trans (dyck-type-dim dy) (sym (dyck-type-dim (dy // pk)))))
                  (<-cmp d (ty-dim (dyck-type (dy // pk)))) _ _ _ ⟩
  _ ∎
... | true = begin
  TransportVarSet (drop (dyck-bd-supp d dy true)) (lift-sub (lift-sub (π pk))) ∪ ewf (ewt empty)
    ≡⟨ cong (_∪ ewf (ewt empty)) (TransportVarSet-lift (drop (dyck-bd-supp d dy true)) (lift-sub (π pk))) ⟩
  ewf (TransportVarSet (drop (dyck-bd-supp d dy true)) (lift-sub (π pk)) ∪ ewt empty)
    ≡⟨ cong (λ - → ewf (- ∪ ewt empty)) (TransportVarSet-lift (drop (dyck-bd-supp d dy true)) (π pk)) ⟩
  ewf (ewt (TransportVarSet (drop (dyck-bd-supp d dy true)) (π pk) ∪ empty))
    ≡⟨ cong (ewf ∘ ewt) (∪-right-unit (TransportVarSet (drop (dyck-bd-supp d dy true)) (π pk))) ⟩
  ewf (ewt (TransportVarSet (drop (dyck-bd-supp d dy true)) (π pk)))
    ≡⟨ cong (ewf ∘ ewt) (π-drop pk d (≤-reflexive (trans b₁ (dyck-type-dim dy)))) ⟩
  ewf (ewt (drop (TransportVarSet (dyck-bd-supp d dy true) (π pk))))
    ≡⟨ cong (ewf ∘ ewt ∘ drop) (π-boundary-supp pk d true) ⟩
  ewf (ewt (drop (dyck-bd-supp d (dy // pk) true)))
    ≡˘⟨ tri-case≡ (trans b₁ (trans (dyck-type-dim dy) (sym (dyck-type-dim (dy // pk)))))
                  (<-cmp d (ty-dim (dyck-type (dy // pk)))) _ _ _ ⟩
  _ ∎
π-boundary-supp (⇓pk pk) d b = π-boundary-supp pk d b


 -- begin
  -- TransportVarSet (dyck-bd-supp d dy b) (π pk)
  --   ≡˘⟨ cong (λ - → TransportVarSet - (π pk)) (supp-ctx-inc-FV (dyck-bd-supp d dy b)) ⟩
  -- TransportVarSet (FVSub (supp-ctx-inc (dyck-bd-supp d dy b))) (π pk)
  --   ≡⟨ TransportVarSet-sub (supp-ctx-inc (dyck-bd-supp d dy b)) (π pk) ⟩
  -- FVSub (supp-ctx-inc (dyck-bd-supp d dy b) ● π pk)
  --   ≡⟨ {!!} ⟩
  -- {!!}
  --   ≡⟨ {!!} ⟩
  -- {!!}
  --   ≡⟨ {!!} ⟩
  -- {!!}
  --   ≡⟨ {!!} ⟩
  -- {!!}
  --   ≡⟨ {!!} ⟩
  -- {!!}
  --   ≡⟨ {!!} ⟩
  -- dyck-bd-supp d (dy // pk) b ∎
