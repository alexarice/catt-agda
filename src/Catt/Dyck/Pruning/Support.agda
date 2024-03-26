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
            idSub-fv ⟩
  full ∪ FVTm (dyck-term dy) ∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))
    ≡⟨ cong (_∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))) (∪-left-zero (FVTm (dyck-term dy))) ⟩
  full ∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))
    ≡⟨ ∪-left-zero (FVTm (identity-term (dyck-type dy) (dyck-term dy))) ⟩
  full ∎
π-full {n = suc n} (⇑pk p) = begin
  FVSub (wk-sub (wk-sub (π p))) ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ cong (λ - → - ∪ ewf (ewt empty) ∪ ewt empty) (fv-wk-sub (wk-sub (π p))) ⟩
  ewt (FVSub (wk-sub (π p)) ∪ ewt empty ∪ empty)
    ≡⟨ cong (λ - → ewt (- ∪ ewt empty ∪ empty)) (fv-wk-sub (π p)) ⟩
  ewt (ewt (FVSub (π p) ∪ empty ∪ empty))
    ≡⟨ cong (ewt ∘ ewt) (solve (∪-monoid {n = suc (double n)})) ⟩
  ewt (ewt (FVSub (π p)))
    ≡⟨ cong (ewt ∘ ewt) (π-full p) ⟩
  full ∎
π-full (⇓pk p) = π-full p

π-drop : {dy : Dyck (suc n) m}
       → (pk : Peak dy)
       → (d : ℕ)
       → (d ≤ m)
       → drop (dyck-bd-vs d dy true) [ π pk ]vs
         ≡
         drop (dyck-bd-vs d dy true [ π pk ]vs)
π-drop (⇕pk dy) d p with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = begin
  drop (dyck-bd-vs d dy true) [ idSub ]vs
    ≡⟨ vs-sub-id (drop (dyck-bd-vs d dy true)) ⟩
  drop (dyck-bd-vs d dy true)
    ≡˘⟨ cong drop (vs-sub-id (dyck-bd-vs d dy true)) ⟩
  drop (dyck-bd-vs d dy true [ idSub ]vs) ∎
... | tri≈ ¬a b ¬c = begin
  drop (dyck-bd-vs d dy true) [ idSub ]vs
    ≡⟨ vs-sub-id (drop (dyck-bd-vs d dy true)) ⟩
  drop (dyck-bd-vs d dy true)
    ≡˘⟨ cong drop (dyck-bd-drop-≡ d dy (trans b (dyck-type-dim dy))) ⟩
  drop (drop (dyck-bd-vs d dy true) ∪ FVTm (dyck-term dy))
    ≡˘⟨ cong (λ - → drop (- ∪ FVTm (dyck-term dy))) (vs-sub-id (drop (dyck-bd-vs d dy true))) ⟩
  drop (drop (dyck-bd-vs d dy true) [ idSub ]vs ∪ FVTm (dyck-term dy)) ∎
... | tri> ¬a ¬b c = ⊥-elim (1+n≰n (≤-trans (≤-trans (s≤s (≤-reflexive (sym (dyck-type-dim dy)))) c) p))
π-drop (⇑pk {dy = dy} pk) d p with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = begin
  drop (dyck-bd-vs d dy true) [ wk-sub (wk-sub (π pk)) ]vs
    ≡⟨ vs-sub-wk (drop (dyck-bd-vs d dy true)) (wk-sub (π pk)) ⟩
  ewf (drop (dyck-bd-vs d dy true) [ wk-sub (π pk) ]vs)
    ≡⟨ cong ewf (vs-sub-wk (drop (dyck-bd-vs d dy true)) (π pk)) ⟩
  ewf (ewf (drop (dyck-bd-vs d dy true) [ π pk ]vs))
    ≡⟨ cong (ewf ∘ ewf) (π-drop pk d (≤-trans (n≤1+n d) (≤-trans a (≤-reflexive (dyck-type-dim dy))))) ⟩
  ewf (ewf (drop (dyck-bd-vs d dy true [ π pk ]vs)))
    ≡˘⟨ cong (drop ∘ ewf) (vs-sub-wk (dyck-bd-vs d dy true) (π pk)) ⟩
  drop (ewf (dyck-bd-vs d dy true [ wk-sub (π pk) ]vs))
    ≡˘⟨ cong drop (vs-sub-wk (dyck-bd-vs d dy true) (wk-sub (π pk))) ⟩
  drop (dyck-bd-vs d dy true [ wk-sub (wk-sub (π pk)) ]vs) ∎
... | tri≈ ¬a b ¬c = begin
  drop (dyck-bd-vs d dy true) [ wk-sub (wk-sub (π pk)) ]vs
    ≡⟨ vs-sub-wk (drop (dyck-bd-vs d dy true)) (wk-sub (π pk)) ⟩
  ewf (drop (dyck-bd-vs d dy true) [ wk-sub (π pk) ]vs)
    ≡⟨ cong ewf (vs-sub-wk (drop (dyck-bd-vs d dy true)) (π pk)) ⟩
  ewf (ewf (drop (dyck-bd-vs d dy true) [ π pk ]vs))
    ≡˘⟨ cong (ewf ∘ ewf) (∪-right-unit (drop (dyck-bd-vs d dy true) [ π pk ]vs)) ⟩
  ewf (ewf (drop (dyck-bd-vs d dy true) [ π pk ]vs) ∪ empty)
    ≡˘⟨ cong (λ - → drop (ewf (- ∪ ewt empty))) (vs-sub-wk (drop (dyck-bd-vs d dy true)) (π pk)) ⟩
  drop (ewf (drop (dyck-bd-vs d dy true) [ wk-sub (π pk) ]vs ∪ ewt empty))
    ≡˘⟨ cong (λ - → drop (- ∪ ewf (ewt empty))) (vs-sub-wk (drop (dyck-bd-vs d dy true)) (wk-sub (π pk))) ⟩
  drop (drop (dyck-bd-vs d dy true) [ wk-sub (wk-sub (π pk)) ]vs ∪ ewf (ewt empty)) ∎
... | tri> ¬a ¬b c = begin
  dyck-bd-vs d dy true [ wk-sub (wk-sub (π pk)) ]vs ∪ ewf (ewt empty)
    ≡⟨ cong (_∪ ewf (ewt empty)) (vs-sub-wk (dyck-bd-vs d dy true) (wk-sub (π pk))) ⟩
  ewf (dyck-bd-vs d dy true [ wk-sub (π pk) ]vs ∪ ewt empty)
    ≡˘⟨ cong ewf (∪-right-unit (dyck-bd-vs d dy true [ wk-sub (π pk) ]vs ∪ ewt empty)) ⟩
  ewf (dyck-bd-vs d dy true [ wk-sub (π pk) ]vs ∪ ewt empty ∪ empty)
    ≡˘⟨ cong (λ - → drop (- ∪ ewf (ewt empty) ∪ ewt empty)) (vs-sub-wk (dyck-bd-vs d dy true) (wk-sub (π pk))) ⟩
  drop (dyck-bd-vs d dy true [ wk-sub (wk-sub (π pk)) ]vs ∪ ewf (ewt empty) ∪ ewt empty) ∎
π-drop (⇓pk pk) d p = π-drop pk d (≤-trans p (n≤1+n _))

π-boundary-vs : {dy : Dyck (suc n) m}
                → (pk : Peak dy)
                → (d : ℕ)
                → (b : Bool)
                → dyck-bd-vs d dy b [ π pk ]vs ≡ dyck-bd-vs d (dy // pk) b
π-boundary-vs (⇕pk dy) d b with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = vs-sub-id (dyck-bd-vs d dy b)
... | tri> ¬a ¬b c = begin
  dyck-bd-vs d dy b [ idSub ]vs
  ∪ FVTm (dyck-term dy)
  ∪ FVTm (identity-term (dyck-type dy) (dyck-term dy))
    ≡⟨ cong₂ (λ a b → a ∪ FVTm (dyck-term dy) ∪ b)
             (vs-sub-id (dyck-bd-vs d dy b))
             (identity-term-fv (dyck-type dy) (dyck-term dy)) ⟩
  dyck-bd-vs d dy b
    ∪ FVTm (dyck-term dy)
    ∪ (FVTy (dyck-type dy) ∪ FVTm (dyck-term dy))
    ≡⟨ prove 3 ((var 0F ⊕ var 1F) ⊕ (var 2F ⊕ var 1F))
               ((var 0F ⊕ var 2F) ⊕ var 1F)
               (dyck-bd-vs d dy b ∷ FVTm (dyck-term dy) ∷ FVTy (dyck-type dy) ∷ emp) ⟩
  dyck-bd-vs d dy b
    ∪ FVTy (dyck-type dy)
    ∪ FVTm (dyck-term dy)
    ≡˘⟨ cong (_∪ FVTm (dyck-term dy)) (dyck-bd-contains-ty′ 0 d dy b (≤-trans (≤-trans (n≤1+n _) (s≤s (≤-reflexive (sym (dyck-type-dim dy))))) c)) ⟩
  dyck-bd-vs d dy b ∪ FVTm (dyck-term dy)
    ≡˘⟨ dyck-bd-contains-tm d dy b (≤-trans (s≤s (≤-reflexive (sym (dyck-type-dim dy)))) c) ⟩
  dyck-bd-vs d dy b ∎
  where
    open Solver ∪-idempotentCommutativeMonoid
... | tri≈ ¬a b₁ ¬c with b
... | false = vs-sub-id (dyck-bd-vs d dy false)
... | true = begin
  drop (dyck-bd-vs d dy true) [ idSub ]vs ∪ FVTm (dyck-term dy)
    ≡⟨ cong (_∪ FVTm (dyck-term dy)) (vs-sub-id (drop (dyck-bd-vs d dy true))) ⟩
  drop (dyck-bd-vs d dy true) ∪ FVTm (dyck-term dy)
    ≡⟨ dyck-bd-drop-≡ d dy (trans b₁ (dyck-type-dim dy)) ⟩
  dyck-bd-vs d dy true ∎
π-boundary-vs (⇑pk {dy = dy} pk) d b with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = begin
  dyck-bd-vs d dy b [ wk-sub (wk-sub (π pk)) ]vs
    ≡⟨ vs-sub-wk (dyck-bd-vs d dy b) (wk-sub (π pk)) ⟩
  ewf (dyck-bd-vs d dy b [ wk-sub (π pk) ]vs)
    ≡⟨ cong ewf (vs-sub-wk (dyck-bd-vs d dy b) (π pk)) ⟩
  ewf (ewf (dyck-bd-vs d dy b [ π pk ]vs))
    ≡⟨ cong (ewf ∘ ewf) (π-boundary-vs pk d b) ⟩
  ewf (ewf (dyck-bd-vs d (dy // pk) b))
    ≡˘⟨ tri-case< (≤-trans a (≤-reflexive (trans (dyck-type-dim dy) (sym (dyck-type-dim (dy // pk))))))
                  (<-cmp d (ty-dim (dyck-type (dy // pk)))) _ _ _ ⟩
  _ ∎
... | tri> ¬a ¬b c = begin
  dyck-bd-vs d dy b [ wk-sub (wk-sub (π pk)) ]vs ∪ ewf (ewt empty) ∪ ewt empty
    ≡⟨ ∪-assoc _ _ _ ⟩
  dyck-bd-vs d dy b [ wk-sub (wk-sub (π pk)) ]vs ∪ (ewt (ewt (empty ∪ empty)))
    ≡⟨ cong₂ _∪_ (vs-sub-wk (dyck-bd-vs d dy b) (wk-sub (π pk))) (cong (ewt ∘ ewt) (∪-left-unit empty)) ⟩
  ewt (dyck-bd-vs d dy b [ wk-sub (π pk) ]vs ∪ ewt empty)
    ≡⟨ cong (λ a → ewt (a ∪ ewt empty)) (vs-sub-wk (dyck-bd-vs d dy b) (π pk)) ⟩
  ewt (ewt (dyck-bd-vs d dy b [ π pk ]vs) ∪ empty)
    ≡⟨ cong (ewt ∘ ewt) (∪-right-unit (dyck-bd-vs d dy b [ π pk ]vs)) ⟩
  ewt (ewt (dyck-bd-vs d dy b [ π pk ]vs))
    ≡⟨ cong (ewt ∘ ewt) (π-boundary-vs pk d b) ⟩
  ewt (ewt (dyck-bd-vs d (dy // pk) b))
    ≡˘⟨ tri-case> (≤-trans (≤-reflexive (cong suc (trans (dyck-type-dim (dy // pk)) (sym (dyck-type-dim dy))))) c)
                 (<-cmp d (ty-dim (dyck-type (dy // pk)))) _ _ _ ⟩
  _ ∎
... | tri≈ ¬a b₁ ¬c with b
... | false = begin
  dyck-bd-vs d dy false [ wk-sub (wk-sub (π pk)) ]vs
    ≡⟨ vs-sub-wk (dyck-bd-vs d dy false) (wk-sub (π pk)) ⟩
  ewf (dyck-bd-vs d dy false [ wk-sub (π pk) ]vs)
    ≡⟨ cong ewf (vs-sub-wk (dyck-bd-vs d dy false) (π pk)) ⟩
  ewf (ewf (dyck-bd-vs d dy false [ π pk ]vs))
    ≡⟨ cong (ewf ∘ ewf) (π-boundary-vs pk d false) ⟩
  ewf (ewf (dyck-bd-vs d (dy // pk) false))
    ≡˘⟨ tri-case≡ (trans b₁ (trans (dyck-type-dim dy) (sym (dyck-type-dim (dy // pk)))))
                  (<-cmp d (ty-dim (dyck-type (dy // pk)))) _ _ _ ⟩
  _ ∎
... | true = begin
  drop (dyck-bd-vs d dy true) [ wk-sub (wk-sub (π pk)) ]vs ∪ ewf (ewt empty)
    ≡⟨ cong (_∪ ewf (ewt empty)) (vs-sub-wk (drop (dyck-bd-vs d dy true)) (wk-sub (π pk))) ⟩
  ewf (drop (dyck-bd-vs d dy true) [ wk-sub (π pk) ]vs ∪ ewt empty)
    ≡⟨ cong (λ - → ewf (- ∪ ewt empty)) (vs-sub-wk (drop (dyck-bd-vs d dy true)) (π pk)) ⟩
  ewf (ewt (drop (dyck-bd-vs d dy true) [ π pk ]vs ∪ empty))
    ≡⟨ cong (ewf ∘ ewt) (∪-right-unit (drop (dyck-bd-vs d dy true) [ π pk ]vs)) ⟩
  ewf (ewt (drop (dyck-bd-vs d dy true) [ π pk ]vs))
    ≡⟨ cong (ewf ∘ ewt) (π-drop pk d (≤-reflexive (trans b₁ (dyck-type-dim dy)))) ⟩
  ewf (ewt (drop (dyck-bd-vs d dy true [ π pk ]vs)))
    ≡⟨ cong (ewf ∘ ewt ∘ drop) (π-boundary-vs pk d true) ⟩
  ewf (ewt (drop (dyck-bd-vs d (dy // pk) true)))
    ≡˘⟨ tri-case≡ (trans b₁ (trans (dyck-type-dim dy) (sym (dyck-type-dim (dy // pk)))))
                  (<-cmp d (ty-dim (dyck-type (dy // pk)))) _ _ _ ⟩
  _ ∎
π-boundary-vs (⇓pk pk) d b = π-boundary-vs pk d b
