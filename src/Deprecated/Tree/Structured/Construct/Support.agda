module Deprecated.Tree.Structured.Construct.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct

open import Catt.Support
open import Deprecated.Tree.Support
open import Deprecated.Tree.Structured.Support
open import Deprecated.Tree.Structured.Support.Properties

import Algebra.Solver.IdempotentCommutativeMonoid as Solver

open ≡-Reasoning

extend-disc-label-supp : {X : MaybeTree m}
                       → (L : Label X S)
                       → .⦃ _ : is-linear S ⦄
                       → (t : STm X)
                       → (a : STm X)
                       → FVLabel (extend-disc-label L t a) ≡ FVLabel L ∪m FVSTm t ∪m FVSTm a
extend-disc-label-supp {S = Sing} L t a
  = prove 3 ((var 0F ⊕ var 1F) ⊕ var 2F)
            ((var 0F ⊕ var 2F) ⊕ var 1F)
            (FVSTm (L PHere) ∷ FVSTm a ∷ FVSTm t ∷ emp)
  where
    open Solver ∪m-idempotentCommutativeMonoid
extend-disc-label-supp {S = Susp S} L t a = begin
  FVSTm (L PHere) ∪m FVLabel (extend-disc-label (L ∘ PExt) t a) ∪m FVSTm (L (PShift PHere))
    ≡⟨ cong (λ - → FVSTm (L PHere) ∪m - ∪m FVSTm (L (PShift PHere))) (extend-disc-label-supp (L ∘ PExt) t a) ⟩
  FVSTm (L PHere) ∪m (FVLabel (L ∘ PExt) ∪m FVSTm t ∪m FVSTm a) ∪m FVSTm (L (PShift PHere))
    ≡⟨ prove 5 ((var 0F ⊕ ((var 1F ⊕ var 2F) ⊕ var 3F)) ⊕ var 4F)
               ((((var 0F ⊕ var 1F) ⊕ var 4F) ⊕ var 2F) ⊕ var 3F)
               (FVSTm (L PHere) ∷ FVLabel (L ∘ PExt) ∷ FVSTm t ∷ FVSTm a ∷ FVSTm (L (PShift PHere)) ∷ emp) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVSTm (L (PShift PHere)) ∪m FVSTm t ∪m FVSTm a ∎
  where
    open Solver ∪m-idempotentCommutativeMonoid

stm-to-label-supp : {X : MaybeTree m}
                  → (S : Tree n)
                  → .⦃ _ : is-linear S ⦄
                  → (a : STm X)
                  → (As : STy X)
                  → .⦃ _ : has-dim (tree-dim S) As ⦄
                  → FVLabel (stm-to-label S a As) ≡ FVSTy As ∪m FVSTm a
stm-to-label-supp Sing a S⋆ = sym (∪m-left-unit (FVSTm a))
stm-to-label-supp (Susp S) a (SArr s As t) = begin
  FVLabel (extend-disc-label (stm-to-label S s As) t a)
    ≡⟨ extend-disc-label-supp (stm-to-label S s As) t a ⟩
  FVLabel (stm-to-label S s As) ∪m FVSTm t ∪m FVSTm a
    ≡⟨ cong (λ - → - ∪m FVSTm t ∪m FVSTm a) (stm-to-label-supp S s As) ⟩
  FVSTy As ∪m FVSTm s ∪m FVSTm t ∪m FVSTm a ∎
