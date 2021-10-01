{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Support where

open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Connection.Support
open import Catt.Suspension.Support
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Variables
open import Data.Nat
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero; fromℕ; inject₁)
open import Relation.Binary.PropositionalEquality
open import Catt.Suspension
open import Data.Vec
open import Data.Bool

supp-bd-compat : (d : ℕ) → (T : Tree n) → (b : Bool) → FVSub (tree-inc d T b) ≡ supp-bd d T b
supp-bd-compat zero T false = ∪-left-unit (trueAt (fromℕ _))
supp-bd-compat zero T true = trans (∪-left-unit (FVTm (tree-last-var T))) (FVTm-on-var (tree-last-var T) ⦃ tree-last-var-is-var T ⦄)
supp-bd-compat (suc d) Sing b = refl
supp-bd-compat (suc d) (Join S T) b = trans (sub-between-connect-susps-supp (tree-inc d S b) (tree-inc (suc d) T b) (tree-inc-preserve-fst-var d T b)) (cong₂ (λ a b → connect-supp (suspSupp a) b) (supp-bd-compat d S b) (supp-bd-compat (suc d) T b))

linear-tree-supp-lem : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → .(tree-dim T ≡ suc d) → supp-bd d T false ∪ supp-bd d T true ∪ ewt empty ≡ full
linear-tree-supp-lem zero Sing p = refl
linear-tree-supp-lem zero (Join Sing Sing) p = refl
linear-tree-supp-lem zero (Join (Join S T) Sing) p with .(join-tree-has-non-zero-dim S T (sym (cong pred p)))
... | ()
linear-tree-supp-lem (suc d) (Join T Sing) p = begin
  suspSupp (supp-bd d T false) ∪ suspSupp (supp-bd d T true) ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) (suspSupp∪ (supp-bd d T false) (supp-bd d T true)) ⟩
  suspSupp (supp-bd d T false ∪ supp-bd d T true) ∪ ewt empty
    ≡⟨ lem (supp-bd d T false ∪ supp-bd d T true) ⟩
  suspSupp (supp-bd d T false ∪ supp-bd d T true ∪ ewt empty)
    ≡⟨ cong suspSupp (linear-tree-supp-lem d T (cong pred p)) ⟩
  suspSupp full
    ≡⟨ suspSuppFull ⟩
  full ∎
  where
    open ≡-Reasoning
    lem : (xs : VarSet (suc n)) → suspSupp xs ∪ ewt empty ≡ suspSupp (xs ∪ ewt empty)
    lem (x ∷ xs) = cong ((x ∨ true) ∷_) (trans (∪-right-unit (suspSupp xs)) (cong suspSupp (sym (∪-right-unit xs))))
