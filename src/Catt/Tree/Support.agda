{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Support where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
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
open import Data.Bool using (Bool; true; false; _∨_) renaming (T to Truth)
open import Data.Nat.Properties
import Relation.Binary.Reasoning.PartialOrder as PReasoning
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Unit using (tt)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using ()

supp-bd-full : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-dim T ≤ d → supp-bd d T b ≡ full
supp-bd-full zero Sing false p = refl
supp-bd-full zero Sing true p = refl
supp-bd-full zero (Join S T) b p with tree-dim T
supp-bd-full zero (Join S T) b () | zero
supp-bd-full zero (Join S T) b () | suc x
supp-bd-full (suc d) Sing b p = refl
supp-bd-full (suc d) (Join S T) b p = begin
  connect-supp (suspSupp (supp-bd d S b)) (supp-bd (suc d) T b)
    ≡⟨ cong₂ (λ a b → connect-supp (suspSupp a) b) (supp-bd-full d S b (≤-pred (m⊔n≤o⇒m≤o (suc (tree-dim S)) (tree-dim T) p))) (supp-bd-full (suc d) T b (m⊔n≤o⇒n≤o (suc (tree-dim S)) (tree-dim T) p)) ⟩
  connect-supp (suspSupp full) full
    ≡⟨ cong (λ - → connect-supp - full) suspSuppFull ⟩
  connect-supp full full
    ≡⟨ connect-supp-full (suc (suc _)) _ ⟩
  full ∎
  where
    open ≡-Reasoning

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

supp-bd-include-fst : (d : ℕ) → (T : Tree n) → (b : Bool) → Truth (lookup-isVar (supp-bd (suc d) T b) (Var (fromℕ _)))
supp-bd-include-fst d Sing b = tt
supp-bd-include-fst d (Join S T) b = connect-supp-fst (suspSupp (supp-bd d S b)) (supp-bd (suc d) T b) (suspSuppFstTruth (supp-bd d S b))

supp-bd-include-last : (d : ℕ) → (T : Tree n) → (b : Bool) → FVTm (tree-last-var T) ⊆ supp-bd (suc d) T b
supp-bd-include-last d Sing b = ⊆-refl
supp-bd-include-last d (Join S T) b = begin
  FVTm (tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm)
    ≡˘⟨ TransportVarSet-tm (tree-last-var T) (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
  TransportVarSet (FVTm (tree-last-var T))
    (connect-susp-inc-right (tree-size S) (tree-size T))
    ≤⟨ ⊆-TransportVarSet (connect-susp-inc-right (tree-size S) (tree-size T)) (supp-bd-include-last d T b) ⟩
  TransportVarSet (supp-bd (suc d) T b) (connect-inc-right getSnd _)
    ≤⟨ ∪-⊆-2 (TransportVarSet (suspSupp (supp-bd d S b))
               (connect-inc-left getSnd _)) (TransportVarSet (supp-bd (suc d) T b) (connect-inc-right getSnd _)) ⟩
  TransportVarSet (suspSupp (supp-bd d S b))
    (connect-inc-left getSnd _)
    ∪
    TransportVarSet (supp-bd (suc d) T b) (connect-inc-right getSnd _)
    ≡⟨ connect-supp-incs (suspSupp (supp-bd d S b)) getSnd (supp-bd (suc d) T b) (suspSuppSnd (supp-bd d S b)) ⟩
  connect-supp (suspSupp (supp-bd d S b)) (supp-bd (suc d) T b) ∎
  where
    open PReasoning (⊆-poset _)

connect-tree-to-ctx-supp : (d : ℕ) → (S : Tree n) → (T : Tree m) → (b : Bool)
                         → TransportVarSet (connect-supp (supp-bd (suc d) S b) (supp-bd (suc d) T b))
                                           (idSub≃ (sym≃c (connect-tree-to-ctx S T)))
                         ≡ supp-bd (suc d) (connect-tree S T) b
connect-tree-to-ctx-supp d S T b = P.Pointwise-≡⇒≡ (P.trans trans (TransportVarSet-idSub≃ (connect-supp (supp-bd (suc d) S b) (supp-bd (suc d) T b)) (sym≃c (connect-tree-to-ctx S T))) (lem d S T b))
  where
    lem : (d : ℕ) → (S : Tree n) → (T : Tree m) → (b : Bool)
        → connect-supp (supp-bd (suc d) S b) (supp-bd (suc d) T b) ≡ᵖ supp-bd (suc d) (connect-tree S T) b
    lem d Sing T b = connect-supp-unit-left (supp-bd (suc d) T b) (supp-bd-include-fst d T b)
    lem d (Join S₁ S₂) T b = P.trans trans (connect-supp-assoc (suspSupp (supp-bd d S₁ b)) (supp-bd (suc d) S₂ b) (supp-bd (suc d) T b)) (connect-supp-≡ᵖ (P.refl refl) (lem d S₂ T b))
