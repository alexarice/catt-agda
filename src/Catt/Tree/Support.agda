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
open import Data.Vec hiding (drop)
open import Data.Bool using (Bool; true; false; _∨_) renaming (T to Truth)
open import Data.Nat.Properties
import Relation.Binary.Reasoning.PartialOrder as PReasoning
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Unit using (tt)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using ()
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Tree.Pasting
open import Relation.Binary.Definitions
open import Data.Empty
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Connection.Support
open import Catt.Connection.Pasting

drop-var : (t : Tm n) → .⦃ isVar t ⦄ → drop (FVTm t) ≡ empty
drop-var (Var zero) = refl
drop-var (Var (suc i)) = cong ewf (drop-var (Var i))

supp-compat : (n : ℕ) → (T : Tree m) → (b : Bool) → supp-tree-bd n T b ≡ pd-bd-supp n (tree-to-ctx T) ⦃ tree-to-pd T ⦄ b
supp-compat zero T false = lem (tree-to-ctx T) ⦃ pd-to-pdb (tree-to-pd T) ⦄
  where
    lem : (Γ : Ctx (suc m)) → .⦃ pdb : Γ ⊢pdb ⦄ → trueAt (fromℕ m) ≡ pdb-bd-supp zero Γ false
    lem (∅ , A) = refl
    lem (∅ , B , A) = ⊥-elim′ (pdb-odd-length it)
    lem (Γ , C , B , A) with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = cong ewf (cong ewf (lem (Γ , C) ⦃ pdb-prefix it ⦄))
    ... | tri≈ ¬a b ¬c = cong ewf (cong ewf (lem (Γ , C) ⦃ pdb-prefix it ⦄))
supp-compat zero T true = begin
  FVTm (tree-last-var T)
    ≡˘⟨ FVTm-≃ (tree-to-pd-focus-tm T) ⟩
  FVTm (pd-focus-tm (tree-to-pd T))
    ≡˘⟨ FVTm-≃ (pd-right-base (tree-to-pd T)) ⟩
  FVTm (pdb-right-base (pd-to-pdb (tree-to-pd T)))
    ≡⟨ lem (tree-to-ctx T) (pd-to-pdb (tree-to-pd T)) ⟩
  pd-bd-supp zero (tree-to-ctx T) ⦃ tree-to-pd T ⦄ true ∎
  where
    open ≡-Reasoning

    lem : (Γ : Ctx (suc m)) → (pdb : Γ ⊢pdb) → FVTm (pdb-right-base pdb) ≡ pdb-bd-supp zero Γ ⦃ pdb ⦄ true
    lem (∅ , .⋆) Base = refl
    lem (∅ , A) (Restr pdb) = ⊥-elim (NonZero′-⊥ (≤-trans (pdb-dim-lem pdb) (≤-reflexive (ty-dim-≃ (pdb-singleton-lem pdb)))))
    lem (∅ , B , A) pdb = ⊥-elim (pdb-odd-length pdb)
    lem (Γ , C , B , A) pdb with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = begin
      FVTm (pdb-right-base pdb)
        ≡⟨ FVTm-≃ (pdb-right-base-prefix pdb a) ⟩
      FVTm (liftTerm (liftTerm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ supp-lift-tm (liftTerm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (FVTm (liftTerm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ cong ewf (supp-lift-tm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (ewf (FVTm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ cong ewf (cong ewf (lem (Γ , C) (pdb-prefix pdb))) ⟩
      ewf (ewf (pdb-bd-supp 0 (Γ , C) ⦃ pdb-prefix pdb ⦄ true)) ∎
        where open ≡-Reasoning
    ... | tri≈ ¬a b ¬c = begin
      FVTm (pdb-right-base pdb)
        ≡⟨ FVTm-≃ (pdb-right-base-0-dim pdb (sym b)) ⟩
      FVTm 1V
        ≡˘⟨ cong ewf (cong ewt (drop-var (pdb-right-base (pdb-prefix pdb)) ⦃ pdb-right-base-isVar (pdb-prefix pdb) ⦄)) ⟩
      ewf (ewt (drop (FVTm (pdb-right-base (pdb-prefix pdb)))))
        ≡⟨ cong ewf (cong ewt (cong drop (lem (Γ , C) (pdb-prefix pdb)))) ⟩
      ewf (ewt (drop (pdb-bd-supp 0 (Γ , C) ⦃ pdb-prefix pdb ⦄ true))) ∎
        where open ≡-Reasoning
supp-compat (suc n) Sing b = refl
supp-compat (suc n) (Join S T) b = let
  instance _ = tree-to-pd S
  instance _ = tree-to-pd T
  in begin
  connect-supp (suspSupp (supp-tree-bd n S b)) (supp-tree-bd (suc n) T b)
    ≡⟨ cong₂ (λ a b → connect-supp (suspSupp a) b) (supp-compat n S b) (supp-compat (suc n) T b) ⟩
  connect-supp
    (suspSupp (pd-bd-supp n (tree-to-ctx S) b))
    (pd-bd-supp (suc n) (tree-to-ctx T) b)
    ≡⟨ connect-susp-pd-bd-compat n (tree-to-ctx S) (tree-to-ctx T) b ⟩
  pd-bd-supp (suc n) (connect-susp (tree-to-ctx S) (tree-to-ctx T))
      ⦃ connect-susp-pd (tree-to-pd S) (tree-to-pd T) ⦄ b ∎
  where
    open ≡-Reasoning

supp-tree-bd-full : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-dim T ≤ d → supp-tree-bd d T b ≡ full
supp-tree-bd-full zero Sing false p = refl
supp-tree-bd-full zero Sing true p = refl
supp-tree-bd-full zero (Join S T) b p with tree-dim T
supp-tree-bd-full zero (Join S T) b () | zero
supp-tree-bd-full zero (Join S T) b () | suc x
supp-tree-bd-full (suc d) Sing b p = refl
supp-tree-bd-full (suc d) (Join S T) b p = begin
  connect-supp (suspSupp (supp-tree-bd d S b)) (supp-tree-bd (suc d) T b)
    ≡⟨ cong₂ (λ a b → connect-supp (suspSupp a) b) (supp-tree-bd-full d S b {!!}) (supp-tree-bd-full (suc d) T b (m⊔n≤o⇒n≤o (suc (tree-dim S)) (tree-dim T) {!!})) ⟩
  connect-supp (suspSupp full) full
    ≡⟨ cong (λ - → connect-supp - full) suspSuppFull ⟩
  connect-supp full full
    ≡⟨ connect-supp-full (suc (suc _)) _ ⟩
  full ∎
  where
    open ≡-Reasoning

supp-tree-bd-compat : (d : ℕ) → (T : Tree n) → (b : Bool) → FVSub (tree-inc d T b) ≡ supp-tree-bd d T b
supp-tree-bd-compat zero T false = ∪-left-unit (trueAt (fromℕ _))
supp-tree-bd-compat zero T true = trans (∪-left-unit (FVTm (tree-last-var T))) {!!}
supp-tree-bd-compat (suc d) Sing b = refl
supp-tree-bd-compat (suc d) (Join S T) b = trans (sub-between-connect-susps-supp (tree-inc d S b) (tree-inc (suc d) T b) (tree-inc-preserve-fst-var d T b)) (cong₂ (λ a b → connect-supp (suspSupp a) b) (supp-tree-bd-compat d S b) (supp-tree-bd-compat (suc d) T b))

linear-tree-supp-lem : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → .(tree-dim T ≡ suc d) → supp-tree-bd d T false ∪ supp-tree-bd d T true ∪ ewt empty ≡ full
linear-tree-supp-lem zero Sing p = refl
linear-tree-supp-lem zero (Join Sing Sing) p = refl
linear-tree-supp-lem zero (Join (Join S T) Sing) p with .(join-tree-has-non-zero-dim S T {!!})
... | ()
linear-tree-supp-lem (suc d) (Join T Sing) p = begin
  suspSupp (supp-tree-bd d T false) ∪ suspSupp (supp-tree-bd d T true) ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) (suspSupp∪ (supp-tree-bd d T false) (supp-tree-bd d T true)) ⟩
  suspSupp (supp-tree-bd d T false ∪ supp-tree-bd d T true) ∪ ewt empty
    ≡⟨ lem (supp-tree-bd d T false ∪ supp-tree-bd d T true) ⟩
  suspSupp (supp-tree-bd d T false ∪ supp-tree-bd d T true ∪ ewt empty)
    ≡⟨ cong suspSupp (linear-tree-supp-lem d T {!!}) ⟩
  suspSupp full
    ≡⟨ suspSuppFull ⟩
  full ∎
  where
    open ≡-Reasoning
    lem : (xs : VarSet (suc n)) → suspSupp xs ∪ ewt empty ≡ suspSupp (xs ∪ ewt empty)
    lem (x ∷ xs) = cong ((x ∨ true) ∷_) (trans (∪-right-unit (suspSupp xs)) (cong suspSupp (sym (∪-right-unit xs))))

supp-tree-bd-include-fst : (d : ℕ) → (T : Tree n) → (b : Bool) → Truth (lookup-isVar (supp-tree-bd (suc d) T b) (Var (fromℕ _)))
supp-tree-bd-include-fst d Sing b = tt
supp-tree-bd-include-fst d (Join S T) b = connect-supp-fst (suspSupp (supp-tree-bd d S b)) (supp-tree-bd (suc d) T b) (suspSuppFstTruth (supp-tree-bd d S b))

supp-tree-bd-include-last : (d : ℕ) → (T : Tree n) → (b : Bool) → FVTm (tree-last-var T) ⊆ supp-tree-bd (suc d) T b
supp-tree-bd-include-last d Sing b = ⊆-refl
supp-tree-bd-include-last d (Join S T) b = begin
  FVTm (tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm)
    ≡˘⟨ TransportVarSet-tm (tree-last-var T) (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
  TransportVarSet (FVTm (tree-last-var T))
    (connect-susp-inc-right (tree-size S) (tree-size T))
    ≤⟨ ⊆-TransportVarSet (connect-susp-inc-right (tree-size S) (tree-size T)) (supp-tree-bd-include-last d T b) ⟩
  TransportVarSet (supp-tree-bd (suc d) T b) (connect-inc-right getSnd _)
    ≤⟨ ∪-⊆-2 (TransportVarSet (suspSupp (supp-tree-bd d S b))
               (connect-inc-left getSnd _)) (TransportVarSet (supp-tree-bd (suc d) T b) (connect-inc-right getSnd _)) ⟩
  TransportVarSet (suspSupp (supp-tree-bd d S b))
    (connect-inc-left getSnd _)
    ∪
    TransportVarSet (supp-tree-bd (suc d) T b) (connect-inc-right getSnd _)
    ≡⟨ connect-supp-incs (suspSupp (supp-tree-bd d S b)) getSnd (supp-tree-bd (suc d) T b) (suspSuppSnd (supp-tree-bd d S b)) ⟩
  connect-supp (suspSupp (supp-tree-bd d S b)) (supp-tree-bd (suc d) T b) ∎
  where
    open PReasoning (⊆-poset _)

connect-tree-to-ctx-supp : (d : ℕ) → (S : Tree n) → (T : Tree m) → (b : Bool)
                         → TransportVarSet (connect-supp (supp-tree-bd (suc d) S b) (supp-tree-bd (suc d) T b))
                                           (idSub≃ (sym≃c (connect-tree-to-ctx S T)))
                         ≡ supp-tree-bd (suc d) (connect-tree S T) b
connect-tree-to-ctx-supp d S T b = P.Pointwise-≡⇒≡ (P.trans trans (TransportVarSet-idSub≃ (connect-supp (supp-tree-bd (suc d) S b) (supp-tree-bd (suc d) T b)) (sym≃c (connect-tree-to-ctx S T))) (lem d S T b))
  where
    lem : (d : ℕ) → (S : Tree n) → (T : Tree m) → (b : Bool)
        → connect-supp (supp-tree-bd (suc d) S b) (supp-tree-bd (suc d) T b) ≡ᵖ supp-tree-bd (suc d) (connect-tree S T) b
    lem d Sing T b = connect-supp-unit-left (supp-tree-bd (suc d) T b) (supp-tree-bd-include-fst d T b)
    lem d (Join S₁ S₂) T b = P.trans trans (connect-supp-assoc (suspSupp (supp-tree-bd d S₁ b)) (supp-tree-bd (suc d) S₂ b) (supp-tree-bd (suc d) T b)) (connect-supp-≡ᵖ (P.refl refl) (lem d S₂ T b))
