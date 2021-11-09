{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Suspension.Support where

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Syntax
open import Data.Nat
open import Data.Vec
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (fromℕ; inject₁; Fin; zero; suc)
open import Data.Bool renaming (T to Truth)
open import Data.Bool.Properties
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Tree
open import Catt.Tree.Properties
open import Data.Unit
import Relation.Binary.Reasoning.PartialOrder as PReasoning
open import Catt.Globular
open import Catt.Syntax.SyntacticEquality

suspSupp∪ : (vs vs′ : VarSet n) → suspSupp vs ∪ suspSupp vs′ ≡ suspSupp (vs ∪ vs′)
suspSupp∪ emp emp = refl
suspSupp∪ (x ∷ xs) (y ∷ ys) = cong₂ _∷_ refl (suspSupp∪ xs ys)

suspSuppLem : (n : ℕ) → empty ∪ ewf (trueAt (fromℕ n)) ∪ trueAt (inject₁ (fromℕ n)) ≡ suspSupp empty
suspSuppLem zero = refl
suspSuppLem (suc n) = cong (ewf) (suspSuppLem n)

suspSuppFstTruth : (xs : VarSet n) → Truth (lookup-isVar (suspSupp xs) getFst)
suspSuppFstTruth emp = tt
suspSuppFstTruth (x ∷ xs) = suspSuppFstTruth xs

suspSuppSndTruth : (xs : VarSet n) → Truth (lookup-isVar (suspSupp xs) getSnd)
suspSuppSndTruth emp = tt
suspSuppSndTruth (x ∷ xs) = suspSuppSndTruth xs

suspSuppSnd : (xs : VarSet n) → FVTm getSnd ⊆ suspSupp xs
suspSuppSnd emp = refl
suspSuppSnd (x ∷ xs) = cong₂ _∷_ (sym (∨-identityʳ x)) (suspSuppSnd xs)

suspSuppEmpRight : (xs : VarSet n) → suspSupp xs ≡ suspSupp xs ∪ suspSupp empty
suspSuppEmpRight xs = sym (trans (suspSupp∪ xs empty) (cong suspSupp (∪-right-unit xs)))

suspSuppTy : (A : Ty n) → FVTy (suspTy A) ≡ suspSupp (FVTy A)
suspSuppTm : (t : Tm n) → (suspSupp empty) ∪ FVTm (suspTm t) ≡ suspSupp (FVTm t)
suspSuppSub : (σ : Sub n m ⋆) → FVSub (suspSub σ) ≡ suspSupp (FVSub σ)
suspSuppTyTm : (A : Ty n) → (t : Tm n) → FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ suspSupp (FVTy A ∪ FVTm t)

suspSuppTy ⋆ = suspSuppLem _
suspSuppTy (s ─⟨ A ⟩⟶ t) = begin
  FVTy (suspTy (s ─⟨ A ⟩⟶ t)) ≡⟨⟩
  FVTy (suspTy A) ∪ FVTm (suspTm s) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppTyTm A s) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVTy A ∪ FVTm s)) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVTy A ∪ FVTm s)) (suspSupp empty) (FVTm (suspTm t)) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪
    (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVTy A ∪ FVTm s) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  suspSupp (FVTy (s ─⟨ A ⟩⟶ t)) ∎
  where
    open ≡-Reasoning

suspSuppTyTm A t = begin
  FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppTy A) ⟩
  suspSupp (FVTy A) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVTy A)) ⟩
  suspSupp (FVTy A) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVTy A)) (suspSupp empty) (FVTm (suspTm t)) ⟩
  suspSupp (FVTy A) ∪ (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVTy A) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVTy A) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVTy A) (FVTm t) ⟩
  suspSupp (FVTy A ∪ FVTm t) ∎
  where
    open ≡-Reasoning


suspSuppTm (Var i) = lem _ i
  where
    lem : (n : ℕ) → (i : Fin n) → suspSupp empty ∪ trueAt (inject₁ (inject₁ i)) ≡ suspSupp (trueAt i)
    lem (suc n) zero = cong ewt (∪-right-unit (suspSupp empty))
    lem (suc n) (suc i) = cong ewf (lem n i)
suspSuppTm (Coh Δ A σ) = trans (∪-comm (suspSupp empty) (FVTm (suspTm (Coh Δ A σ)))) (trans (cong (_∪ suspSupp empty) (suspSuppSub σ)) (sym (suspSuppEmpRight (FVSub σ))))

suspSuppSub ⟨⟩ = suspSuppLem _
suspSuppSub ⟨ σ , t ⟩ = begin
  FVSub (suspSub ⟨ σ , t ⟩) ≡⟨⟩
  FVSub (suspSub σ) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppSub σ) ⟩
  suspSupp (FVSub σ) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVSub σ)) ⟩
  suspSupp (FVSub σ) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVSub σ)) (suspSupp empty) (FVTm (suspTm t)) ⟩
  suspSupp (FVSub σ) ∪ (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVSub σ) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVSub σ) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVSub σ) (FVTm t) ⟩
  suspSupp (FVSub ⟨ σ , t ⟩) ∎
  where
    open ≡-Reasoning

suspSuppFull : suspSupp (full {n}) ≡ full
suspSuppFull {zero} = refl
suspSuppFull {suc n} = cong ewt suspSuppFull

suspSuppCondition : {b : Bool} → {A : Ty (suc n)} → {T : Tree n} → supp-condition b A T → supp-condition b (suspTy A) (suspTree T)
suspSuppCondition {b = false} {A} {T} sc = begin
  FVTy (suspTy A) ≡⟨ suspSuppTy A ⟩
  suspSupp (FVTy A) ≡⟨ cong suspSupp sc ⟩
  suspSupp full ≡⟨ suspSuppFull ⟩
  full ∎
  where
    open ≡-Reasoning
suspSuppCondition {b = true} {s ─⟨ A ⟩⟶ t} {T} (nz ,, sc1 ,, sc2) = it ,, l1 ,, l2
  where
    instance _ = nz
    open ≡-Reasoning
    suc-pred : (n : ℕ) → .⦃ NonZero′ n ⦄ → suc (pred n) ≡ n
    suc-pred (suc n) = refl

    l1 : FVTy (suspTy A) ∪ FVTm (suspTm s) ≡ supp-bd (tree-dim T) (suspTree T) false
    l1 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm s) ≡⟨ suspSuppTyTm A s ⟩
      suspSupp (FVTy A ∪ FVTm s) ≡⟨ cong suspSupp sc1 ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T false) ≡⟨ suspSuppBd (pred (tree-dim T)) T false ⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) false ≡⟨ cong (λ - → supp-bd - (suspTree T) false) (suc-pred (tree-dim T)) ⟩
      supp-bd (tree-dim T) (suspTree T) false ∎

    l2 : FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ supp-bd (tree-dim T) (suspTree T) true
    l2 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ suspSuppTyTm A t ⟩
      suspSupp (FVTy A ∪ FVTm t) ≡⟨ cong suspSupp sc2 ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T true) ≡⟨ suspSuppBd (pred (tree-dim T)) T true ⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) true ≡⟨ cong (λ - → supp-bd - (suspTree T) true) (suc-pred (tree-dim T)) ⟩
      supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true ∎

TransportVarSet-susp : (xs : VarSet n) → (σ : Sub n m ⋆) → TransportVarSet (suspSupp xs) (suspSub σ) ≡ suspSupp (TransportVarSet xs σ)
TransportVarSet-susp emp ⟨⟩ = suspSuppLem _
TransportVarSet-susp (ewf xs) ⟨ σ , t ⟩ = TransportVarSet-susp xs σ
TransportVarSet-susp (ewt xs) ⟨ σ , t ⟩ = begin
  TransportVarSet (suspSupp xs) (suspSub σ) ∪ FVTm (suspTm t)
    ≡⟨ cong (_∪ FVTm (suspTm t)) (trans (TransportVarSet-susp xs σ) (suspSuppEmpRight (TransportVarSet xs σ))) ⟩
  suspSupp (TransportVarSet xs σ) ∪ suspSupp empty ∪ FVTm (suspTm t)
    ≡⟨ ∪-assoc (suspSupp (TransportVarSet xs σ)) (suspSupp empty) (FVTm (suspTm t)) ⟩
  suspSupp (TransportVarSet xs σ) ∪ (suspSupp empty ∪ FVTm (suspTm t))
    ≡⟨ cong (suspSupp (TransportVarSet xs σ) ∪_) (suspSuppTm t) ⟩
  suspSupp (TransportVarSet xs σ) ∪ suspSupp (FVTm t)
    ≡⟨ suspSupp∪ (TransportVarSet xs σ) (FVTm t) ⟩
  suspSupp (TransportVarSet xs σ ∪ FVTm t) ∎
  where
    open ≡-Reasoning

suspSuppTyContainsEmpty : (A : Ty n) → suspSupp empty ⊆ FVTy (suspTy A)
suspSuppTyContainsEmpty ⋆ = ⊆-reflexive (sym (suspSuppLem _))
suspSuppTyContainsEmpty (s ─⟨ A ⟩⟶ t) = begin
  suspSupp empty
    ≤⟨ suspSuppTyContainsEmpty A ⟩
  FVTy (suspTy A)
    ≤⟨ ∪-⊆-1 (FVTy (suspTy A)) (FVTm (suspTm s)) ⟩
  FVTy (suspTy A) ∪ FVTm (suspTm s)
    ≤⟨ ∪-⊆-1 (FVTy (suspTy A) ∪ FVTm (suspTm s)) (FVTm (suspTm t)) ⟩
  FVTy (suspTy A) ∪ FVTm (suspTm s) ∪ FVTm (suspTm t) ∎
  where
    open PReasoning (⊆-poset _)

suspSuppTmContainsEmpty : (Γ : Ctx n) → (t : Tm n) → suspSupp empty ⊆ SuppTm (suspCtx Γ) (suspTm t)
suspSuppTmContainsEmpty Γ t = begin
  suspSupp empty
    ≤⟨ suspSuppTyContainsEmpty (tm-to-ty Γ t) ⟩
  FVTy (suspTy (tm-to-ty Γ t))
    ≤⟨ DC-⊆ (suspCtx Γ) (FVTy (suspTy (tm-to-ty Γ t))) ⟩
  SuppTy (suspCtx Γ) (suspTy (tm-to-ty Γ t))
    ≡⟨ cong (SuppTy (suspCtx Γ)) (≃ty-to-≡ (tm-to-ty-susp t Γ)) ⟩
  SuppTy (suspCtx Γ) (tm-to-ty (suspCtx Γ) (suspTm t))
    ≤⟨ SuppContainsType (suspTm t) (suspCtx Γ) ⟩
  SuppTm (suspCtx Γ) (suspTm t) ∎
  where
    open PReasoning (⊆-poset _)

DC-suspSupp : (Γ : Ctx n) → (xs : VarSet n) → DC (suspCtx Γ) (suspSupp xs) ≡ suspSupp (DC Γ xs)
DC-suspSupp ∅ emp = refl
DC-suspSupp (Γ , A) (ewf xs) = cong ewf (DC-suspSupp Γ xs)
DC-suspSupp (Γ , A) (ewt xs) = cong ewt (begin
  DC (suspCtx Γ) (suspSupp xs ∪ FVTy (suspTy A))
    ≡⟨ cong (DC (suspCtx Γ)) lem ⟩
  DC (suspCtx Γ) (suspSupp (xs ∪ FVTy A))
    ≡⟨ DC-suspSupp Γ (xs ∪ FVTy A) ⟩
  suspSupp (DC Γ (xs ∪ FVTy A)) ∎)
  where
    open ≡-Reasoning
    lem : suspSupp xs ∪ FVTy (suspTy A) ≡ suspSupp (xs ∪ FVTy A)
    lem = begin
      suspSupp xs ∪ FVTy (suspTy A)
        ≡⟨ cong (suspSupp xs ∪_) (suspSuppTy A) ⟩
      suspSupp xs ∪ suspSupp (FVTy A)
        ≡⟨ suspSupp∪ xs (FVTy A) ⟩
      suspSupp (xs ∪ FVTy A) ∎

suspSuppTm′ : (Γ : Ctx n) → (t : Tm n) → SuppTm (suspCtx Γ) (suspTm t) ≡ suspSupp (SuppTm Γ t)
suspSuppTm′ Γ t = begin
  SuppTm (suspCtx Γ) (suspTm t)
    ≡⟨ suspSuppTmContainsEmpty Γ t ⟩
  SuppTm (suspCtx Γ) (suspTm t) ∪ suspSupp empty
    ≡⟨ ∪-comm (DC (suspCtx Γ) (FVTm (suspTm t))) (suspSupp empty) ⟩
  suspSupp empty ∪ SuppTm (suspCtx Γ) (suspTm t)
    ≡˘⟨ cong (_∪ SuppTm (suspCtx Γ) (suspTm t)) (trans (DC-suspSupp Γ empty) (cong suspSupp (DC-empty Γ))) ⟩
  DC (suspCtx Γ) (suspSupp empty) ∪ DC (suspCtx Γ) (FVTm (suspTm t))
    ≡˘⟨ DC-cup (suspCtx Γ) (suspSupp empty) (FVTm (suspTm t)) ⟩
  DC (suspCtx Γ) (suspSupp empty ∪ FVTm (suspTm t))
    ≡⟨ cong (DC (suspCtx Γ)) (suspSuppTm t) ⟩
  DC (suspCtx Γ) (suspSupp (FVTm t))
    ≡⟨ DC-suspSupp Γ (FVTm t) ⟩
  suspSupp (SuppTm Γ t) ∎
  where
    open ≡-Reasoning

SuspSuppTmProp : (s t : Tm n) → SuppTm Γ s ≡ SuppTm Γ t → SuppTm (suspCtx Γ) (suspTm s) ≡ SuppTm (suspCtx Γ) (suspTm t)
SuspSuppTmProp {Γ = Γ} s t p = begin
  SuppTm (suspCtx Γ) (suspTm s)
    ≡⟨ suspSuppTm′ Γ s ⟩
  suspSupp (SuppTm Γ s)
    ≡⟨ cong suspSupp p ⟩
  suspSupp (SuppTm Γ t)
    ≡˘⟨ suspSuppTm′ Γ t ⟩
  SuppTm (suspCtx Γ) (suspTm t) ∎
  where
    open ≡-Reasoning
