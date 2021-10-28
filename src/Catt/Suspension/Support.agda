{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Suspension.Support where

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Dimension
open import Catt.Syntax
open import Data.Nat
open import Data.Vec
open import Catt.Suspension
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (fromℕ; inject₁; Fin; zero; suc)
open import Data.Bool renaming (T to Truth)
open import Data.Bool.Properties
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Tree
open import Catt.Tree.Properties
open import Data.Unit


suspSupp∪ : (vs vs′ : VarSet n) → suspSupp vs ∪ suspSupp vs′ ≡ suspSupp (vs ∪ vs′)
suspSupp∪ emp emp = refl
suspSupp∪ (x ∷ xs) (y ∷ ys) = cong₂ _∷_ refl (suspSupp∪ xs ys)

-- suspSuppLem : (n : ℕ) → empty ∪ ewf (trueAt (fromℕ n)) ∪ trueAt (inject₁ (fromℕ n)) ≡ suspSupp empty
-- suspSuppLem zero = refl
-- suspSuppLem (suc n) = cong (ewf) (suspSuppLem n)

suspSuppLem : (Γ : Ctx n) → Supp (CtxTm getFst (suspCtx Γ)) ∪ Supp (CtxTm getSnd (suspCtx Γ)) ≡ suspSupp empty
suspSuppLem ∅ = refl
suspSuppLem (Γ , A) = cong ewf (suspSuppLem Γ)

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

Supp-unrestrict : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → (Γ : Ctx m) → Supp (CtxSub (unrestrict σ) Γ) ≡ Supp (CtxSub σ Γ)
Supp-unrestrict ⟨⟩ Γ = refl
Supp-unrestrict ⟨ σ , t ⟩ Γ = cong (_∪ Supp (CtxTm t Γ)) (Supp-unrestrict σ Γ)

suspCtxSyntax : CtxSyntax n → CtxSyntax (2 + n)
suspCtxSyntax (CtxTm t Γ) = CtxTm (suspTm t) (suspCtx Γ)
suspCtxSyntax (CtxTy A Γ) = CtxTy (suspTy A) (suspCtx Γ)
suspCtxSyntax (CtxSub σ Γ) = CtxSub (suspSubRes σ) (suspCtx Γ)

suspSuppComp : (x : CtxSyntax n) → Supp (suspCtxSyntax x) ≡ suspSupp (Supp x)
suspSuppComp = ≺-rec (λ x → Supp (suspCtxSyntax x) ≡ suspSupp (Supp x)) r
  where
    open ≡-Reasoning
    r : (x : CtxSyntax n)
      → (∀ {m} → (y : CtxSyntax m) → y ≺ x → Supp (suspCtxSyntax y) ≡ suspSupp (Supp y))
      → Supp (suspCtxSyntax x) ≡ suspSupp (Supp x)
    r (CtxTm (Var zero) (Γ , A)) rec = cong ewt (rec (CtxTy A Γ) Tm1)
    r (CtxTm (Var (suc i)) (Γ , A)) rec = cong ewf (rec (CtxTm (Var i) Γ) Tm2)
    r (CtxTm (Coh S A σ) Γ) rec = begin
      Supp (CtxSub (suspSub σ) (suspCtx Γ)) ≡⟨ Supp-unrestrict (suspSubRes σ) (suspCtx Γ) ⟩
      Supp (CtxSub (suspSubRes σ) (suspCtx Γ)) ≡⟨ rec (CtxSub σ Γ) Tm4 ⟩
      suspSupp (Supp (CtxTm (Coh S A σ) Γ)) ∎
    r (CtxTy ⋆ Γ) rec = begin
      empty ∪ Supp (CtxTm getFst (suspCtx Γ)) ∪ Supp (CtxTm getSnd (suspCtx Γ))
        ≡⟨ cong (_∪ Supp (CtxTm getSnd (suspCtx Γ))) (∪-left-unit (Supp (CtxTm getFst (suspCtx Γ)))) ⟩
      Supp (CtxTm getFst (suspCtx Γ)) ∪ Supp (CtxTm getSnd (suspCtx Γ))
        ≡⟨ suspSuppLem Γ ⟩
      suspSupp empty ∎
    r (CtxTy (s ─⟨ A ⟩⟶ t) Γ) rec = begin
      Supp (CtxTy (suspTy A) (suspCtx Γ)) ∪ Supp (CtxTm (suspTm s) (suspCtx Γ)) ∪ Supp (CtxTm (suspTm t) (suspCtx Γ)) ≡⟨ cong₂ _∪_ (cong₂ _∪_ (rec (CtxTy A Γ) Ty2) (rec (CtxTm s Γ) Ty1)) (rec (CtxTm t Γ) Ty3) ⟩
      suspSupp (Supp (CtxTy A Γ)) ∪ suspSupp (Supp (CtxTm s Γ)) ∪
        suspSupp (Supp (CtxTm t Γ)) ≡⟨ cong (_∪ suspSupp (Supp (CtxTm t Γ))) (suspSupp∪ (Supp (CtxTy A Γ)) (Supp (CtxTm s Γ))) ⟩
      suspSupp (Supp (CtxTy A Γ) ∪ Supp (CtxTm s Γ)) ∪
        suspSupp (Supp (CtxTm t Γ)) ≡⟨ suspSupp∪ (Supp (CtxTy A Γ) ∪ Supp (CtxTm s Γ)) (Supp (CtxTm t Γ)) ⟩
      suspSupp (Supp (CtxTy A Γ) ∪ Supp (CtxTm s Γ) ∪ Supp (CtxTm t Γ)) ∎
    r (CtxSub ⟨⟩ Γ) rec = rec (CtxTy _ Γ) Sub1
    r (CtxSub ⟨ σ , t ⟩ Γ) rec = begin
      Supp (CtxSub (suspSubRes σ) (suspCtx Γ)) ∪ Supp (CtxTm (suspTm t) (suspCtx Γ))
        ≡⟨ cong₂ _∪_ (rec (CtxSub σ Γ) Sub2) (rec (CtxTm t Γ) Sub3) ⟩
      suspSupp (Supp (CtxSub σ Γ)) ∪ suspSupp (Supp (CtxTm t Γ)) ≡⟨ suspSupp∪ (Supp (CtxSub σ Γ)) (Supp (CtxTm t Γ)) ⟩
      suspSupp (Supp (CtxSub σ Γ) ∪ Supp (CtxTm t Γ)) ∎

-- suspSuppTy : (A : Ty n) → FVTy (suspTy A) ≡ suspSupp (FVTy A)
-- suspSuppTm : (t : Tm n) → FVTm (suspTm t) ≡ suspSupp (FVTm t)
-- suspSuppSub : (σ : Sub n m ⋆) → FVSub (suspSub σ) ≡ suspSupp (FVSub σ)
-- suspSuppTyTm : (A : Ty n) → (t : Tm n) → FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ suspSupp (FVTy A ∪ FVTm t)

-- suspSuppTy ⋆ = suspSuppLem _
-- suspSuppTy (s ─⟨ A ⟩⟶ t) = begin
--   FVTy (suspTy (s ─⟨ A ⟩⟶ t)) ≡⟨⟩
--   FVTy (suspTy A) ∪ FVTm (suspTm s) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppTyTm A s) ⟩
--   suspSupp (FVTy A ∪ FVTm s) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVTy A ∪ FVTm s)) ⟩
--   suspSupp (FVTy A ∪ FVTm s) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVTy A ∪ FVTm s)) (suspSupp empty) (FVTm (suspTm t)) ⟩
--   suspSupp (FVTy A ∪ FVTm s) ∪
--     (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVTy A ∪ FVTm s) ∪_) (suspSuppTm t) ⟩
--   suspSupp (FVTy A ∪ FVTm s) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVTy A ∪ FVTm s) (FVTm t) ⟩
--   suspSupp (FVTy (s ─⟨ A ⟩⟶ t)) ∎
--   where
--     open ≡-Reasoning

-- suspSuppTyTm A t = begin
--   FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppTy A) ⟩
--   suspSupp (FVTy A) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVTy A)) ⟩
--   suspSupp (FVTy A) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVTy A)) (suspSupp empty) (FVTm (suspTm t)) ⟩
--   suspSupp (FVTy A) ∪ (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVTy A) ∪_) (suspSuppTm t) ⟩
--   suspSupp (FVTy A) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVTy A) (FVTm t) ⟩
--   suspSupp (FVTy A ∪ FVTm t) ∎
--   where
--     open ≡-Reasoning


-- suspSuppTm (Var i) = lem _ i
--   where
--     lem : (n : ℕ) → (i : Fin n) → suspSupp empty ∪ trueAt (inject₁ (inject₁ i)) ≡ suspSupp (trueAt i)
--     lem (suc n) zero = cong ewt (∪-right-unit (suspSupp empty))
--     lem (suc n) (suc i) = cong ewf (lem n i)
-- suspSuppTm (Coh Δ A σ) = trans (∪-comm (suspSupp empty) (FVTm (suspTm (Coh Δ A σ)))) (trans (cong (_∪ suspSupp empty) (suspSuppSub σ)) (sym (suspSuppEmpRight (FVSub σ))))

-- suspSuppSub ⟨⟩ = suspSuppLem _
-- suspSuppSub ⟨ σ , t ⟩ = begin
--   FVSub (suspSub ⟨ σ , t ⟩) ≡⟨⟩
--   FVSub (suspSub σ) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppSub σ) ⟩
--   suspSupp (FVSub σ) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVSub σ)) ⟩
--   suspSupp (FVSub σ) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVSub σ)) (suspSupp empty) (FVTm (suspTm t)) ⟩
--   suspSupp (FVSub σ) ∪ (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVSub σ) ∪_) (suspSuppTm t) ⟩
--   suspSupp (FVSub σ) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVSub σ) (FVTm t) ⟩
--   suspSupp (FVSub ⟨ σ , t ⟩) ∎
--   where
--     open ≡-Reasoning

suspSuppFull : suspSupp (full {n}) ≡ full
suspSuppFull {zero} = refl
suspSuppFull {suc n} = cong ewt suspSuppFull

suspSuppCondition : {b : Bool} → {A : Ty (suc n)} → {T : Tree n} → supp-condition b A T → supp-condition b (suspTy A) (suspTree T)
suspSuppCondition {b = false} {A} {T} sc = begin
  Supp (CtxTy (suspTy A) (suspCtx (tree-to-ctx T))) ≡⟨ suspSuppComp (CtxTy A (tree-to-ctx T)) ⟩
  suspSupp (Supp (CtxTy A (tree-to-ctx T))) ≡⟨ cong suspSupp sc ⟩
  suspSupp full ≡⟨ suspSuppFull ⟩
  full ∎
  -- FVTy (suspTy A) ≡⟨ suspSuppTy A ⟩
  -- suspSupp (FVTy A) ≡⟨ cong suspSupp sc ⟩
  -- suspSupp full ≡⟨ suspSuppFull ⟩
  -- full ∎
  where
    open ≡-Reasoning
suspSuppCondition {b = true} {s ─⟨ A ⟩⟶ t} {T} (nz ,, sc1 ,, sc2) = it ,, l1 ,, l2
  where
    instance _ = nz
    open ≡-Reasoning
    suc-pred : (n : ℕ) → .⦃ NonZero′ n ⦄ → suc (pred n) ≡ n
    suc-pred (suc n) = refl

    l1 : Supp (CtxTm (suspTm s) (tree-to-ctx (suspTree T))) ≡ supp-bd (tree-dim T) (suspTree T) false
    l1 = begin
      Supp (CtxTm (suspTm s) (suspCtx (tree-to-ctx T))) ≡⟨ suspSuppComp (CtxTm s (tree-to-ctx T)) ⟩
      suspSupp (Supp (CtxTm s (tree-to-ctx T))) ≡⟨ cong suspSupp sc1 ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T false) ≡⟨⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) false
        ≡⟨ cong (λ - → supp-bd - (suspTree T) false) (suc-pred (tree-dim T)) ⟩
      supp-bd (tree-dim T) (suspTree T) false ∎
      -- FVTy (suspTy A) ∪ FVTm (suspTm s) ≡⟨ suspSuppTyTm A s ⟩
      -- suspSupp (FVTy A ∪ FVTm s) ≡⟨ cong suspSupp sc1 ⟩
      -- suspSupp (supp-bd (pred (tree-dim T)) T false) ≡⟨ suspSuppBd (pred (tree-dim T)) T false ⟩
      -- supp-bd (suc (pred (tree-dim T))) (suspTree T) false ≡⟨ cong (λ - → supp-bd - (suspTree T) false) (suc-pred (tree-dim T)) ⟩
      -- supp-bd (tree-dim T) (suspTree T) false ∎

    l2 : Supp (CtxTm (suspTm t) (tree-to-ctx (suspTree T))) ≡ supp-bd (tree-dim T) (suspTree T) true
    l2 = begin
      Supp (CtxTm (suspTm t) (suspCtx (tree-to-ctx T))) ≡⟨ suspSuppComp (CtxTm t (tree-to-ctx T)) ⟩
      suspSupp (Supp (CtxTm t (tree-to-ctx T))) ≡⟨ cong suspSupp sc2 ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T true) ≡⟨⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) true
        ≡⟨ cong (λ - → supp-bd - (suspTree T) true) (suc-pred (tree-dim T)) ⟩
      supp-bd (tree-dim T) (suspTree T) true ∎
      -- FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ suspSuppTyTm A t ⟩
      -- suspSupp (FVTy A ∪ FVTm t) ≡⟨ cong suspSupp sc2 ⟩
      -- suspSupp (supp-bd (pred (tree-dim T)) T true) ≡⟨ suspSuppBd (pred (tree-dim T)) T true ⟩
      -- supp-bd (suc (pred (tree-dim T))) (suspTree T) true ≡⟨ cong (λ - → supp-bd - (suspTree T) true) (suc-pred (tree-dim T)) ⟩
      -- supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true ∎

-- TransportVarSet-susp : (xs : VarSet n) → (σ : Sub n m ⋆) → TransportVarSet (suspSupp xs) (suspSub σ) ≡ suspSupp (TransportVarSet xs σ)
-- TransportVarSet-susp emp ⟨⟩ = suspSuppLem _
-- TransportVarSet-susp (ewf xs) ⟨ σ , t ⟩ = TransportVarSet-susp xs σ
-- TransportVarSet-susp (ewt xs) ⟨ σ , t ⟩ = begin
--   TransportVarSet (suspSupp xs) (suspSub σ) ∪ FVTm (suspTm t)
--     ≡⟨ cong (_∪ FVTm (suspTm t)) (trans (TransportVarSet-susp xs σ) (suspSuppEmpRight (TransportVarSet xs σ))) ⟩
--   suspSupp (TransportVarSet xs σ) ∪ suspSupp empty ∪ FVTm (suspTm t)
--     ≡⟨ ∪-assoc (suspSupp (TransportVarSet xs σ)) (suspSupp empty) (FVTm (suspTm t)) ⟩
--   suspSupp (TransportVarSet xs σ) ∪ (suspSupp empty ∪ FVTm (suspTm t))
--     ≡⟨ cong (suspSupp (TransportVarSet xs σ) ∪_) (suspSuppTm t) ⟩
--   suspSupp (TransportVarSet xs σ) ∪ suspSupp (FVTm t)
--     ≡⟨ suspSupp∪ (TransportVarSet xs σ) (FVTm t) ⟩
--   suspSupp (TransportVarSet xs σ ∪ FVTm t) ∎
--   where
--     open ≡-Reasoning
