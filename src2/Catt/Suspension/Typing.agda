{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Suspension.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Data.Fin.Properties using (toℕ-inject₁)
open import Catt.Typing.Properties index rule props
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (drop)
open import Data.Bool

suspSupp : VarSet n → VarSet (2 + n)
suspSupp [] = full
suspSupp (x ∷ vs) = x ∷ suspSupp vs

suspSupp∪ : (vs vs′ : VarSet n) → suspSupp vs ∪ suspSupp vs′ ≡ suspSupp (vs ∪ vs′)
suspSupp∪ emp emp = refl
suspSupp∪ (x ∷ xs) (y ∷ ys) = cong₂ _∷_ refl (suspSupp∪ xs ys)

suspSuppLem : (n : ℕ) → empty ∪ ewf (trueAt (fromℕ n)) ∪ trueAt (inject₁ (fromℕ n)) ≡ suspSupp empty
suspSuppLem zero = refl
suspSuppLem (suc n) = cong (ewf) (suspSuppLem n)

suspSuppEmpRight : (xs : VarSet n) → suspSupp xs ≡ suspSupp xs ∪ suspSupp empty
suspSuppEmpRight xs = sym (trans (suspSupp∪ xs empty) (cong suspSupp (∪-right-unit xs)))

suspSuppTy : (A : Ty n d) → FVTy (suspTy A) ≡ suspSupp (FVTy A)
suspSuppTm : (t : Tm n) → (suspSupp empty) ∪ FVTm (suspTm t) ≡ suspSupp (FVTm t)
suspSuppSub : (σ : Sub n m) → (suspSupp empty) ∪ FVSub (suspSub σ) ≡ suspSupp (FVSub σ)
suspSuppTyTm : (A : Ty n d) → (t : Tm n) → FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ suspSupp (FVTy A ∪ FVTm t)

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
suspSuppTm (Coh Δ A σ) = suspSuppSub σ

suspSuppSub ⟨⟩ = trans (cong (suspSupp empty ∪_) (suspSuppLem _)) (∪-idem (suspSupp empty))
suspSuppSub ⟨ σ , t ⟩ = begin
  suspSupp empty ∪ FVSub (suspSub ⟨ σ , t ⟩) ≡⟨⟩
  suspSupp empty ∪ (FVSub (suspSub σ) ∪ FVTm (suspTm t)) ≡˘⟨ ∪-assoc (suspSupp empty) (FVSub (suspSub σ)) (FVTm (suspTm t)) ⟩
  suspSupp empty ∪ FVSub (suspSub σ) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppSub σ) ⟩
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

suspSuppDrop : (xs : VarSet (suc n)) → suspSupp (drop xs) ≡ drop (suspSupp xs)
suspSuppDrop (x ∷ xs) = refl

suspSuppSrcPdb : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ _ : NonZero′ (submax + d) ⦄ → suspSupp (supp-pdb-src pdb) ≡ supp-pdb-src (susp-pdb pdb)
suspSuppSrcPdb (Extend {submax = zero} pdb p q) = cong ewf (cong ewf suspSuppFull)
suspSuppSrcPdb (Extend {submax = suc zero} pdb p q) = cong ewf (cong ewf (suspSuppSrcPdb pdb))
suspSuppSrcPdb (Extend {submax = suc (suc submax)} pdb p q) = cong ewt (cong ewt (suspSuppSrcPdb pdb))
suspSuppSrcPdb (Restr pdb) = suspSuppSrcPdb pdb

suspSuppTgtPdb : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ _ : NonZero′ (submax + d) ⦄ → suspSupp (supp-pdb-tgt pdb) ≡ supp-pdb-tgt (susp-pdb pdb)
suspSuppTgtPdb (Extend {submax = zero} pdb p q) = cong (λ - → ewf (ewt (ewf -))) suspSuppFull
suspSuppTgtPdb (Extend {submax = suc zero} pdb p q) = cong ewf (cong ewt (trans (suspSuppDrop (supp-pdb-tgt pdb)) (cong drop (suspSuppTgtPdb pdb))))
suspSuppTgtPdb (Extend {submax = suc (suc submax)} pdb p q) = cong ewt (cong ewt (suspSuppTgtPdb pdb))
suspSuppTgtPdb (Restr pdb) = suspSuppTgtPdb pdb

suspSuppSrc : (pd : Γ ⊢pd₀ d) → .⦃ _ : NonZero′ d ⦄ → suspSupp (supp-src pd) ≡ supp-src (susp-pd pd)
suspSuppSrc {d = suc d} (Finish pdb) = suspSuppSrcPdb pdb

suspSuppTgt : (pd : Γ ⊢pd₀ d) → .⦃ _ : NonZero′ d ⦄ → suspSupp (supp-tgt pd) ≡ supp-tgt (susp-pd pd)
suspSuppTgt {d = suc d} (Finish pdb) = suspSuppTgtPdb pdb

-- suspCtxTy : Typing-Ctx Γ → Typing-Ctx (suspCtx Γ)
suspTyTy : Typing-Ty Γ A → Typing-Ty (suspCtx Γ) (suspTy A)
suspTmTy : Typing-Tm Γ t A → Typing-Tm (suspCtx Γ) (suspTm t) (suspTy A)
suspSubTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) (suspCtx Δ) (suspSub σ)
getFstTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getFst) ⋆
getSndTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getSnd) ⋆

-- suspCtxEq : Γ ≈c Δ → suspCtx Γ ≈c suspCtx Δ
suspTyEq : A ≈[ Γ ]ty B → suspTy A ≈[ suspCtx Γ ]ty suspTy B
suspTmEq : s ≈[ Γ ]tm t → suspTm s ≈[ suspCtx Γ ]tm suspTm t
suspSubEq : σ ≈[ Γ ]s τ → suspSub σ ≈[ suspCtx Γ ]s suspSub τ

-- suspCtxTy TyEmp = TyAdd (TyAdd TyEmp TyStar) TyStar
-- suspCtxTy (TyAdd ty x) = TyAdd (suspCtxTy ty) (suspTyTy x)

suspTyTy TyStar = TyArr getFstTy TyStar getSndTy
suspTyTy (TyArr p q r) = TyArr (suspTmTy p) (suspTyTy q) (suspTmTy r)

suspTmTy {Γ = Γ , A} (TyVarZ {Γ = .(Γ , A)} x) = TyVarZ (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift A))) (suspTyEq x))
suspTmTy (TyVarS i tvi x) = TyVarS (inject₁ (inject₁ i)) (suspTmTy tvi) (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift _))) (suspTyEq x))
suspTmTy (TyCoh {A = A} p q r s t) = TyCoh (susp-pd p) (suspTyTy q) (suspSubTy r) (lem) (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty _ _))) (suspTyEq t))
  where
    open ≡-Reasoning
    lem : FVTy (suspTy A) ≡ full
    lem = begin
      FVTy (suspTy A) ≡⟨ suspSuppTy A ⟩
      suspSupp (FVTy A) ≡⟨ cong suspSupp s ⟩
      suspSupp full ≡⟨ suspSuppFull ⟩
      full ∎

suspTmTy (TyComp {s = s} {A = A} {t = t} {σ = σ} pd p q r x y) = TyComp (susp-pd pd) (suspTyTy p) (suspSubTy q) lem1 lem2 (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty σ (s ─⟨ A ⟩⟶ t)))) (suspTyEq y))
  where
    open ≡-Reasoning
    lem1 : FVTy (suspTy A) ∪ FVTm (suspTm s) ≡ supp-src (susp-pd pd)
    lem1 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm s) ≡⟨ suspSuppTyTm A s ⟩
      suspSupp (FVTy A ∪ FVTm s) ≡⟨ cong suspSupp r ⟩
      suspSupp (supp-src pd) ≡⟨ suspSuppSrc pd ⟩
      supp-src (susp-pd pd) ∎

    lem2 : FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ supp-tgt (susp-pd pd)
    lem2 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ suspSuppTyTm A t ⟩
      suspSupp (FVTy A ∪ FVTm t) ≡⟨ cong suspSupp x ⟩
      suspSupp (supp-tgt pd) ≡⟨ suspSuppTgt pd ⟩
      supp-tgt (susp-pd pd) ∎

suspSubTy TyNull = TyExt (TyExt TyNull getFstTy) getSndTy
suspSubTy (TyExt p r) = TyExt (suspSubTy p) (term-conversion (suspTmTy r) (reflexive≈ty (susp-functorial-ty _ _)))

getFstTy {Γ = ∅} = TyVarS zero (TyVarZ Star≈) Star≈
getFstTy {Γ = Γ , A} = lift-tm-typing getFstTy

getSndTy {Γ = ∅} = TyVarZ Star≈
getSndTy {Γ = Γ , A} = lift-tm-typing getSndTy

-- suspCtxEq Emp≈ = refl≈c
-- suspCtxEq (Add≈ eq x) = Add≈ (suspCtxEq eq) (suspTyEq x)

suspTyEq Star≈ = refl≈ty

suspTyEq (Arr≈ q r s) = Arr≈ (suspTmEq q) (suspTyEq r) (suspTmEq s)

suspTmEq (Var≈ x) = Var≈ (begin
  toℕ (inject₁ (inject₁ _)) ≡⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ _) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ _ ≡⟨ x ⟩
  toℕ _ ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ _) ≡˘⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ (inject₁ _)) ∎)
  where
    open ≡-Reasoning
suspTmEq (Sym≈ eq) = Sym≈ (suspTmEq eq)
suspTmEq (Trans≈ eq eq′) = Trans≈ (suspTmEq eq) (suspTmEq eq′)
suspTmEq (Coh≈ q r) = Coh≈ (suspTyEq q) (suspSubEq r)
suspTmEq (Rule≈ i a eqt tc) = props i .susp-rule a (λ j → suspTmEq (eqt j)) (suspTmTy tc)

suspSubEq Null≈ = refl≈s
suspSubEq (Ext≈ p x) = Ext≈ (suspSubEq p) (suspTmEq x)
