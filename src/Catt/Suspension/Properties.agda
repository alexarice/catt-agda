{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Pasting
open import Catt.Suspension
-- open import Catt.Globular
-- open import Catt.Globular.Properties
open import Data.Nat
open import Data.Fin using (Fin;zero;suc;inject₁;toℕ;fromℕ;lower₁)
open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁;toℕ-fromℕ;toℕ-lower₁;inject₁-lower₁)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Variables
open import Relation.Nullary
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)

susp-ctx-≃ : Γ ≃c Δ → suspCtx Γ ≃c suspCtx Δ
susp-ty-≃ : {A : Ty Γ d} {B : Ty Δ d′} → Γ ≃c Δ → A ≃ty B → suspTy A ≃ty suspTy B
susp-tm-≃ : {s : Tm Γ} {t : Tm Δ} → Γ ≃c Δ → s ≃tm t → suspTm s ≃tm suspTm t
susp-sub-≃ : {σ : Sub Γ Δ} → {τ : Sub Γ′ Δ′} → Δ ≃c Δ′ → σ ≃s τ → suspSub σ ≃s suspSub τ

susp-ctx-≃ Emp≃ = refl≃c
susp-ctx-≃ (Add≃ p q) = Add≃ (susp-ctx-≃ p) (susp-ty-≃ p q)

susp-ty-≃ p Star≃ with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = refl≃ty
susp-ty-≃ p (Arr≃ q r s) = Arr≃ (susp-tm-≃ p q) (susp-ty-≃ p r) (susp-tm-≃ p s)

susp-tm-≃ _ (Var≃ q) = Var≃ (trans (toℕ-inject₁ (inject₁ _)) (trans (toℕ-inject₁ _) (trans q (sym (trans (toℕ-inject₁ (inject₁ _)) (toℕ-inject₁ _))))))
susp-tm-≃ p (Coh≃ q r s) = Coh≃ (susp-ctx-≃ q) (susp-ty-≃ q r) (susp-sub-≃ p s)

susp-sub-≃ p Null≃ with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = refl≃s
susp-sub-≃ p (Ext≃ r s) = Ext≃ (susp-sub-≃ p r) (susp-tm-≃ p s)

getFst-is-Fst : getFst {Γ = Γ} ≃tm Var {Γ = suspCtx Γ} (fromℕ _)
getFst-is-Fst {Γ = ∅} = Var≃ refl
getFst-is-Fst {Γ = Γ , A} = lift-tm-≃ getFst-is-Fst

getSnd-is-Snd : getSnd {Γ = Γ} ≃tm Var {Γ = suspCtx Γ} (inject₁ (fromℕ _))
getSnd-is-Snd {Γ = ∅} = Var≃ refl
getSnd-is-Snd {Γ = Γ , A} = lift-tm-≃ getSnd-is-Snd

getFst-across-ctx : {Γ : Ctx n} → {Δ : Ctx m} → n ≡ m → getFst {Γ = Γ} ≃tm getFst {Γ = Δ}
getFst-across-ctx p = trans≃tm getFst-is-Fst (trans≃tm (Var≃ (cong (λ - → suc (toℕ (fromℕ -))) p)) (sym≃tm getFst-is-Fst))

getSnd-across-ctx : {Γ : Ctx n} → {Δ : Ctx m} → n ≡ m → getSnd {Γ = Γ} ≃tm getSnd {Γ = Δ}
getSnd-across-ctx p = trans≃tm getSnd-is-Snd (trans≃tm (Var≃ (cong (λ - → toℕ (inject₁ (fromℕ -))) p)) (sym≃tm getSnd-is-Snd))

getFst-Lem : suspCtx Γ ≃c suspCtx Δ → getFst {Γ = Γ} ≃tm getFst {Γ = Δ}
getFst-Lem p = getFst-across-ctx (cong (λ - → pred (pred -)) (≃c-preserve-length p))

getSnd-Lem : suspCtx Γ ≃c suspCtx Δ → getSnd {Γ = Γ} ≃tm getSnd {Γ = Δ}
getSnd-Lem p = getSnd-across-ctx (cong (λ - → pred (pred -)) (≃c-preserve-length p))

susp-fst-var : (σ : Sub Γ Δ) → Var (fromℕ _) [ suspSub σ ]tm ≃tm Var {Γ = suspCtx Δ} (fromℕ _)
susp-fst-var ⟨⟩ = getFst-is-Fst
susp-fst-var ⟨ σ , t ⟩ = susp-fst-var σ

susp-snd-var : (σ : Sub Γ Δ) → Var (inject₁ (fromℕ _)) [ suspSub σ ]tm ≃tm Var {Γ = suspCtx Δ} (inject₁ (fromℕ _))
susp-snd-var ⟨⟩ = getSnd-is-Snd
susp-snd-var ⟨ σ , t ⟩ = susp-snd-var σ

susp-sub-preserve-getFst : {Γ : Ctx n} → {Δ : Ctx m} → (σ : Sub Γ Δ) → getFst {Γ = Δ} ≃tm getFst [ suspSub σ ]tm
susp-sub-preserve-getFst ⟨⟩ = refl≃tm
susp-sub-preserve-getFst ⟨ σ , t ⟩ = trans≃tm (susp-sub-preserve-getFst σ) (sym≃tm (lift-sub-comp-lem-tm (suspSub σ) getFst))

susp-sub-preserve-getSnd : {Γ : Ctx n} → {Δ : Ctx m} → (σ : Sub Γ Δ) → getSnd {Γ = Δ} ≃tm getSnd [ suspSub σ ]tm
susp-sub-preserve-getSnd ⟨⟩ = refl≃tm
susp-sub-preserve-getSnd ⟨ σ , t ⟩ = trans≃tm (susp-sub-preserve-getSnd σ) (sym≃tm (lift-sub-comp-lem-tm (suspSub σ) getSnd))

susp-functorial : (σ : Sub Δ Υ) → (τ : Sub Γ Δ) → suspSub (σ ∘ τ) ≃s suspSub σ ∘ suspSub τ
susp-functorial-tm : (σ : Sub Δ Υ) → (t : Tm Δ) → suspTm (t [ σ ]tm) ≃tm suspTm t [ suspSub σ ]tm
susp-functorial-ty : (σ : Sub Δ Υ) → (A : Ty Δ d) → suspTy (A [ σ ]ty) ≃ty suspTy A [ suspSub σ ]ty

susp-functorial σ ⟨⟩ = Ext≃ (Ext≃ Null≃ (susp-sub-preserve-getFst σ)) (susp-sub-preserve-getSnd σ)
susp-functorial σ ⟨ τ , t ⟩ = Ext≃ (susp-functorial σ τ) (susp-functorial-tm σ t)

susp-functorial-tm σ (Var i) = lem σ i
  where
    lem : {Γ : Ctx n} → (σ : Sub Γ Δ) → (i : Fin (ctxLength Γ)) → suspTm (Var i [ σ ]tm) ≃tm (Var (inject₁ (inject₁ i)) [ suspSub σ ]tm)
    lem ⟨ σ , t ⟩ zero = refl≃tm
    lem ⟨ σ , t ⟩ (suc i) = lem σ i
susp-functorial-tm σ (Coh Δ A τ) = Coh≃ refl≃c refl≃ty (susp-functorial σ τ)

susp-functorial-ty σ ⋆ = Arr≃ (susp-sub-preserve-getFst σ) Star≃ (susp-sub-preserve-getSnd σ)
susp-functorial-ty σ (s ─⟨ A ⟩⟶ t) = Arr≃ (susp-functorial-tm σ s) (susp-functorial-ty σ A) (susp-functorial-tm σ t)

susp-functorial-id : (Γ : Ctx n) → suspSub (idSub Γ) ≃s idSub (suspCtx Γ)
susp-functorial-id ∅ = Ext≃ (Ext≃ Null≃ (Var≃ refl)) (Var≃ refl)
susp-functorial-id (Γ , A) = Ext≃ (trans≃s (susp-sub-lift (idSub Γ)) (lift-sub-≃ (susp-functorial-id Γ))) (Var≃ refl)

suspSub-preserve-star : {Γ : Ctx n} → (σ : Sub Γ Δ) → suspTy ⋆ [ suspSub σ ]ty ≃ty suspTy (⋆ {Γ = Δ})
suspSub-preserve-star ⟨⟩ = refl≃ty
suspSub-preserve-star ⟨ σ , t ⟩ = trans≃ty (lift-sub-comp-lem-ty (suspSub σ) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) (suspSub-preserve-star σ)

suspSub-preserve-focus-ty : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ])→ (σ : Sub Γ Δ) → getFocusType (susp-pdb pdb) [ suspSub σ ]ty ≃ty getFocusType (susp-pdb pdb2)
suspSub-preserve-focus-ty pdb pdb2 σ = begin
  < getFocusType (susp-pdb pdb) [ suspSub σ ]ty >ty ≈˘⟨ sub-action-≃-ty (susp-pdb-foc-ty pdb) refl≃s ⟩
  < suspTy (getFocusType pdb) [ suspSub σ ]ty >ty ≈˘⟨ sub-action-≃-ty (susp-ty-≃ refl≃c ⋆-is-only-0-d-ty) refl≃s ⟩
  < suspTy ⋆ [ suspSub σ ]ty >ty ≈⟨ suspSub-preserve-star σ ⟩
  < suspTy ⋆ >ty ≈⟨ susp-ty-≃ refl≃c ⋆-is-only-0-d-ty ⟩
  < suspTy (getFocusType pdb2) >ty ≈⟨ susp-pdb-foc-ty pdb2 ⟩
  < getFocusType (susp-pdb pdb2) >ty ∎
  where
    open Reasoning ty-setoid

suspSub-preserve-focus-tm : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ]) → (σ : Sub Γ Δ) → getFocusTerm (Restr (susp-pdb pdb)) [ suspSub σ ]tm ≃tm getFocusTerm (Restr (susp-pdb pdb2))
suspSub-preserve-focus-tm pdb pdb2 σ = begin
  < getFocusTerm (Restr (susp-pdb pdb)) [ suspSub σ ]tm >tm ≡⟨⟩
  < ty-tgt (getFocusType (susp-pdb pdb)) [ suspSub σ ]tm >tm ≈⟨ ty-tgt-subbed (getFocusType (susp-pdb pdb)) (suspSub σ) ⟩
  < ty-tgt (getFocusType (susp-pdb pdb) [ suspSub σ ]ty) >tm ≈⟨ ty-tgt-≃ (suspSub-preserve-focus-ty pdb pdb2 σ) ⟩
  < ty-tgt (getFocusType (susp-pdb pdb2)) >tm ≡⟨⟩
  < getFocusTerm (Restr (susp-pdb pdb2)) >tm ∎
  where
    open Reasoning tm-setoid

-- inject-susp-sub : (σ : Sub Γ Δ) → (i : Fin (ctxLength Γ)) → Var (inject₁ (inject₁ i)) [ suspSub σ ]tm ≃tm suspTm (Var i [ σ ]tm)
-- inject-susp-sub ⟨ σ , t ⟩ zero = refl≃tm
-- inject-susp-sub ⟨ σ , t ⟩ (suc i) = inject-susp-sub σ i

-- susp-var-split : VarSplit Γ σ τ → VarSplit (suspCtx Γ) (suspSub σ) (suspSub τ)
-- susp-var-split {Γ = Γ} {σ = σ} {τ = τ} vs i with suc (ctxLength Γ) ≟ toℕ i
-- ... | yes p = inj₁ (fromℕ _ ,, γ)
--   where
--     open Reasoning tm-setoid
--     γ : (Var (fromℕ (suc _)) [ suspSub σ ]tm) ≃tm Var i
--     γ = begin
--       < Var (fromℕ (suc _)) [ suspSub σ ]tm >tm ≈⟨ susp-fst-var σ ⟩
--       < Var (fromℕ (suc _)) >tm ≈⟨ Var≃ (trans (cong suc (toℕ-fromℕ _)) p) ⟩
--       < Var i >tm ∎
-- ... | no p with ctxLength Γ ≟ toℕ (lower₁ i p)
-- ... | yes q = inj₁ ((inject₁ (fromℕ _)) ,, γ)
--   where
--     open Reasoning tm-setoid
--     γ : Var (inject₁ (fromℕ _)) [ suspSub σ ]tm ≃tm Var i
--     γ = begin
--       < Var (inject₁ (fromℕ _)) [ suspSub σ ]tm >tm ≈⟨ susp-snd-var σ ⟩
--       < Var (inject₁ (fromℕ _)) >tm ≈⟨ Var≃ (trans (toℕ-inject₁ (fromℕ _)) (trans (toℕ-fromℕ _) (trans q (toℕ-lower₁ i p)))) ⟩
--       < Var i >tm ∎
-- ... | no q with vs (lower₁ (lower₁ i p) q)
-- ... | inj₁ (j ,, x) = inj₁ ((inject₁ (inject₁ j)) ,, γ)
--   where
--     open Reasoning tm-setoid
--     γ : (Var (inject₁ (inject₁ j)) [ suspSub σ ]tm) ≃tm Var i
--     γ = begin
--       < Var (inject₁ (inject₁ j)) [ suspSub σ ]tm >tm ≈⟨ inject-susp-sub σ j ⟩
--       < suspTm (Var j [ σ ]tm) >tm ≈⟨ susp-tm-≃ refl≃c x ⟩
--       < suspTm (Var (lower₁ (lower₁ i p) q)) >tm ≈⟨ lookupSusp-is-inject (lower₁ (lower₁ i p) q) ⟩
--       < Var (inject₁ (inject₁ (lower₁ (lower₁ i p) q))) >tm ≈⟨ Var≃ (cong toℕ (trans (cong inject₁ (inject₁-lower₁ (lower₁ i p) q)) (inject₁-lower₁ i p))) ⟩
--       < Var i >tm ∎
-- ... | inj₂ (j ,, x) = inj₂ ((inject₁ (inject₁ j)) ,, γ)
--   where
--     open Reasoning tm-setoid
--     γ : (Var (inject₁ (inject₁ j)) [ suspSub τ ]tm) ≃tm Var i
--     γ = begin
--       < Var (inject₁ (inject₁ j)) [ suspSub τ ]tm >tm ≈⟨ inject-susp-sub τ j ⟩
--       < suspTm (Var j [ τ ]tm) >tm ≈⟨ susp-tm-≃ refl≃c x ⟩
--       < suspTm (Var (lower₁ (lower₁ i p) q)) >tm ≈⟨ lookupSusp-is-inject (lower₁ (lower₁ i p) q) ⟩
--       < Var (inject₁ (inject₁ (lower₁ (lower₁ i p) q))) >tm ≈⟨ Var≃ (cong toℕ (trans (cong inject₁ (inject₁-lower₁ (lower₁ i p) q)) (inject₁-lower₁ i p))) ⟩
--       < Var i >tm ∎

-- susp-function : (f : (i : Fin (ctxLength Γ)) → Tm Δ (suc (lookupDim Γ i))) → (i : Fin (ctxLength (suspCtx Γ))) → Tm (suspCtx Δ) (suc (lookupDim (suspCtx Γ) i))
-- susp-function {Γ = ∅} f zero = getSnd
-- susp-function {Γ = ∅} f (suc zero) = getFst
-- susp-function {Γ = Γ , A} f zero = suspTm (f zero)
-- susp-function {Γ = Γ , A} f (suc i) = susp-function {Γ = Γ} (λ j → f (suc j)) i

-- susp-function-prop : (f : (i : Fin (ctxLength Γ)) → Tm Δ (suc (lookupDim Γ i))) → (i : Fin (ctxLength Γ)) → susp-function {Γ = Γ} f (inject₁ (inject₁ i)) ≃tm suspTm (f i)
-- susp-function-prop {Γ = Γ , A} f zero = refl≃tm
-- susp-function-prop {Γ = Γ , A} f (suc i) = susp-function-prop {Γ = Γ} (λ j → f (suc j)) i

-- sub-from-function-susp : {Γ : Ctx n} → (f : (i : Fin (ctxLength Γ)) → Tm Δ (suc (lookupDim Γ i)))
--                        → sub-from-function {Γ = suspCtx Γ} (susp-function {Γ = Γ} f) ≃s suspSub {Γ = Γ} (sub-from-function f)
-- sub-from-function-susp {Γ = ∅} f = refl≃s
-- sub-from-function-susp {Γ = Γ , A} f = Ext≃ (sub-from-function-susp (λ i → f (suc i))) refl≃tm

-- suspension-vars : (Γ : Ctx n) → (i : Fin (ctxLength (suspCtx Γ))) → ((i ≡ fromℕ _) ⊎ (i ≡ inject₁ (fromℕ _))) ⊎ Σ[ j ∈ Fin (ctxLength Γ) ] i ≡ inject₁ (inject₁ j)
-- suspension-vars ∅ zero = inj₁ (inj₂ refl)
-- suspension-vars ∅ (suc zero) = inj₁ (inj₁ refl)
-- suspension-vars (Γ , A) zero = inj₂ (zero ,, refl)
-- suspension-vars (Γ , A) (suc i) with suspension-vars Γ i
-- ... | inj₁ (inj₁ x) = inj₁ (inj₁ (cong suc x))
-- ... | inj₁ (inj₂ y) = inj₁ (inj₂ (cong suc y))
-- ... | inj₂ (j ,, p) = inj₂ ((suc j) ,, (cong suc p))
