{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Pasting
open import Catt.Suspension
open import Catt.Globular
open import Catt.Globular.Properties
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
susp-ty-≃ : A ≃ty B → suspTy A ≃ty suspTy B
susp-tm-≃ : s ≃tm t → suspTm s ≃tm suspTm t
susp-sub-≃ : σ ≃s τ → suspSub σ ≃s suspSub τ

susp-ctx-≃ Emp≃ = refl≃c
susp-ctx-≃ (Add≃ p q) = Add≃ (susp-ctx-≃ p) (susp-ty-≃ q)

susp-ty-≃ (Star≃ x) with x
... | refl = refl≃ty
susp-ty-≃ (Arr≃ q r s) = Arr≃ (susp-tm-≃ q) (susp-ty-≃ r) (susp-tm-≃ s)

susp-tm-≃ (Var≃ p q) = Var≃ (cong suc (cong suc p)) (trans (toℕ-inject₁ (inject₁ _)) (trans (toℕ-inject₁ _) (trans q (sym (trans (toℕ-inject₁ (inject₁ _)) (toℕ-inject₁ _))))))
susp-tm-≃ (Coh≃ q r s) = Coh≃ (susp-ctx-≃ q) (susp-ty-≃ r) (susp-sub-≃ s)

susp-sub-≃ (Null≃ x) with x
... | refl = refl≃s
susp-sub-≃ (Ext≃ r s) = Ext≃ (susp-sub-≃ r) (susp-tm-≃ s)


getFst-Lem : suspCtx Γ ≃c suspCtx Δ → getFst {n = ctxLength Γ} ≃tm getFst {n = ctxLength Δ}
getFst-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → suc (toℕ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

getSnd-Lem : suspCtx Γ ≃c suspCtx Δ → getSnd {n = ctxLength Γ} ≃tm getSnd {n = ctxLength Δ}
getSnd-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → toℕ (inject₁ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

susp-fst-var : (σ : Sub n m) → Var (fromℕ _) [ suspSub σ ]tm ≃tm Var {2 + m} (fromℕ _)
susp-fst-var ⟨⟩ = refl≃tm
susp-fst-var ⟨ σ , t ⟩ = susp-fst-var σ

susp-snd-var : (σ : Sub n m) → Var (inject₁ (fromℕ _)) [ suspSub σ ]tm ≃tm Var {2 + m} (inject₁ (fromℕ _))
susp-snd-var ⟨⟩ = refl≃tm
susp-snd-var ⟨ σ , t ⟩ = susp-snd-var σ

susp-‼ : (Γ : Ctx n) → (i : Fin (ctxLength Γ)) → suspCtx Γ ‼ inject₁ (inject₁ i) ≃ty suspTy (Γ ‼ i)
susp-‼ (Γ , A) zero = sym≃ty (susp-ty-lift A)
susp-‼ (Γ , A) (suc i) = trans≃ty (lift-ty-≃ (susp-‼ Γ i)) (sym≃ty (susp-ty-lift (Γ ‼ i)))

susp-sub-preserve-getFst : (σ : Sub n m) → getFst {n = m} ≃tm getFst [ suspSub σ ]tm
susp-sub-preserve-getFst ⟨⟩ = refl≃tm
susp-sub-preserve-getFst ⟨ σ , t ⟩ = trans≃tm (susp-sub-preserve-getFst σ) (sym≃tm (lift-sub-comp-lem-tm {t = suspTm t} (suspSub σ) (getFst)))

susp-sub-preserve-getSnd : (σ : Sub n m) → getSnd {n = m} ≃tm getSnd [ suspSub σ ]tm
susp-sub-preserve-getSnd ⟨⟩ = refl≃tm
susp-sub-preserve-getSnd ⟨ σ , t ⟩ = trans≃tm (susp-sub-preserve-getSnd σ) (sym≃tm (lift-sub-comp-lem-tm {t = suspTm t} (suspSub σ) (getSnd)))


susp-functorial : (σ : Sub m l) → (τ : Sub n m) → suspSub (σ ∘ τ) ≃s suspSub σ ∘ suspSub τ
susp-functorial-tm : (σ : Sub m l) → (t : Tm m) → suspTm (t [ σ ]tm) ≃tm suspTm t [ suspSub σ ]tm
susp-functorial-ty : (σ : Sub m l) → (A : Ty m d) → suspTy (A [ σ ]ty) ≃ty suspTy A [ suspSub σ ]ty

susp-functorial σ ⟨⟩ = Ext≃ (Ext≃ (Null≃ refl) (susp-sub-preserve-getFst σ)) (susp-sub-preserve-getSnd σ)
susp-functorial σ ⟨ τ , t ⟩ = Ext≃ (susp-functorial σ τ) (susp-functorial-tm σ t)

susp-functorial-tm σ (Var i) = lem σ i
  where
    lem : (σ : Sub n m) → (i : Fin n) → suspTm (Var i [ σ ]tm) ≃tm (Var (inject₁ (inject₁ i)) [ suspSub σ ]tm)
    lem ⟨ σ , t ⟩ zero = refl≃tm
    lem ⟨ σ , t ⟩ (suc i) = lem σ i
susp-functorial-tm σ (Coh Δ A τ) = Coh≃ refl≃c refl≃ty (susp-functorial σ τ)

susp-functorial-ty σ ⋆ = Arr≃ (susp-sub-preserve-getFst σ) (Star≃ refl) (susp-sub-preserve-getSnd σ)
susp-functorial-ty σ (s ─⟨ A ⟩⟶ t) = Arr≃ (susp-functorial-tm σ s) (susp-functorial-ty σ A) (susp-functorial-tm σ t)

susp-functorial-id : (n : ℕ) → suspSub (idSub n) ≃s idSub (2 + n)
susp-functorial-id zero = refl≃s
susp-functorial-id (suc n) = Ext≃ (trans≃s (susp-sub-lift (idSub n)) (lift-sub-≃ (susp-functorial-id n))) refl≃tm


suspSub-preserve-star : (σ : Sub n m) → suspTy ⋆ [ suspSub σ ]ty ≃ty suspTy (⋆ {n = m})
suspSub-preserve-star ⟨⟩ = refl≃ty
suspSub-preserve-star ⟨ σ , t ⟩ = trans≃ty (lift-sub-comp-lem-ty {t = suspTm t} (suspSub σ) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) (suspSub-preserve-star σ)

suspSub-preserve-focus-ty : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ])→ (σ : Sub (ctxLength Γ) (ctxLength Δ)) → getFocusType (susp-pdb pdb) [ suspSub σ ]ty ≃ty getFocusType (susp-pdb pdb2)
suspSub-preserve-focus-ty pdb pdb2 σ = begin
  < getFocusType (susp-pdb pdb) [ suspSub σ ]ty >ty ≈˘⟨ sub-action-≃-ty (susp-pdb-foc-ty pdb) refl≃s ⟩
  < suspTy (getFocusType pdb) [ suspSub σ ]ty >ty ≈˘⟨ sub-action-≃-ty (susp-ty-≃ ⋆-is-only-0-d-ty) refl≃s ⟩
  < suspTy ⋆ [ suspSub σ ]ty >ty ≈⟨ suspSub-preserve-star σ ⟩
  < suspTy ⋆ >ty ≈⟨ susp-ty-≃ ⋆-is-only-0-d-ty ⟩
  < suspTy (getFocusType pdb2) >ty ≈⟨ susp-pdb-foc-ty pdb2 ⟩
  < getFocusType (susp-pdb pdb2) >ty ∎
  where
    open Reasoning ty-setoid

suspSub-preserve-focus-tm : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ]) → (σ : Sub (ctxLength Γ) (ctxLength Δ)) → getFocusTerm (Restr (susp-pdb pdb)) [ suspSub σ ]tm ≃tm getFocusTerm (Restr (susp-pdb pdb2))
suspSub-preserve-focus-tm pdb pdb2 σ = begin
  < getFocusTerm (Restr (susp-pdb pdb)) [ suspSub σ ]tm >tm ≡⟨⟩
  < ty-tgt (getFocusType (susp-pdb pdb)) [ suspSub σ ]tm >tm ≈⟨ ty-tgt-subbed (getFocusType (susp-pdb pdb)) (suspSub σ) ⟩
  < ty-tgt (getFocusType (susp-pdb pdb) [ suspSub σ ]ty) >tm ≈⟨ ty-tgt-≃ (suspSub-preserve-focus-ty pdb pdb2 σ) ⟩
  < ty-tgt (getFocusType (susp-pdb pdb2)) >tm ≡⟨⟩
  < getFocusTerm (Restr (susp-pdb pdb2)) >tm ∎
  where
    open Reasoning tm-setoid

lookupHeight-suspCtx : (Γ : Ctx n) → (i : Fin (ctxLength Γ)) → suc (lookupHeight Γ i) ≡ lookupHeight (suspCtx Γ) (inject₁ (inject₁ i))
lookupHeight-suspCtx (Γ , A) zero = refl
lookupHeight-suspCtx (Γ , A) (suc i) = lookupHeight-suspCtx Γ i

-- inject-susp-sub : (σ : Sub Γ Δ) → (i : Fin (ctxLength Γ)) → Var (inject₁ (inject₁ i)) [ suspSub σ ]tm ≃tm suspTm (Var i [ σ ]tm)
-- inject-susp-sub ⟨ σ , t ⟩ zero = refl≃tm
-- inject-susp-sub ⟨ σ , t ⟩ (suc i) = inject-susp-sub σ i

suspension-vars : (i : Fin (2 + n)) → ((i ≡ fromℕ _) ⊎ (i ≡ inject₁ (fromℕ _))) ⊎ Σ[ j ∈ Fin n ] i ≡ inject₁ (inject₁ j)
suspension-vars {n = zero} zero = inj₁ (inj₂ refl)
suspension-vars {n = zero} (suc zero) = inj₁ (inj₁ refl)
suspension-vars {n = suc n} zero = inj₂ (zero ,, refl)
suspension-vars {n = suc n} (suc i) with suspension-vars i
... | inj₁ (inj₁ x) = inj₁ (inj₁ (cong suc x))
... | inj₁ (inj₂ y) = inj₁ (inj₂ (cong suc y))
... | inj₂ (j ,, p) = inj₂ ((suc j) ,, (cong suc p))

susp-var-split : VarSplit n m l → VarSplit (2 + n) (2 + m) (2 + l)
susp-var-split vs i with suspension-vars i
... | inj₁ (inj₁ _) = inj₂ (fromℕ _)
... | inj₁ (inj₂ _) = inj₂ (inject₁ (fromℕ _))
... | inj₂ (j ,, _) with vs j
... | inj₁ j = inj₁ (inject₁ (inject₁ j))
... | inj₂ j = inj₂ (inject₁ (inject₁ j))

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
