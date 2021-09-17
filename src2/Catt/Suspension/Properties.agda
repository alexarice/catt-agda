{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
open import Catt.Globular
open import Catt.Globular.Properties
open import Data.Nat
open import Data.Fin using (Fin;zero;suc;inject₁;toℕ;fromℕ;lower₁)
open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁;toℕ-fromℕ;toℕ-lower₁;inject₁-lower₁;inject₁-injective)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Variables
open import Relation.Nullary
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

getFst-Lem : suspCtx Γ ≃c suspCtx Δ → getFst {n = ctxLength Γ} ≃tm getFst {n = ctxLength Δ}
getFst-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → suc (toℕ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

getSnd-Lem : suspCtx Γ ≃c suspCtx Δ → getSnd {n = ctxLength Γ} ≃tm getSnd {n = ctxLength Δ}
getSnd-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → toℕ (inject₁ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

susp-‼ : (Γ : Ctx n) → (i : Fin (ctxLength Γ)) → suspCtx Γ ‼ inject₁ (inject₁ i) ≃ty suspTy (Γ ‼ i)
susp-‼ (Γ , A) zero = sym≃ty (susp-ty-lift A)
susp-‼ (Γ , A) (suc i) = trans≃ty (lift-ty-≃ (susp-‼ Γ i)) (sym≃ty (susp-ty-lift (Γ ‼ i)))

susp-sub-preserve-getFst : (σ : Sub n m) → getFst {n = m} ≃tm getFst [ suspSub σ ]tm
susp-sub-preserve-getFst ⟨⟩ = refl≃tm
susp-sub-preserve-getFst ⟨ σ , t ⟩ = susp-sub-preserve-getFst σ

susp-sub-preserve-getSnd : (σ : Sub n m) → getSnd {n = m} ≃tm getSnd [ suspSub σ ]tm
susp-sub-preserve-getSnd ⟨⟩ = refl≃tm
susp-sub-preserve-getSnd ⟨ σ , t ⟩ = susp-sub-preserve-getSnd σ

susp-pd-focus-tm-is-getSnd : (pd : Γ ⊢pd₀ d) → pd-focus-tm (susp-pd pd) ≃tm getSnd {n = ctxLength Γ}
susp-pd-focus-tm-is-getSnd (Finish pdb) = begin
  < ty-tgt (getFocusType (susp-pdb pdb)) >tm
    ≈˘⟨ ty-tgt-≃ (susp-pdb-foc-ty pdb) ⟩
  < ty-tgt (suspTy (getFocusType pdb)) >tm
    ≈˘⟨ ty-tgt-≃ (susp-ty-≃ (⋆-is-only-0-d-ty {A = getFocusType pdb})) ⟩
  < ty-tgt (suspTy ⋆) >tm
    ≡⟨⟩
  < getSnd >tm ∎
  where
    open Reasoning tm-setoid


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

suspSub-preserve-focus-tm : (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → (σ : Sub (ctxLength Γ) (ctxLength Δ)) → pd-focus-tm (susp-pd pd) [ suspSub σ ]tm ≃tm pd-focus-tm (susp-pd pd2)
suspSub-preserve-focus-tm (Finish pdb) (Finish pdb2) σ = begin
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

inject-susp-sub : (σ : Sub n m) → (i : Fin n) → Var (inject₁ (inject₁ i)) [ suspSub σ ]tm ≃tm suspTm (Var i [ σ ]tm)
inject-susp-sub ⟨ σ , t ⟩ zero = refl≃tm
inject-susp-sub ⟨ σ , t ⟩ (suc i) = inject-susp-sub σ i

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

susp-var-split-compat : {vs : VarSplit n m l} → VarSplitCompat σ τ vs → VarSplitCompat (suspSub σ) (suspSub τ) (susp-var-split vs)
susp-var-split-compat {σ = σ} {τ = τ} {vs = vs} vsc i with suspension-vars i
... | inj₁ (inj₁ refl) = sym≃tm (susp-sub-preserve-getFst τ)
... | inj₁ (inj₂ refl) = sym≃tm (susp-sub-preserve-getSnd τ)
... | inj₂ (j ,, refl) with vs j | vsc j
... | inj₁ k | p = trans≃tm (inject-susp-sub σ k) (susp-tm-≃ p)
... | inj₂ k | p = trans≃tm (inject-susp-sub τ k) (susp-tm-≃ p)

module _  where
  private
    minus1 : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
    minus1 zero = zero
    minus1 (suc i) = i

    lem : (n : ℕ) → (k : Fin n) → fromℕ n ≢ (inject₁ k)
    lem zero ()
    lem (suc n) (suc k) p = lem n k (cong minus1 p)

  susp-var-split-fst : (vs : VarSplit n m l) → susp-var-split vs (fromℕ _) ≡ inj₂ (fromℕ _)
  susp-var-split-fst {n = n} vs with suspension-vars (fromℕ (suc n))
  ... | inj₁ (inj₁ x) = refl
  ... | inj₁ (inj₂ y) = ⊥-elim (lem (suc n) (fromℕ n) y)
  ... | inj₂ (k ,, p) = ⊥-elim (lem (suc n) (inject₁ k) p)

  susp-var-split-snd : (vs : VarSplit n m l) → susp-var-split vs (inject₁ (fromℕ _)) ≡ inj₂ (inject₁ (fromℕ _))
  susp-var-split-snd {n = n} vs with suspension-vars (inject₁ (fromℕ n))
  ... | inj₁ (inj₁ x) = ⊥-elim (lem (suc n) (fromℕ n) (sym x))
  ... | inj₁ (inj₂ y) = refl
  ... | inj₂ (k ,, p) = ⊥-elim (lem n k (inject₁-injective p))

  susp-var-split-inject : (vs : VarSplit n m l) → (k : Fin n) → susp-var-split vs (inject₁ (inject₁ k)) ≡ Data.Sum.map (λ - → inject₁ (inject₁ -)) (λ - → inject₁ (inject₁ -)) (vs k)
  susp-var-split-inject vs k with suspension-vars (inject₁ (inject₁ k))
  ... | inj₁ (inj₁ x) = ⊥-elim (lem (suc _) (inject₁ k) (sym x))
  ... | inj₁ (inj₂ y) = ⊥-elim (lem _ k (sym (inject₁-injective y)))
  ... | inj₂ (j ,, p) with (inject₁-injective (inject₁-injective p))
  ... | refl with vs j
  ... | inj₁ x = refl
  ... | inj₂ y = refl

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

susp-pdb-bd : (pdb : Γ ⊢pd[ submax ][ d ])
            → .⦃ _ : NonZero′ (submax + d) ⦄
            → pdb-bd-ctx (susp-pdb pdb) ≃c (suspCtx (pdb-bd-ctx pdb))
susp-pdb-bd (Extend {submax = zero} pdb p q) = refl≃c
susp-pdb-bd (Extend {submax = suc zero} pdb p q) = susp-pdb-bd pdb
  where
    open Reasoning ctx-setoid
susp-pdb-bd (Extend {submax = suc (suc submax)} pdb p q) = trans≃c (extend-on-eq-ctx (pdb-bd-pd (susp-pdb pdb)) (susp-pdb (pdb-bd-pd pdb)) (susp-pdb-bd pdb)) (sym≃c (Add≃ (Add≃ refl≃c (susp-pdb-foc-ty (pdb-bd-pd pdb))) (susp-pdb-≃-lem (pdb-bd-pd pdb))))
  where
    open Reasoning ctx-setoid
susp-pdb-bd (Restr pdb) = susp-pdb-bd pdb

susp-pd-bd : (pd : Γ ⊢pd₀ suc d) → pd-bd-ctx (susp-pd pd) ≃c suspCtx (pd-bd-ctx pd)
susp-pd-bd (Finish pdb) = susp-pdb-bd pdb

susp-pdb-src : (pdb : Γ ⊢pd[ submax ][ d ])
             → .⦃ _ : NonZero′ (submax + d) ⦄
             → pdb-src (susp-pdb pdb) ≃s (suspSub (pdb-src pdb))
susp-pdb-src (Extend {submax = zero} pdb p q) = begin
  < pdb-src (susp-pdb (Extend pdb p q)) >s ≡⟨⟩
  < liftSub (liftSub (idSub _)) >s
    ≈˘⟨ lift-sub-≃ (lift-sub-≃ (susp-functorial-id (suc _))) ⟩
  < liftSub (liftSub (suspSub (idSub (suc _)))) >s
    ≈˘⟨ lift-sub-≃ (susp-sub-lift (idSub _)) ⟩
  < liftSub (suspSub (liftSub (idSub _))) >s
    ≈˘⟨ susp-sub-lift (liftSub (idSub _)) ⟩
  < suspSub (liftSub (liftSub (idSub _))) >s ≡⟨⟩
  < suspSub (pdb-src (Extend pdb p q)) >s ∎
  where
    open Reasoning sub-setoid
susp-pdb-src (Extend {submax = suc zero} pdb p q) = begin
  < liftSub (liftSub (pdb-src (susp-pdb pdb))) >s
    ≈⟨ lift-sub-≃ (lift-sub-≃ (susp-pdb-src pdb)) ⟩
  < liftSub (liftSub (suspSub (pdb-src pdb))) >s
    ≈˘⟨ lift-sub-≃ (susp-sub-lift (pdb-src pdb)) ⟩
  < liftSub (suspSub (liftSub (pdb-src pdb))) >s
    ≈˘⟨ susp-sub-lift (liftSub (pdb-src pdb)) ⟩
  < suspSub (liftSub (liftSub (pdb-src pdb))) >s ∎
  where
    open Reasoning sub-setoid
susp-pdb-src (Extend {submax = suc (suc submax)} pdb p q) = Ext≃ (Ext≃ lem refl≃tm) refl≃tm
  where
    open Reasoning sub-setoid
    lem : liftSub (liftSub (pdb-src (susp-pdb pdb))) ≃s
          suspSub (liftSub (liftSub (pdb-src pdb)))
    lem = begin
      < liftSub (liftSub (pdb-src (susp-pdb pdb))) >s
        ≈⟨ lift-sub-≃ (lift-sub-≃ (susp-pdb-src pdb)) ⟩
      < liftSub (liftSub (suspSub (pdb-src pdb))) >s
        ≈˘⟨ lift-sub-≃ (susp-sub-lift (pdb-src pdb)) ⟩
      < liftSub (suspSub (liftSub (pdb-src pdb))) >s
        ≈˘⟨ susp-sub-lift (liftSub (pdb-src pdb)) ⟩
      < suspSub (liftSub (liftSub (pdb-src pdb))) >s ∎
susp-pdb-src (Restr pdb) = susp-pdb-src pdb

susp-pd-src : (pd : Γ ⊢pd₀ suc d) → pd-src (susp-pd pd) ≃s suspSub (pd-src pd)
susp-pd-src (Finish pdb) = susp-pdb-src pdb


susp-replacePdSub : (σ : Sub (suc m) n) → (t : Tm n) → suspSub (replacePdSub σ t) ≃s replacePdSub (suspSub σ) (suspTm t)
susp-replacePdSub ⟨ σ , x ⟩ t = refl≃s

susp-pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ])
             → .⦃ _ : NonZero′ (submax + d) ⦄
             → pdb-tgt (susp-pdb pdb) ≃s (suspSub (pdb-tgt pdb))
susp-pdb-tgt (Extend {submax = zero} pdb p q) = Ext≃ lem refl≃tm
  where
    open Reasoning sub-setoid
    lem : liftSub (liftSub (liftSub (idSub _))) ≃s
          suspSub (liftSub (liftSub (liftSub (idSub _))))
    lem = begin
      < liftSub (liftSub (liftSub (idSub (suc (suc _))))) >s
        ≈˘⟨ lift-sub-≃ (lift-sub-≃ (lift-sub-≃ (susp-functorial-id _))) ⟩
      < liftSub (liftSub (liftSub (suspSub (idSub _)))) >s
        ≈˘⟨ lift-sub-≃ (lift-sub-≃ (susp-sub-lift (idSub _))) ⟩
      < liftSub (liftSub (suspSub (liftSub (idSub _)))) >s
        ≈˘⟨ lift-sub-≃ (susp-sub-lift (liftSub (idSub _))) ⟩
      < liftSub (suspSub (liftSub (liftSub (idSub _)))) >s
        ≈˘⟨ susp-sub-lift (liftSub (liftSub (idSub _))) ⟩
      < suspSub (liftSub (liftSub (liftSub (idSub _)))) >s ∎
susp-pdb-tgt (Extend {submax = suc zero} pdb p q) = begin
  < replacePdSub (liftSub (liftSub (pdb-tgt (susp-pdb pdb)))) 1V >s
    ≈⟨ replacePdSub-≃ lem refl≃tm ⟩
  < replacePdSub (suspSub (liftSub (liftSub (pdb-tgt pdb)))) 1V >s
    ≈˘⟨ susp-replacePdSub (liftSub (liftSub (pdb-tgt pdb))) 1V ⟩
  < suspSub (replacePdSub (liftSub (liftSub (pdb-tgt pdb))) 1V) >s ∎
  where
    open Reasoning sub-setoid
    lem : liftSub (liftSub (pdb-tgt (susp-pdb pdb))) ≃s
          suspSub (liftSub (liftSub (pdb-tgt pdb)))
    lem = begin
      < liftSub (liftSub (pdb-tgt (susp-pdb pdb))) >s
        ≈⟨ lift-sub-≃ (lift-sub-≃ (susp-pdb-tgt pdb)) ⟩
      < liftSub (liftSub (suspSub (pdb-tgt pdb))) >s
        ≈˘⟨ lift-sub-≃ (susp-sub-lift (pdb-tgt pdb)) ⟩
      < liftSub (suspSub (liftSub (pdb-tgt pdb))) >s
        ≈˘⟨ susp-sub-lift (liftSub (pdb-tgt pdb)) ⟩
      < suspSub (liftSub (liftSub (pdb-tgt pdb))) >s ∎
susp-pdb-tgt (Extend {submax = suc (suc submax)} pdb p q) = Ext≃ (Ext≃ lem refl≃tm) refl≃tm
  where
    open Reasoning sub-setoid
    lem : liftSub (liftSub (pdb-tgt (susp-pdb pdb))) ≃s
          suspSub (liftSub (liftSub (pdb-tgt pdb)))
    lem = begin
      < liftSub (liftSub (pdb-tgt (susp-pdb pdb))) >s
        ≈⟨ lift-sub-≃ (lift-sub-≃ (susp-pdb-tgt pdb)) ⟩
      < liftSub (liftSub (suspSub (pdb-tgt pdb))) >s
        ≈˘⟨ lift-sub-≃ (susp-sub-lift (pdb-tgt pdb)) ⟩
      < liftSub (suspSub (liftSub (pdb-tgt pdb))) >s
        ≈˘⟨ susp-sub-lift (liftSub (pdb-tgt pdb)) ⟩
      < suspSub (liftSub (liftSub (pdb-tgt pdb))) >s ∎
susp-pdb-tgt (Restr pdb) = susp-pdb-tgt pdb

susp-pd-tgt : (pd : Γ ⊢pd₀ suc d) → pd-tgt (susp-pd pd) ≃s suspSub (pd-tgt pd)
susp-pd-tgt (Finish pdb) = susp-pdb-tgt pdb
