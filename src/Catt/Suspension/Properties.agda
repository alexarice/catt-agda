{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Suspension
open import Data.Nat
open import Data.Fin using (Fin;zero;suc;inject₁;toℕ;fromℕ;lower₁)
open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁;toℕ-fromℕ;toℕ-lower₁;inject₁-lower₁;inject₁-injective)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Variables
open import Catt.Variables.Properties
open import Relation.Nullary
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty

susp-tree-≃ : S ≃ T → suspTree S ≃ suspTree T
susp-ctx-≃ : Γ ≃c Δ → suspCtx Γ ≃c suspCtx Δ
susp-ty-≃ : A ≃ty B → suspTy A ≃ty suspTy B
susp-tm-≃ : s ≃tm t → suspTm s ≃tm suspTm t
susp-sub-≃ : σ ≃s τ → suspSub σ ≃s suspSub τ

susp-tree-≃ p = Join≃ p Sing≃

susp-ctx-≃ Emp≃ = refl≃c
susp-ctx-≃ (Add≃ p q) = Add≃ (susp-ctx-≃ p) (susp-ty-≃ q)

susp-ty-≃ (Star≃ x) with x
... | refl = refl≃ty
susp-ty-≃ (Arr≃ q r s) = Arr≃ (susp-tm-≃ q) (susp-ty-≃ r) (susp-tm-≃ s)

susp-tm-≃ (Var≃ p q) = Var≃ (cong suc (cong suc p)) (trans (toℕ-inject₁ (inject₁ _)) (trans (toℕ-inject₁ _) (trans q (sym (trans (toℕ-inject₁ (inject₁ _)) (toℕ-inject₁ _))))))
susp-tm-≃ (Coh≃ q r s) = Coh≃ (susp-tree-≃ q) (susp-ty-≃ r) (susp-sub-≃ s)

susp-sub-≃ (Null≃ x) with x
... | refl = refl≃s
susp-sub-≃ (Ext≃ r s) = Ext≃ (susp-sub-≃ r) (susp-tm-≃ s)

susp-ty-lift : (B : Ty n d) → suspTy (liftType B) ≃ty liftType (suspTy B)
susp-tm-lift : (t : Tm n) → suspTm (liftTerm t) ≃tm liftTerm (suspTm t)
susp-sub-lift : (σ : Sub n m) → suspSub (liftSub σ) ≃s liftSub (suspSub σ)

susp-ty-lift ⋆ = Arr≃ refl≃tm (Star≃ refl) refl≃tm
susp-ty-lift (s ─⟨ B ⟩⟶ t) = Arr≃ (susp-tm-lift s) (susp-ty-lift B) (susp-tm-lift t)

susp-tm-lift (Var i) = refl≃tm
susp-tm-lift (Coh Δ A σ) = Coh≃ refl≃ refl≃ty (susp-sub-lift σ)

susp-sub-lift ⟨⟩ = Ext≃ (Ext≃ (Null≃ refl) refl≃tm) refl≃tm
susp-sub-lift ⟨ σ , t ⟩ = Ext≃ (susp-sub-lift σ) (susp-tm-lift t)

susp-src-compat : (A : Ty n (suc d)) → suspTm (ty-src A) ≃tm ty-src (suspTy A)
susp-src-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

susp-tgt-compat : (A : Ty n (suc d)) → suspTm (ty-tgt A) ≃tm ty-tgt (suspTy A)
susp-tgt-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

susp-base-compat : (A : Ty n (suc d)) → suspTy (ty-base A) ≃ty ty-base (suspTy A)
susp-base-compat (s ─⟨ A ⟩⟶ t) = refl≃ty

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
susp-functorial-tm σ (Coh Δ A τ) = Coh≃ refl≃ refl≃ty (susp-functorial σ τ)

susp-functorial-ty σ ⋆ = Arr≃ (susp-sub-preserve-getFst σ) (Star≃ refl) (susp-sub-preserve-getSnd σ)
susp-functorial-ty σ (s ─⟨ A ⟩⟶ t) = Arr≃ (susp-functorial-tm σ s) (susp-functorial-ty σ A) (susp-functorial-tm σ t)

susp-functorial-id : (n : ℕ) → suspSub (idSub n) ≃s idSub (2 + n)
susp-functorial-id zero = refl≃s
susp-functorial-id (suc n) = Ext≃ (trans≃s (susp-sub-lift (idSub n)) (lift-sub-≃ (susp-functorial-id n))) refl≃tm

suspSub-preserve-star : (σ : Sub n m) → suspTy ⋆ [ suspSub σ ]ty ≃ty suspTy (⋆ {n = m})
suspSub-preserve-star ⟨⟩ = refl≃ty
suspSub-preserve-star ⟨ σ , t ⟩ = trans≃ty (lift-sub-comp-lem-ty {t = suspTm t} (suspSub σ) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) (suspSub-preserve-star σ)

lookupHeight-suspCtx : (Γ : Ctx n) → (i : Fin (ctxLength Γ)) → suc (lookupHeight Γ i) ≡ lookupHeight (suspCtx Γ) (inject₁ (inject₁ i))
lookupHeight-suspCtx (Γ , A) zero = refl
lookupHeight-suspCtx (Γ , A) (suc i) = lookupHeight-suspCtx Γ i

inject-susp-sub : (σ : Sub n m) → (i : Fin n) → Var (inject₁ (inject₁ i)) [ suspSub σ ]tm ≃tm suspTm (Var i [ σ ]tm)
inject-susp-sub ⟨ σ , t ⟩ zero = refl≃tm
inject-susp-sub ⟨ σ , t ⟩ (suc i) = inject-susp-sub σ i

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

    varToVarSuspSub-preserve-fst : (σ : Sub n m) → .⦃ _ : varToVar σ ⦄ → varToVarFunction (suspSub σ) ⦃ suspSub-var-to-var σ ⦄ (fromℕ _) ≡ fromℕ _
    varToVarSuspSub-preserve-fst ⟨⟩ = refl
    varToVarSuspSub-preserve-fst ⟨ σ , Var i ⟩ ⦃ v ⦄ = varToVarSuspSub-preserve-fst σ ⦃ proj₁ v ⦄

    varToVarSuspSub-preserve-snd : (σ : Sub n m) → .⦃ _ : varToVar σ ⦄ → varToVarFunction (suspSub σ) ⦃ suspSub-var-to-var σ ⦄ (inject₁ (fromℕ _)) ≡ inject₁ (fromℕ _)
    varToVarSuspSub-preserve-snd ⟨⟩ = refl
    varToVarSuspSub-preserve-snd ⟨ σ , Var i ⟩ ⦃ v ⦄ = varToVarSuspSub-preserve-snd σ ⦃ proj₁ v ⦄

    varToVarSuspSub-preserve-inject : (σ : Sub n m) → .⦃ _ : varToVar σ ⦄ → (k : Fin n) → varToVarFunction (suspSub σ) ⦃ suspSub-var-to-var σ ⦄ (inject₁ (inject₁ k)) ≡ inject₁ (inject₁ (varToVarFunction σ k))
    varToVarSuspSub-preserve-inject ⟨ σ , Var i ⟩ zero = refl
    varToVarSuspSub-preserve-inject ⟨ σ , Var i ⟩ ⦃ v ⦄ (suc k) = varToVarSuspSub-preserve-inject σ ⦃ proj₁ v ⦄ k

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

  susp-var-split-full : (τ : Sub l n) → .⦃ _ : varToVar τ ⦄ → (vs : VarSplit n m l) → VarSplitFull₂ τ vs → VarSplitFull₂ (suspSub τ) ⦃ suspSub-var-to-var τ ⦄ (susp-var-split vs)
  susp-var-split-full τ vs vsf i with suspension-vars i
  ... | inj₁ (inj₁ refl) = let
    instance _ = suspSub-var-to-var τ
    in begin
    susp-var-split vs (varToVarFunction (suspSub τ) (suc (fromℕ _)))
      ≡⟨ cong (susp-var-split vs) (varToVarSuspSub-preserve-fst τ) ⟩
    susp-var-split vs (fromℕ (suc _))
      ≡⟨ susp-var-split-fst vs ⟩
    inj₂ (fromℕ (suc _)) ∎
    where
      open ≡-Reasoning
  ... | inj₁ (inj₂ refl) = let
    instance _ = suspSub-var-to-var τ
    in begin
    susp-var-split vs (varToVarFunction (suspSub τ) (inject₁ (fromℕ _)))
      ≡⟨ cong (susp-var-split vs) (varToVarSuspSub-preserve-snd τ) ⟩
    susp-var-split vs (inject₁ (fromℕ _))
      ≡⟨ susp-var-split-snd vs ⟩
    inj₂ (inject₁ (fromℕ _)) ∎
    where
      open ≡-Reasoning
  ... | inj₂ (k ,, refl) = let
    instance - = suspSub-var-to-var τ
    in begin
      susp-var-split vs (varToVarFunction (suspSub τ) (inject₁ (inject₁ k)))
        ≡⟨ cong (susp-var-split vs) (varToVarSuspSub-preserve-inject τ k) ⟩
      susp-var-split vs (inject₁ (inject₁ (varToVarFunction τ k)))
        ≡⟨ susp-var-split-inject vs (varToVarFunction τ k) ⟩
      Data.Sum.map (λ - → inject₁ (inject₁ -))
        (λ - → inject₁ (inject₁ -)) (vs (varToVarFunction τ k))
        ≡⟨ cong (Data.Sum.map (λ - → inject₁ (inject₁ -))
        (λ - → inject₁ (inject₁ -))) (vsf k) ⟩
      inj₂ (inject₁ (inject₁ k)) ∎
    where
      open ≡-Reasoning
