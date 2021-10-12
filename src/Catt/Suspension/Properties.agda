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
open import Data.Unit

-- susp-src-compat : (A : Ty n (suc d)) → suspTm (ty-src A) ≃tm ty-src (suspTy A)
-- susp-src-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

-- susp-tgt-compat : (A : Ty n (suc d)) → suspTm (ty-tgt A) ≃tm ty-tgt (suspTy A)
-- susp-tgt-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

-- susp-base-compat : (A : Ty n (suc d)) → suspTy (ty-base A) ≃ty ty-base (suspTy A)
-- susp-base-compat (s ─⟨ A ⟩⟶ t) = refl≃ty

getFst-Lem : suspCtx Γ ≃c suspCtx Δ → getFst {n = ctxLength Γ} ≃tm getFst {n = ctxLength Δ}
getFst-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → suc (toℕ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

getSnd-Lem : suspCtx Γ ≃c suspCtx Δ → getSnd {n = ctxLength Γ} ≃tm getSnd {n = ctxLength Δ}
getSnd-Lem p = Var≃ (≃c-preserve-length p) (cong (λ - → toℕ (inject₁ (fromℕ (pred (pred -))))) (≃c-preserve-length p))

susp-‼ : (Γ : Ctx n) → (i : Fin (ctxLength Γ)) → suspCtx Γ ‼ inject₁ (inject₁ i) ≃ty suspTy (Γ ‼ i)
susp-‼ (Γ , A) zero = sym≃ty (susp-ty-lift A)
susp-‼ (Γ , A) (suc i) = trans≃ty (lift-ty-≃ (susp-‼ Γ i)) (sym≃ty (susp-ty-lift (Γ ‼ i)))

susp-functorial-id : (n : ℕ) → suspSub (idSub n) ≃s idSub (2 + n)
susp-functorial-id zero = refl≃s
susp-functorial-id (suc n) = Ext≃ (trans≃s (susp-sub-lift (idSub n)) (lift-sub-≃ (susp-functorial-id n))) refl≃tm

suspSub-preserve-star : (σ : Sub n m ⋆) → suspTy ⋆ [ suspSub σ ]ty ≃ty suspTy (⋆ {n = m})
suspSub-preserve-star ⟨⟩ = refl≃ty
suspSub-preserve-star ⟨ σ , t ⟩ = trans≃ty (lift-sub-comp-lem-ty {t = suspTm t} (suspSub σ) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) (suspSub-preserve-star σ)

-- lookupHeight-suspCtx : (Γ : Ctx n) → (i : Fin (ctxLength Γ)) → suc (lookupHeight Γ i) ≡ lookupHeight (suspCtx Γ) (inject₁ (inject₁ i))
-- lookupHeight-suspCtx (Γ , A) zero = refl
-- lookupHeight-suspCtx (Γ , A) (suc i) = lookupHeight-suspCtx Γ i

inject-susp-sub : (σ : Sub n m ⋆) → (i : Fin n) → Var (inject₁ (inject₁ i)) [ suspSub σ ]tm ≃tm suspTm (Var i [ σ ]tm)
inject-susp-sub ⟨ σ , t ⟩ zero = refl≃tm
inject-susp-sub ⟨ σ , t ⟩ (suc i) = inject-susp-sub σ i

sub-res-unrestrict-comm : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → suspSubRes (unrestrict σ) ≃s unrestrict (suspSubRes σ)
sub-res-unrestrict-comm ⟨⟩ = refl≃s
sub-res-unrestrict-comm ⟨ σ , t ⟩ = Ext≃ (sub-res-unrestrict-comm σ) refl≃tm

susp-res-comp-ty : (B : Ty n) → (σ : Sub n m A) → suspTy (B [ σ ]ty) ≃ty B [ suspSubRes σ ]ty
susp-res-comp-tm : (t : Tm n) → (σ : Sub n m A) → suspTm (t [ σ ]tm) ≃tm t [ suspSubRes σ ]tm
susp-res-comp-sub : (σ : Sub n m A) → (τ : Sub l n B) → suspSubRes (σ ∘ τ) ≃s suspSubRes σ ∘ τ

susp-res-comp-ty ⋆ σ = refl≃ty
susp-res-comp-ty (s ─⟨ B ⟩⟶ t) σ = Arr≃ (susp-res-comp-tm s σ) (susp-res-comp-ty B σ) (susp-res-comp-tm t σ)

susp-res-comp-tm (Var zero) ⟨ σ , t ⟩ = refl≃tm
susp-res-comp-tm (Var (suc i)) ⟨ σ , t ⟩ = susp-res-comp-tm (Var i) σ
susp-res-comp-tm {A = ⋆} (Coh S B τ) σ = Coh≃ refl≃ refl≃ty (susp-functorial σ τ)
susp-res-comp-tm {A = s ─⟨ A ⟩⟶ t} (Coh S B τ) σ = trans≃tm (susp-res-comp-tm (Coh (suspTree S) (suspTy B) (suspSub τ)) (unrestrict σ)) (sub-action-≃-tm (refl≃tm {s = Coh (suspTree S) (suspTy B) (suspSub τ)}) (sub-res-unrestrict-comm σ))

susp-res-comp-sub σ ⟨⟩ = Null≃ (susp-res-comp-ty _ σ)
susp-res-comp-sub σ ⟨ τ , t ⟩ = Ext≃ (susp-res-comp-sub σ τ) (susp-res-comp-tm t σ)

susp-res-restrict : (σ : Sub (2 + n) m A) → (s t : Tm m) → suspSubRes (restrict σ s t) ≃s restrict (suspSubRes σ) (suspTm s) (suspTm t)
susp-res-restrict ⟨ ⟨ ⟨⟩ , _ ⟩ , _ ⟩ s t = refl≃s
susp-res-restrict ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ s t = Ext≃ (susp-res-restrict σ s t) refl≃tm

restrict-comp-sub : (τ : Sub n m A)
                  → (σ : Sub (2 + l) n B)
                  → (s t : Tm n)
                  → τ ∘ restrict σ s t ≃s restrict (τ ∘ σ) (s [ τ ]tm) (t [ τ ]tm)
restrict-comp-sub τ ⟨ ⟨ ⟨⟩ , _ ⟩ , _ ⟩ s t = refl≃s
restrict-comp-sub τ ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ s t = Ext≃ (restrict-comp-sub τ σ s t) refl≃tm

restrict-susp : (u : Tm n) → .⦃ isVar u ⦄ → (σ : Sub (2 + n) m A) → suspTm u [ σ ]tm ≃tm u [ restrict σ s t ]tm
restrict-susp (Var zero) ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = refl≃tm
restrict-susp (Var (suc i)) ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = restrict-susp (Var i) ⟨ ⟨ σ , u ⟩ , s ⟩

unrestrict-restrict-≃ : (σ : Sub (2 + n) m A)
                      → s ≃tm getFst [ σ ]tm
                      → t ≃tm getSnd [ σ ]tm
                      → unrestrict (restrict σ s t) ≃s σ
unrestrict-restrict-≃ ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ p q = Ext≃ (Ext≃ refl≃s p) q
unrestrict-restrict-≃ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ p q = Ext≃ (unrestrict-restrict-≃ ⟨ ⟨ σ , u ⟩ , s ⟩ p q) refl≃tm

restrict-susp-full : (u : Tm n)
                   → (σ : Sub (2 + n) m A)
                   → s ≃tm getFst [ σ ]tm
                   → t ≃tm getSnd [ σ ]tm
                   → suspTm u [ σ ]tm ≃tm u [ restrict σ s t ]tm
restrict-susp-full (Var i) σ p q = restrict-susp (Var i) σ
restrict-susp-full (Coh S A τ) σ p q = sub-action-≃-tm (refl≃tm {s = suspTm (Coh S A τ)}) (sym≃s (unrestrict-restrict-≃ σ p q))

getFst-unrestrict : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → getFst [ unrestrict σ ]tm ≃tm s
getFst-unrestrict ⟨⟩ = refl≃tm
getFst-unrestrict ⟨ σ , t ⟩ = getFst-unrestrict σ

getSnd-unrestrict : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → getSnd [ unrestrict σ ]tm ≃tm t
getSnd-unrestrict ⟨⟩ = refl≃tm
getSnd-unrestrict ⟨ σ , t ⟩ = getSnd-unrestrict σ

{-
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
-}

susp-tm-glob : (t : Tm n) → ⦃ isVar t ⦄ → isVar (suspTm t)
susp-tm-glob (Var i) = tt

susp-ty-glob : (A : Ty n) → ⦃ ty-is-globular A ⦄ → ty-is-globular (suspTy A)
susp-ty-glob ⋆ = tt ,, (tt ,, tt)
susp-ty-glob (s ─⟨ A ⟩⟶ t) ⦃ a ,, b ,, c ⦄ = susp-tm-glob s ⦃ a ⦄ ,, (susp-ty-glob A ⦃ b ⦄) ,, (susp-tm-glob t ⦃ c ⦄)

susp-ctx-glob : (Γ : Ctx n) → ⦃ ctx-is-globular Γ ⦄ → ctx-is-globular (suspCtx Γ)
susp-ctx-glob ∅ = (tt ,, tt) ,, tt
susp-ctx-glob (Γ , A) ⦃ a ,, b ⦄ = susp-ctx-glob Γ ⦃ a ⦄ ,, susp-ty-glob A ⦃ b ⦄
