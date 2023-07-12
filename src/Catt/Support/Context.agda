module Catt.Support.Context where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Variables
open import Catt.Variables.Properties

open import Catt.Support
open import Catt.Support.Properties

subctx-inc-ty : (A : Ty n) → (σ : Sub m n ⋆) → .⦃ varToVar σ ⦄ → .(FVTy A ⊆ FVSub σ) → Ty m
subctx-inc-tm : (t : Tm n) → (σ : Sub m n ⋆) → .⦃ varToVar σ ⦄ → .(FVTm t ⊆ FVSub σ) → Tm m
subctx-inc-sub : (τ : Sub l n ⋆) → (σ : Sub m n ⋆) → .⦃ varToVar σ ⦄ → .(FVSub τ ⊆ FVSub σ) → Sub l m ⋆

subctx-inc-ty ⋆ σ p = ⋆
subctx-inc-ty (s ─⟨ A ⟩⟶ t) σ p = (subctx-inc-tm s σ (⊆-trans (⊆-trans (∪-⊆-2 (FVTy A) (FVTm s)) (∪-⊆-1 (FVTy A ∪ FVTm s) (FVTm t))) p)) ─⟨ (subctx-inc-ty A σ (⊆-trans (⊆-trans (∪-⊆-1 (FVTy A) (FVTm s)) (∪-⊆-1 (FVTy A ∪ FVTm s) (FVTm t))) p)) ⟩⟶ (subctx-inc-tm t σ (⊆-trans (∪-⊆-2 (FVTy A ∪ FVTm s) (FVTm t)) p))

subctx-inc-tm (Var i) ⟨⟩ p = ⊥-elim (lem i p)
  where
    lem : (i : Fin n) → .(trueAt i ⊆ empty) → ⊥
    lem zero ()
    lem (suc i) p = lem i (debuild-⊆-2 p)
subctx-inc-tm (Var i) ⟨ σ , Var j ⟩ ⦃ q ⦄ p with i f≟ j
... | yes x = 0V
... | no x = lift-tm (subctx-inc-tm (Var i) σ ⦃ proj₁ q ⦄ (lem i j x (FVSub σ) p))
  where
    lem : (i j : Fin n) → ¬ i ≡ j → (xs : VarSet n) → trueAt i ⊆ xs ∪ trueAt j → trueAt i ⊆ xs
    lem zero zero p xs q = ⊥-elim (p refl)
    lem zero (suc j) p (ewt xs) q = cong ewt (⊆-bot xs)
    lem (suc i) zero p (x ∷ xs) q = build-⊆-1 x (⊆-trans (debuild-⊆-2 q) (⊆-reflexive (∪-right-unit xs)))
    lem (suc i) (suc j) p (x ∷ xs) q = build-⊆-1 x (lem i j (λ where refl → p refl) xs (debuild-⊆-2 q))

subctx-inc-tm (Coh S A τ) σ p = Coh S A (subctx-inc-sub τ σ p)

subctx-inc-sub ⟨⟩ σ p = ⟨⟩
subctx-inc-sub ⟨ τ , t ⟩ σ p = ⟨ (subctx-inc-sub τ σ (⊆-trans (∪-⊆-1 (FVSub τ) (FVTm t)) p)) , (subctx-inc-tm t σ (⊆-trans (∪-⊆-2 (FVSub τ) (FVTm t)) p)) ⟩

VarSet-size : VarSet n → ℕ
VarSet-size emp = 0
VarSet-size (ewf xs) = VarSet-size xs
VarSet-size (ewt xs) = suc (VarSet-size xs)

supp-ctx-inc : (xs : VarSet n) → Sub (VarSet-size xs) n ⋆
supp-ctx-inc emp = ⟨⟩
supp-ctx-inc (ewf xs) = lift-sub (supp-ctx-inc xs)
supp-ctx-inc (ewt xs) = ⟨ (lift-sub (supp-ctx-inc xs)) , 0V ⟩

supp-ctx-inc-v2v : (xs : VarSet n) → varToVar (supp-ctx-inc xs)
supp-ctx-inc-v2v emp = tt
supp-ctx-inc-v2v (ewf xs) = lift-sub-preserve-var-to-var (supp-ctx-inc xs) ⦃ supp-ctx-inc-v2v xs ⦄
supp-ctx-inc-v2v (ewt xs) = (lift-sub-preserve-var-to-var (supp-ctx-inc xs) ⦃ supp-ctx-inc-v2v xs ⦄) ,, tt

supp-ctx-inc-FV : (xs : VarSet n) → FVSub (supp-ctx-inc xs) ≡ xs
supp-ctx-inc-FV emp = refl
supp-ctx-inc-FV (ewf xs) = trans (supp-lift-sub (supp-ctx-inc xs)) (cong ewf (supp-ctx-inc-FV xs))
supp-ctx-inc-FV (ewt xs) = trans (cong (_∪ ewt empty) (supp-lift-sub (supp-ctx-inc xs))) (cong ewt (trans (∪-right-unit (FVSub (supp-ctx-inc xs))) (supp-ctx-inc-FV xs)))

supp-ctx : (Γ : Ctx n) → (xs : VarSet n) → .(is-DC Γ xs) → Ctx (VarSet-size xs)
supp-ctx ∅ emp dc = ∅
supp-ctx (Γ , A) (ewf xs) dc = supp-ctx Γ xs dc
supp-ctx (Γ , A) (ewt xs) dc = (supp-ctx Γ xs (proj₁ dc)) , subctx-inc-ty A (supp-ctx-inc xs) ⦃ supp-ctx-inc-v2v xs ⦄ (⊆-trans (proj₂ dc) (⊆-reflexive (sym (supp-ctx-inc-FV xs))))
