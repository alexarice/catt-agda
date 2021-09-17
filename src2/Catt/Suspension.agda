{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension where

open import Catt.Syntax
-- open import Catt.Syntax.Properties
-- open import Catt.Syntax.Patterns
open import Catt.Syntax.SyntacticEquality
-- open import Catt.Pasting
-- open import Catt.Pasting.Properties
open import Data.Nat
-- open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc;inject₁;toℕ;fromℕ)
open import Relation.Binary.PropositionalEquality
-- open import Catt.Globular
-- open import Catt.Globular.Properties
open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁)

suspTree : Tree n → Tree (2 + n)
suspCtx : Ctx n → Ctx (2 + n)
suspTy : Ty n d → Ty (2 + n) (suc d)
getFst : Tm (2 + n)
getSnd : Tm (2 + n)
suspTm : Tm n → Tm (2 + n)
suspSub : Sub n m → Sub (2 + n) (2 + m)

suspTree T = Join T Sing

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = getFst ─⟨ ⋆ ⟩⟶ getSnd
suspTy (s ─⟨ A ⟩⟶ t) = suspTm s ─⟨ suspTy A ⟩⟶ suspTm t

getFst = Var (fromℕ _)

getSnd = Var (inject₁ (fromℕ _))

suspTm (Var i) = Var (inject₁ (inject₁ i))
suspTm (Coh T A σ) = Coh (suspTree T) (suspTy A) (suspSub σ)

suspSub ⟨⟩ = ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩
suspSub ⟨ σ , t ⟩ = ⟨ suspSub σ , suspTm t ⟩

{-
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

susp-ty-lift : (B : Ty n d) → suspTy (liftType B) ≃ty liftType (suspTy B)
susp-tm-lift : (t : Tm n) → suspTm (liftTerm t) ≃tm liftTerm (suspTm t)
susp-sub-lift : (σ : Sub n m) → suspSub (liftSub σ) ≃s liftSub (suspSub σ)

susp-ty-lift ⋆ = Arr≃ refl≃tm (Star≃ refl) refl≃tm
susp-ty-lift (s ─⟨ B ⟩⟶ t) = Arr≃ (susp-tm-lift s) (susp-ty-lift B) (susp-tm-lift t)

susp-tm-lift (Var i) = refl≃tm
susp-tm-lift (Coh Δ A σ) = Coh≃ refl≃c refl≃ty (susp-sub-lift σ)

susp-sub-lift ⟨⟩ = Ext≃ (Ext≃ (Null≃ refl) refl≃tm) refl≃tm
susp-sub-lift ⟨ σ , t ⟩ = Ext≃ (susp-sub-lift σ) (susp-tm-lift t)

susp-src-compat : (A : Ty n (suc d)) → suspTm (ty-src A) ≃tm ty-src (suspTy A)
susp-src-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

susp-tgt-compat : (A : Ty n (suc d)) → suspTm (ty-tgt A) ≃tm ty-tgt (suspTy A)
susp-tgt-compat (s ─⟨ A ⟩⟶ t) = refl≃tm

susp-base-compat : (A : Ty n (suc d)) → suspTy (ty-base A) ≃ty ty-base (suspTy A)
susp-base-compat (s ─⟨ A ⟩⟶ t) = refl≃ty

susp-pdb : Γ ⊢pd[ submax ][ d ] → suspCtx Γ ⊢pd[ submax ][ suc d ]
susp-pdb-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTy (getFocusType pdb) ≃ty getFocusType (susp-pdb pdb)
susp-pdb-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTm (getFocusTerm pdb) ≃tm getFocusTerm (susp-pdb pdb)

susp-pdb-≃-lem : (pdb : Γ ⊢pd[ submax ][ d ]) → (suspTm (liftTerm (getFocusTerm pdb)) ─⟨
                                                   suspTy (liftType (getFocusType pdb)) ⟩⟶ 0V)
                                                  ≃ty
                                                  (liftTerm (getFocusTerm (susp-pdb pdb)) ─⟨
                                                   liftType (getFocusType (susp-pdb pdb)) ⟩⟶ 0V)
susp-pdb-≃-lem pdb = Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm pdb)) (lift-tm-≃ (susp-pdb-foc-tm pdb)))
                          (trans≃ty (susp-ty-lift (getFocusType pdb)) (lift-ty-≃ (susp-pdb-foc-ty pdb)))
                          (Var≃ refl refl)

susp-pdb Base = Extend Base refl≃ty refl≃ty
susp-pdb (Extend pdb p q)
  = Extend (susp-pdb pdb)
           (trans≃ty (susp-ty-≃ p) (susp-pdb-foc-ty pdb))
           (trans≃ty (susp-ty-≃ q) (susp-pdb-≃-lem pdb))
susp-pdb (Restr pdb) = Restr (susp-pdb pdb)

susp-pdb-foc-tm Base = refl≃tm
susp-pdb-foc-tm (Extend pdb p q)
  = refl≃tm
susp-pdb-foc-tm (Restr pdb)
  = trans≃tm (susp-tgt-compat (getFocusType pdb)) (ty-tgt-≃ (susp-pdb-foc-ty pdb))

susp-pdb-foc-ty Base = refl≃ty
susp-pdb-foc-ty (Extend pdb p q)
  = susp-ty-lift _
susp-pdb-foc-ty (Restr pdb)
  = trans≃ty (susp-base-compat (getFocusType pdb)) (ty-base-≃ (susp-pdb-foc-ty pdb))

susp-pd : Γ ⊢pd₀ d → suspCtx Γ ⊢pd₀ suc d
susp-pd (Finish pdb) = Finish (Restr (susp-pdb pdb))
-}
