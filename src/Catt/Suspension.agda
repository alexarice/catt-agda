{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension where

open import Catt.Syntax
-- open import Catt.Syntax.Properties
-- open import Catt.Syntax.Patterns
-- open import Catt.Syntax.SyntacticEquality
-- open import Catt.Pasting
-- open import Catt.Pasting.Properties
open import Data.Nat
-- open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc;inject₁;toℕ)
-- open import Relation.Binary.PropositionalEquality
-- open import Catt.Dimension
-- open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁)

susp-tree : Tree n → Tree (suc (suc n))
susp-tree T = Join T Sing

suspCtx : Ctx n → Ctx (suc (suc n))
suspTy : Ty n → Ty (suc (suc n))
getFst : Tm (suc (suc n))
getSnd : Tm (suc (suc n))
suspTm : Tm n → Tm (suc (suc n))
suspSub : Sub n m → Sub (suc (suc n)) (suc (suc m))
lookupSusp : (i : Fin n) → Tm (suc (suc n))

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = getFst ─⟨ ⋆ ⟩⟶ getSnd
suspTy (s ─⟨ A ⟩⟶ t) = suspTm s ─⟨ suspTy A ⟩⟶ suspTm t

getFst {zero} = 1V
getFst {suc n} = liftTerm getFst

getSnd {zero} = 0V
getSnd {suc n} = liftTerm getSnd

suspTm (Var i) = lookupSusp i
suspTm (Coh T A σ) = Coh (susp-tree T) (suspTy A) (suspSub σ)

suspSub ⟨⟩ = ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩
suspSub ⟨ σ , t ⟩ = ⟨ suspSub σ , suspTm t ⟩

lookupSusp zero = 0V
lookupSusp (suc i) = liftTerm (lookupSusp i)

-- susp-src-compat : (A : Ty Γ (suc (suc d))) → suspTm (ty-src A) ≡ ty-src (suspTy A)
-- susp-src-compat (s ─⟨ A ⟩⟶ t) = refl

-- susp-tgt-compat : (A : Ty Γ (suc (suc d))) → suspTm (ty-tgt A) ≡ ty-tgt (suspTy A)
-- susp-tgt-compat (s ─⟨ A ⟩⟶ t) = refl

-- susp-base-compat : (A : Ty Γ (suc (suc d))) → suspTy (ty-base A) ≡ ty-base (suspTy A)
-- susp-base-compat (s ─⟨ A ⟩⟶ t) = refl

-- suspLiftTy : {A : Ty Γ d′} (B : Ty Γ d) → suspTy (liftType {A = A} B) ≡ liftType (suspTy B)
-- suspLiftTm : {A : Ty Γ d′} (t : Tm Γ d) → suspTm (liftTerm {A = A} t) ≡ liftTerm (suspTm t)
-- suspLiftSub : {A : Ty Δ d′} (σ : Sub Γ Δ) → suspSub (liftSub {A = A} σ) ≡ liftSub (suspSub σ)

-- suspLiftTy ⋆ = refl
-- suspLiftTy (s ─⟨ A ⟩⟶ t)
--   = arr-equality (suspLiftTm s)
--                  (suspLiftTy A)
--                  (suspLiftTm t)

-- suspLiftTm (Var i) = refl
-- suspLiftTm (Coh Δ A p σ) = coh-equality refl (suspLiftSub σ)

-- suspLiftSub ⟨⟩ = refl
-- suspLiftSub {A = A} ⟨ σ , t ⟩
--   = sub-equality (suspLiftSub σ)
--                  (suspLiftTm t)

-- susp-pdb : Γ ⊢pd[ submax ][ d ] → suspCtx Γ ⊢pd[ submax ][ suc d ]
-- susp-pdb-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTy (getFocusType pdb) ≡ getFocusType (susp-pdb pdb)
-- susp-pdb-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ]) → suspTm (getFocusTerm pdb) ≡ getFocusTerm (susp-pdb pdb)

-- susp-pdb Base = Extend Base
-- susp-pdb (Extend pdb)
--   = extend-pd-eq (susp-pdb pdb)
--                  (susp-pdb-foc-ty pdb)
--                  (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
--                                       (cong liftTerm (susp-pdb-foc-tm pdb)))
--                                (trans (suspLiftTy (getFocusType pdb))
--                                       (cong liftType (susp-pdb-foc-ty pdb)))
--                                refl)
-- susp-pdb (Restr pdb) = Restr (susp-pdb pdb)

-- susp-pdb-foc-tm Base = refl
-- susp-pdb-foc-tm (Extend pdb)
--   = extend-pd-eq-foc-tm (susp-pdb pdb)
--                         (susp-pdb-foc-ty pdb)
--                         (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
--                                              (cong liftTerm (susp-pdb-foc-tm pdb)))
--                                       (trans (suspLiftTy (getFocusType pdb))
--                                              (cong liftType (susp-pdb-foc-ty pdb)))
--                                       refl)
-- susp-pdb-foc-tm (Restr pdb)
--   = trans (susp-tgt-compat (getFocusType pdb))
--           (cong ty-tgt (susp-pdb-foc-ty pdb))

-- susp-pdb-foc-ty Base = refl
-- susp-pdb-foc-ty (Extend pdb)
--   = trans (arr-equality (trans (suspLiftTm (liftTerm (getFocusTerm pdb)))
--                                (cong liftTerm (trans (suspLiftTm (getFocusTerm pdb))
--                                                      (cong liftTerm (susp-pdb-foc-tm pdb)))))
--                         (trans (suspLiftTy (liftType (getFocusType pdb)))
--                                (cong liftType (trans (suspLiftTy (getFocusType pdb))
--                                                      (cong liftType (susp-pdb-foc-ty pdb)))))
--                         refl)
--           (extend-pd-eq-foc-ty (susp-pdb pdb)
--                                (susp-pdb-foc-ty pdb)
--                                (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
--                                                     (cong liftTerm (susp-pdb-foc-tm pdb)))
--                                              (trans (suspLiftTy (getFocusType pdb))
--                                                     (cong liftType (susp-pdb-foc-ty pdb)))
--                                              refl))
-- susp-pdb-foc-ty (Restr pdb)
--   = trans (susp-base-compat (getFocusType pdb))
--           (cong ty-base (susp-pdb-foc-ty pdb))

-- susp-pd : Γ ⊢pd₀ d → suspCtx Γ ⊢pd₀ suc d
-- susp-pd (Finish pdb) = Finish (Restr (susp-pdb pdb))

-- susp-ty-lift : (B : Ty Γ d) → suspTy (liftType {A = A} B) ≃ty liftType {A = suspTy A} (suspTy B)
-- susp-tm-lift : (t : Tm Γ d) → suspTm (liftTerm {A = A} t) ≃tm liftTerm {A = suspTy A} (suspTm t)
-- susp-sub-lift : (σ : Sub Δ Γ) → suspSub (liftSub {A = A} σ) ≃s liftSub {A = suspTy A} (suspSub σ)

-- susp-ty-lift ⋆ = Arr≃ refl≃tm Star≃ refl≃tm
-- susp-ty-lift (s ─⟨ B ⟩⟶ t) = Arr≃ (susp-tm-lift s) (susp-ty-lift B) (susp-tm-lift t)

-- susp-tm-lift (Var i) = refl≃tm
-- susp-tm-lift (Coh Δ A x σ) = Coh≃ refl≃c refl≃ty (susp-sub-lift σ)

-- susp-sub-lift ⟨⟩ = Ext≃ (Ext≃ Null≃ refl≃tm) refl≃tm
-- susp-sub-lift ⟨ σ , t ⟩ = Ext≃ (susp-sub-lift σ) (susp-tm-lift t)

-- lookupSusp-is-inject : (i : Fin (ctxLength Γ)) → lookupSusp {Γ = Γ} i ≃tm Var {Γ = suspCtx Γ} (inject₁ (inject₁ i))
-- lookupSusp-is-inject {Γ = Γ , A} zero = Var≃ refl
-- lookupSusp-is-inject {Γ = Γ , A} (suc i) = lift-tm-≃ (lookupSusp-is-inject i)

-- susp-ctx-≃ : Γ ≃c Δ → suspCtx Γ ≃c suspCtx Δ
-- susp-ty-≃ : {A : Ty Γ d} {B : Ty Δ d′} → Γ ≃c Δ → A ≃ty B → suspTy A ≃ty suspTy B
-- susp-tm-≃ : {s : Tm Γ d} {t : Tm Δ d′} → Γ ≃c Δ → s ≃tm t → suspTm s ≃tm suspTm t
-- susp-sub-≃ : {σ : Sub Γ Δ} {τ : Sub Γ′ Δ′} → Δ ≃c Δ′ → σ ≃s τ → suspSub σ ≃s suspSub τ

-- susp-ctx-≃ Emp≃ = refl≃c
-- susp-ctx-≃ (Add≃ p q) = Add≃ (susp-ctx-≃ p) (susp-ty-≃ p q)

-- susp-ty-≃ p Star≃ with ≃c-preserve-len p
-- ... | refl with ≃c-to-≡ p
-- ... | refl = refl≃ty
-- susp-ty-≃ p (Arr≃ q r s) = Arr≃ (susp-tm-≃ p q) (susp-ty-≃ p r) (susp-tm-≃ p s)

-- susp-tm-≃ _ (Var≃ q) = trans≃tm (lookupSusp-is-inject _) (trans≃tm (Var≃ (trans (toℕ-inject₁ (inject₁ _)) (trans (toℕ-inject₁ _) (trans q (sym (trans (toℕ-inject₁ (inject₁ _)) (toℕ-inject₁ _))))))) (sym≃tm (lookupSusp-is-inject _)))
-- susp-tm-≃ p (Coh≃ q r s) = Coh≃ (susp-ctx-≃ q) (susp-ty-≃ q r) (susp-sub-≃ p s)

-- susp-sub-≃ p Null≃ with ≃c-preserve-len p
-- ... | refl with ≃c-to-≡ p
-- ... | refl = refl≃s
-- susp-sub-≃ p (Ext≃ r s) = Ext≃ (susp-sub-≃ p r) (susp-tm-≃ p s)
