{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Connection.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule props
open import Catt.Pasting.Typing index rule props
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Connection
open import Catt.Connection.Properties
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning

connect-Ty : {Γ : Ctx (suc n)} → Typing-Ctx Γ → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → {Δ : Ctx (suc m)} → Typing-Ctx Δ → Typing-Ctx (connect Γ t Δ)
connect-inc-right-Ty : {Γ : Ctx (suc n)} → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → (Δ : Ctx (suc m)) → Typing-Sub Δ (connect Γ t Δ) (connect-inc-right t m)

connect-Ty Γty tty (TyAdd TyEmp x) = Γty
connect-Ty Γty tty (TyAdd (TyAdd Δty y) x) = TyAdd (connect-Ty Γty tty (TyAdd Δty y)) (apply-sub-ty-typing x (connect-inc-right-Ty tty (_ , _)))

connect-inc-right-Ty tty (∅ , A) with ≃ty-preserve-height (⋆-is-only-ty-in-empty-context A)
... | refl with A
... | ⋆ = TyExt TyNull tty
connect-inc-right-Ty tty (Δ , A , B) = TyExt (lift-sub-typing (connect-inc-right-Ty tty (Δ , A))) (TyVarZ (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ _ (connect-inc-right _ _)))))

connect-inc-left-Ty : {Γ : Ctx (suc n)} → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → (Δ : Ctx (suc m)) → Typing-Sub Γ (connect Γ t Δ) (connect-inc-left t m)
connect-inc-left-Ty tty (∅ , A) = id-Ty
connect-inc-left-Ty tty (Δ , A , B) = lift-sub-typing (connect-inc-left-Ty tty (Δ , A))

connect-pdb-Ty : (pdb : Γ ⊢pd[ submax ][ 0 ]) → Typing-Ctx Δ → Typing-Ctx (connect-pdb pdb Δ)
connect-pdb-Ty pdb = connect-Ty (pdb-to-Ty pdb) (term-conversion (pdb-focus-tm-Ty pdb) (reflexive≈ty (sym≃ty ⋆-is-only-0-d-ty)))

connect-pdb-inc-left-Ty : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → Typing-Sub Γ (connect-pdb pdb Δ) (connect-pdb-inc-left pdb m)
connect-pdb-inc-left-Ty pdb = connect-inc-left-Ty (term-conversion (pdb-focus-tm-Ty pdb) (reflexive≈ty (sym≃ty ⋆-is-only-0-d-ty)))

connect-pdb-inc-right-Ty : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → Typing-Sub Δ (connect-pdb pdb Δ) (connect-pdb-inc-right pdb m)
connect-pdb-inc-right-Ty pdb = connect-inc-right-Ty (term-conversion (pdb-focus-tm-Ty pdb) (reflexive≈ty (sym≃ty ⋆-is-only-0-d-ty)))

connect-pd-Ty : (pd : Γ ⊢pd₀ d) → Typing-Ctx Δ → Typing-Ctx (connect-pd pd Δ)
connect-pd-Ty (Finish pdb) = connect-pdb-Ty pdb

connect-pd-inc-left-Ty : (pd : Γ ⊢pd₀ d) → (Δ : Ctx (suc m)) → Typing-Sub Γ (connect-pd pd Δ) (connect-pd-inc-left pd m)
connect-pd-inc-left-Ty (Finish pdb) = connect-pdb-inc-left-Ty pdb

connect-pd-inc-right-Ty : (pd : Γ ⊢pd₀ d) → (Δ : Ctx (suc m)) → Typing-Sub Δ (connect-pd pd Δ) (connect-pd-inc-right pd m)
connect-pd-inc-right-Ty (Finish pdb) = connect-pdb-inc-right-Ty pdb

sub-from-connect-inc-right-≈ : (σ : Sub (suc n) l) → (t : Tm (suc n)) → (τ : Sub (suc m) l) → {Γ : Ctx l} → (t [ σ ]tm ≈[ Γ ]tm Var (fromℕ _) [ τ ]tm) → sub-from-connect σ t τ ∘ connect-inc-right t m ≈[ Γ ]s τ
sub-from-connect-inc-right-≈ σ t ⟨ ⟨⟩ , s ⟩ p = Ext≈ Null≈ p
sub-from-connect-inc-right-≈ σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≈ (trans≈s (reflexive≈s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-right t _))) (sub-from-connect-inc-right-≈ σ t ⟨ τ , s ⟩ p)) refl≈tm

sub-from-connect-Ty : Typing-Sub Γ Υ σ → Typing-Sub Δ Υ τ → (t [ σ ]tm ≈[ Υ ]tm Var (fromℕ _) [ τ ]tm)→ Typing-Sub (connect Γ t Δ) Υ (sub-from-connect σ t τ)
sub-from-connect-Ty σty (TyExt TyNull x) p = σty
sub-from-connect-Ty {Υ = Υ} {σ = σ} {t = t} σty (TyExt {A = A} (TyExt {σ = τ} {t = s} τty y) x) p = TyExt (sub-from-connect-Ty σty (TyExt τty y) p) (term-conversion x lem)
  where
    open Reasoning (ty-setoid-≈ Υ)
    lem : (A [ ⟨ τ , s ⟩ ]ty) ≈[ Υ ]ty
            ((A [ connect-inc-right t _ ]ty) [
             sub-from-connect σ t ⟨ τ , s ⟩ ]ty)
    lem = begin
      < A [ ⟨ τ , s ⟩ ]ty >ty′ ≈˘⟨ apply-sub-eq-ty A (sub-from-connect-inc-right-≈ σ t ⟨ τ , s ⟩ p) ⟩
      < A [ sub-from-connect σ t ⟨ τ , s ⟩ ∘ connect-inc-right t _ ]ty >ty′
        ≈⟨ reflexive≈ty (assoc-ty _ _ _) ⟩
      < ((A [ connect-inc-right t _ ]ty) [ sub-from-connect σ t ⟨ τ , s ⟩
          ]ty) >ty′ ∎

sub-from-connect-pdb-Ty : (pdb : Γ ⊢pd[ submax ][ 0 ]) → Typing-Sub Γ Υ σ → Typing-Sub Δ Υ τ → (getFocusTerm pdb [ σ ]tm ≈[ Υ ]tm Var (fromℕ _) [ τ ]tm) → Typing-Sub (connect-pdb pdb Δ) Υ (sub-from-connect-pdb pdb σ τ)
sub-from-connect-pdb-Ty pdb = sub-from-connect-Ty

sub-from-connect-pd-Ty : (pd : Γ ⊢pd₀ d) → Typing-Sub Γ Υ σ → Typing-Sub Δ Υ τ → (pd-focus-tm pd [ σ ]tm ≈[ Υ ]tm Var (fromℕ _) [ τ ]tm) → Typing-Sub (connect-pd pd Δ) Υ (sub-from-connect-pd pd σ τ)
sub-from-connect-pd-Ty (Finish pdb) = sub-from-connect-pdb-Ty pdb

sub-between-connects-Ty : Typing-Sub Γ Δ σ
                        → Typing-Tm Γ t ⋆
                        → Typing-Sub Υ Θ τ
                        → Typing-Tm Δ s ⋆
                        → t [ σ ]tm ≈[ Δ ]tm s
                        → Var (fromℕ _) [ τ ]tm ≈[ Θ ]tm Var (fromℕ l′)
                        → Typing-Sub (connect Γ t Υ) (connect Δ s Θ) (sub-between-connects σ t τ s)
sub-between-connects-Ty {Δ = Δ} {σ = σ} {t = t} {Θ = Θ} {τ = τ} {s = s} σty tty τty sty p q
  = sub-from-connect-Ty (apply-sub-sub-typing σty (connect-inc-left-Ty sty Θ)) (apply-sub-sub-typing τty (connect-inc-right-Ty sty Θ)) (begin
  t [ connect-inc-left s _ ∘ σ ]tm
    ≈⟨ reflexive≈tm (assoc-tm (connect-inc-left s _) σ t) ⟩
  t [ σ ]tm [ connect-inc-left s _ ]tm
    ≈⟨ apply-sub-tm-eq (connect-inc-left-Ty sty Θ) p ⟩
  s [ connect-inc-left s _ ]tm
    ≈⟨ reflexive≈tm (connect-inc-fst-var s _) ⟩
  Var (fromℕ _) [ connect-inc-right s _ ]tm
    ≈˘⟨ apply-sub-tm-eq (connect-inc-right-Ty sty Θ) q ⟩
  Var (fromℕ _) [ τ ]tm [ connect-inc-right s _ ]tm
    ≈˘⟨ reflexive≈tm (assoc-tm (connect-inc-right s _) τ (Var (fromℕ _))) ⟩
  Var (fromℕ _) [ connect-inc-right s _ ∘ τ ]tm ∎)
  where
    open Reasoning (tm-setoid-≈ (connect Δ s Θ))

sub-between-connect-pdbs-Ty : (pdb1 : Γ ⊢pd[ submax ][ 0 ])
                            → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ])
                            → Typing-Sub Γ Δ σ
                            → Typing-Sub Υ Θ τ
                            → getFocusTerm pdb1 [ σ ]tm ≈[ Δ ]tm getFocusTerm pdb2
                            → Var (fromℕ _) [ τ ]tm ≈[ Θ ]tm Var (fromℕ _)
                            → Typing-Sub (connect-pdb pdb1 Υ) (connect-pdb pdb2 Θ) (sub-between-connect-pdbs pdb1 pdb2 σ τ)
sub-between-connect-pdbs-Ty pdb1 pdb2 σty τty = sub-between-connects-Ty σty (term-conversion (pdb-focus-tm-Ty pdb1) (reflexive≈ty (sym≃ty (⋆-is-only-0-d-ty)))) τty (term-conversion (pdb-focus-tm-Ty pdb2) (reflexive≈ty (sym≃ty (⋆-is-only-0-d-ty))))

sub-between-connect-pds-Ty : (pd1 : Γ ⊢pd₀ d)
                           → (pd2 : Δ ⊢pd₀ d′)
                           → Typing-Sub Γ Δ σ
                           → Typing-Sub Υ Θ τ
                           → pd-focus-tm pd1 [ σ ]tm ≈[ Δ ]tm pd-focus-tm pd2
                           → Var (fromℕ _) [ τ ]tm ≈[ Θ ]tm Var (fromℕ _)
                           → Typing-Sub (connect-pd pd1 Υ) (connect-pd pd2 Θ) (sub-between-connect-pds pd1 pd2 σ τ)
sub-between-connect-pds-Ty (Finish pdb1) (Finish pdb2) = sub-between-connect-pdbs-Ty pdb1 pdb2
