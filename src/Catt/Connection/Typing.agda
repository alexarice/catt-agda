{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Connection.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Connection
open import Catt.Connection.Properties
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Data.Empty
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Suspension.Typing index rule lift-rule susp-rule

connect-Ty : {Γ : Ctx (suc n)} → Typing-Ctx Γ → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → {Δ : Ctx (suc m)} → Typing-Ctx Δ → Typing-Ctx (connect Γ t Δ)
connect-inc-right-Ty : {Γ : Ctx (suc n)} → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → Typing-Ctx Δ → Typing-Sub Δ (connect Γ t Δ) (connect-inc-right t m)

connect-Ty Γty tty (TyAdd TyEmp x) = Γty
connect-Ty Γty tty (TyAdd (TyAdd Δty y) x) = TyAdd (connect-Ty Γty tty (TyAdd Δty y)) (apply-sub-ty-typing x (connect-inc-right-Ty tty (TyAdd Δty y)))

connect-inc-right-Ty tty (TyAdd TyEmp TyStar) = TyExt (TyNull TyStar) TyStar tty
connect-inc-right-Ty tty (TyAdd TyEmp (TyArr {s = s} x x₁ x₂)) = ⊥-elim (no-term-in-empty-context s)
connect-inc-right-Ty tty (TyAdd (TyAdd Δty y) x) = TyExt (lift-sub-typing (connect-inc-right-Ty tty (TyAdd Δty y))) x (TyVarZ (apply-sub-ty-typing x (connect-inc-right-Ty tty (TyAdd Δty y))) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ _ (connect-inc-right _ _)))))

connect-inc-left-Ty : Typing-Ctx Γ → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → (Δ : Ctx (suc m)) → Typing-Sub Γ (connect Γ t Δ) (connect-inc-left t m)
connect-inc-left-Ty Γty tty (∅ , A) = id-Ty Γty
connect-inc-left-Ty Γty tty (Δ , A , B) = lift-sub-typing (connect-inc-left-Ty Γty tty (Δ , A))

connect-susp-Ty : Typing-Ctx Γ → Typing-Ctx Δ → Typing-Ctx (connect-susp Γ Δ)
connect-susp-Ty Γty Δty = connect-Ty (suspCtxTy Γty) getSndTy Δty

connect-susp-inc-left-Ty : Typing-Ctx Γ → (Δ : Ctx (suc m)) → Typing-Sub (suspCtx Γ) (connect-susp Γ Δ) (connect-susp-inc-left n m)
connect-susp-inc-left-Ty Γty Δ = connect-inc-left-Ty (suspCtxTy Γty) getSndTy Δ

connect-susp-inc-right-Ty : (Γ : Ctx (suc n)) → Typing-Ctx Δ → Typing-Sub Δ (connect-susp Γ Δ) (connect-susp-inc-right n m)
connect-susp-inc-right-Ty Γ Δty = connect-inc-right-Ty getSndTy Δty

sub-from-connect-inc-right-≈ : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → {Γ : Ctx l} → (t [ σ ]tm ≈[ Γ ]tm Var (fromℕ _) [ τ ]tm) → sub-from-connect σ τ ∘ connect-inc-right t m ≈[ Γ ]s τ
sub-from-connect-inc-right-≈ σ t ⟨ ⟨⟩ , s ⟩ p = Ext≈ (Null≈ refl≈ty) p
sub-from-connect-inc-right-≈ σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≈ (trans≈s (reflexive≈s (lift-sub-comp-lem-sub (sub-from-connect σ ⟨ τ , s ⟩) (connect-inc-right t _))) (sub-from-connect-inc-right-≈ σ t ⟨ τ , s ⟩ p)) refl≈tm

sub-from-connect-Ty : Typing-Sub Γ Υ σ → Typing-Tm Γ t ⋆ → Typing-Sub Δ Υ τ → (t [ σ ]tm ≈[ Υ ]tm Var (fromℕ _) [ τ ]tm) → Typing-Sub (connect Γ t Δ) Υ (sub-from-connect σ τ)
sub-from-connect-Ty σty tty (TyExt (TyNull y) v x) p = σty
sub-from-connect-Ty {Υ = Υ} {σ = σ} {t = t} σty tty (TyExt {A = A} (TyExt {σ = τ} {t = s} τty v y) w x) p = TyExt (sub-from-connect-Ty σty tty (TyExt τty v y) p) (apply-sub-ty-typing w (connect-inc-right-Ty tty (sub-to-ctx-Ty (TyExt τty v y)))) (term-conversion x lem)
  where
    open Reasoning (ty-setoid-≈ Υ)
    lem : (A [ ⟨ τ , s ⟩ ]ty) ≈[ Υ ]ty
            ((A [ connect-inc-right t _ ]ty) [
             sub-from-connect σ ⟨ τ , s ⟩ ]ty)
    lem = begin
      A [ ⟨ τ , s ⟩ ]ty ≈˘⟨ apply-sub-eq-ty A (sub-from-connect-inc-right-≈ σ t ⟨ τ , s ⟩ p) ⟩
      A [ sub-from-connect σ ⟨ τ , s ⟩ ∘ connect-inc-right t _ ]ty
        ≈⟨ reflexive≈ty (assoc-ty _ _ A) ⟩
      ((A [ connect-inc-right t _ ]ty) [ sub-from-connect σ ⟨ τ , s ⟩ ]ty) ∎

sub-between-connects-Ty : Typing-Sub Γ Δ σ
                        → Typing-Tm Γ t ⋆
                        → Typing-Sub Υ Θ τ
                        → Typing-Tm Δ s ⋆
                        → Typing-Ctx Δ
                        → Typing-Ctx Θ
                        → t [ σ ]tm ≈[ Δ ]tm s
                        → Var (fromℕ _) [ τ ]tm ≈[ Θ ]tm Var (fromℕ l′)
                        → Typing-Sub (connect Γ t Υ) (connect Δ s Θ) (sub-between-connects σ τ s)
sub-between-connects-Ty {Δ = Δ} {σ = σ} {t = t} {Θ = Θ} {τ = τ} {s = s} σty tty τty sty Δty Θty p q
  = sub-from-connect-Ty (apply-sub-sub-typing σty (connect-inc-left-Ty Δty sty Θ)) tty (apply-sub-sub-typing τty (connect-inc-right-Ty sty Θty)) (begin
  t [ connect-inc-left s _ ∘ σ ]tm
    ≈⟨ reflexive≈tm (assoc-tm (connect-inc-left s _) σ t) ⟩
  t [ σ ]tm [ connect-inc-left s _ ]tm
    ≈⟨ apply-sub-tm-eq (connect-inc-left-Ty Δty sty Θ) p ⟩
  s [ connect-inc-left s _ ]tm
    ≈⟨ reflexive≈tm (connect-inc-fst-var s _) ⟩
  Var (fromℕ _) [ connect-inc-right s _ ]tm
    ≈˘⟨ apply-sub-tm-eq (connect-inc-right-Ty sty Θty) q ⟩
  Var (fromℕ _) [ τ ]tm [ connect-inc-right s _ ]tm
    ≈˘⟨ reflexive≈tm (assoc-tm (connect-inc-right s _) τ (Var (fromℕ _))) ⟩
  Var (fromℕ _) [ connect-inc-right s _ ∘ τ ]tm ∎)
  where
    open Reasoning (tm-setoid-≈ (connect Δ s Θ))

sub-between-connect-susps-Ty : Typing-Sub Γ Δ σ
                             → Typing-Sub Υ Θ τ
                             → Typing-Ctx Δ
                             → Typing-Ctx Θ
                             → Var (fromℕ _) [ τ ]tm ≈[ Θ ]tm Var (fromℕ _)
                             → Typing-Sub (connect-susp Γ Υ) (connect-susp Δ Θ) (sub-between-connect-susps σ τ)
sub-between-connect-susps-Ty {σ = σ} σty τty Δty Θty p = sub-between-connects-Ty (suspSubTy σty) getSndTy τty getSndTy (suspCtxTy Δty) Θty (reflexive≈tm (sym≃tm (susp-sub-preserve-getSnd σ))) p

between-connect-from-connect-≈ : (σ : Sub (suc n) (suc l) ⋆)
                               → (τ : Sub (suc m) (suc l′) ⋆)
                               → (s : Tm (suc l))
                               → (σ′ : Sub (suc l) o A)
                               → (τ′ : Sub (suc l′) o A)
                               → s [ σ′ ]tm ≈[ Γ ]tm Var (fromℕ _) [ τ′ ]tm
                               → sub-from-connect σ′ τ′ ∘ sub-between-connects σ τ s ≈[ Γ ]s sub-from-connect (σ′ ∘ σ) (τ′ ∘ τ)
between-connect-from-connect-≈ {Γ = Γ} σ ⟨ ⟨⟩ , t ⟩ s σ′ τ′ p = reflexive≈s (begin
  < sub-from-connect σ′ τ′ ∘ (connect-inc-left s _ ∘ σ) >s
    ≈˘⟨ ∘-assoc (sub-from-connect σ′ τ′) (connect-inc-left s _) σ ⟩
  < sub-from-connect σ′ τ′ ∘ connect-inc-left s _ ∘ σ >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-connect-inc-left σ′ s τ′) ⟩
  < σ′ ∘ σ >s ∎)
  where
    open Reasoning sub-setoid
between-connect-from-connect-≈ {Γ = Γ} σ ⟨ ⟨ τ , u ⟩ , t ⟩ s σ′ τ′ p = Ext≈ (between-connect-from-connect-≈ σ ⟨ τ , u ⟩ s σ′ τ′ p) tm-lem
  where
    tm-lem : t [ connect-inc-right s _ ]tm [ sub-from-connect σ′ τ′ ]tm
         ≈[ Γ ]tm t [ τ′ ]tm
    tm-lem = begin
      t [ connect-inc-right s _ ]tm [ sub-from-connect σ′ τ′ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm (sub-from-connect σ′ τ′) (connect-inc-right s _) t) ⟩
      t [ sub-from-connect σ′ τ′ ∘ connect-inc-right s _ ]tm
        ≈⟨ apply-sub-eq-tm t (sub-from-connect-inc-right-≈ σ′ s τ′ p) ⟩
      t [ τ′ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

sub-from-connect-≈ : σ ≈[ Γ ]s σ′ → τ ≈[ Γ ]s τ′ → sub-from-connect σ τ ≈[ Γ ]s sub-from-connect σ′ τ′
sub-from-connect-≈ p (Ext≈ (Null≈ y) x) = p
sub-from-connect-≈ p (Ext≈ (Ext≈ q y) x) = Ext≈ (sub-from-connect-≈ p (Ext≈ q y)) x
