open import Catt.Typing.Rule

module Catt.Wedge.Typing (ops : Op)
                         (rules : RuleSet)
                         (tame : Tame ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Wedge
open import Catt.Wedge.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Suspension.Typing ops susp-op rules lift-cond susp-cond


wedge-Ty : {Γ : Ctx (suc n)} → Typing-Ctx Γ → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → {Δ : Ctx (suc m)} → Typing-Ctx Δ → Typing-Ctx (wedge Γ t Δ)
wedge-inc-right-Ty : {Γ : Ctx (suc n)} → {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → Typing-Sub Δ (wedge Γ t Δ) (wedge-inc-right t m)

wedge-Ty Γty tty (TyAdd TyEmp x) = Γty
wedge-Ty Γty tty (TyAdd (TyAdd Δty y) x) = TyAdd (wedge-Ty Γty tty (TyAdd Δty y)) (apply-sub-ty-typing x (wedge-inc-right-Ty tty))

wedge-inc-right-Ty {Δ = ∅ , ⋆} tty = TyExt (TyNull TyStar) tty
wedge-inc-right-Ty {Δ = ∅ , s ─⟨ _ ⟩⟶ _} tty = ⊥-elim (no-term-in-empty-context s)
wedge-inc-right-Ty {Δ = Δ , B , A} tty = TyExt (lift-sub-typing (wedge-inc-right-Ty tty)) (TyConv (TyVar zero) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ A (wedge-inc-right _ _)))))

wedge-inc-left-Ty : {t : Tm (suc n)} → Typing-Tm Γ t ⋆ → (Δ : Ctx (suc m)) → Typing-Sub Γ (wedge Γ t Δ) (wedge-inc-left t m)
wedge-inc-left-Ty tty (∅ , A) = id-Ty
wedge-inc-left-Ty tty (Δ , A , B) = lift-sub-typing (wedge-inc-left-Ty tty (Δ , A))

wedge-susp-Ty : Typing-Ctx Γ → Typing-Ctx Δ → Typing-Ctx (wedge-susp Γ Δ)
wedge-susp-Ty Γty Δty = wedge-Ty (susp-ctxTy Γty) get-sndTy Δty

wedge-susp-inc-left-Ty : (Δ : Ctx (suc m)) → Typing-Sub (susp-ctx Γ) (wedge-susp Γ Δ) (wedge-susp-inc-left n m)
wedge-susp-inc-left-Ty Δ = wedge-inc-left-Ty get-sndTy Δ

wedge-susp-inc-right-Ty : (Γ : Ctx (suc n)) → Typing-Sub Δ (wedge-susp Γ Δ) (wedge-susp-inc-right n m)
wedge-susp-inc-right-Ty Γ = wedge-inc-right-Ty get-sndTy

sub-from-wedge-inc-right-≈ : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → {Γ : Ctx l} → (t [ σ ]tm ≈[ Γ ]tm Var (fromℕ _) [ τ ]tm) → wedge-inc-right t m ● sub-from-wedge σ τ ≈[ Γ ]s τ
sub-from-wedge-inc-right-≈ σ t ⟨ ⟨ _ ⟩′ , s ⟩ p = Ext≈ (Null≈ refl≈ty) p
sub-from-wedge-inc-right-≈ σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≈ lem refl≈tm
  where
    open Reasoning (sub-setoid-≈ _)
    lem : lift-sub (wedge-inc-right t _) ● sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩ ≈[ _ ]s ⟨ τ , s ⟩
    lem = begin
      < lift-sub (wedge-inc-right t _) ● sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩ >s′
        ≈⟨ reflexive≈s (apply-sub-lifted-sub-≃ (wedge-inc-right t _) (sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩)) ⟩
      < wedge-inc-right t _ ● sub-from-wedge σ ⟨ τ , s ⟩ >s′
        ≈⟨ sub-from-wedge-inc-right-≈ σ t ⟨ τ , s ⟩ p ⟩
      < ⟨ τ , s ⟩ >s′ ∎

sub-from-wedge-Ty : Typing-Sub Γ Υ σ → Typing-Tm Γ t ⋆ → Typing-Sub Δ Υ τ → (t [ σ ]tm ≈[ Υ ]tm Var (fromℕ _) [ τ ]tm) → Typing-Sub (wedge Γ t Δ) Υ (sub-from-wedge σ τ)
sub-from-wedge-Ty σty tty (TyExt (TyNull y) x) p = σty
sub-from-wedge-Ty {Υ = Υ} {σ = σ} {t = t} σty tty (TyExt {A = A} (TyExt {σ = τ} {t = s} τty y) x) p = TyExt (sub-from-wedge-Ty σty tty (TyExt τty y) p) (TyConv x lem)
  where
    open Reasoning (ty-setoid-≈ Υ)
    lem : (A [ ⟨ τ , s ⟩ ]ty) ≈[ Υ ]ty
            ((A [ wedge-inc-right t _ ]ty) [
             sub-from-wedge σ ⟨ τ , s ⟩ ]ty)
    lem = begin
      A [ ⟨ τ , s ⟩ ]ty ≈˘⟨ apply-sub-eq-ty A (sub-from-wedge-inc-right-≈ σ t ⟨ τ , s ⟩ p) ⟩
      A [ wedge-inc-right t _ ● sub-from-wedge σ ⟨ τ , s ⟩ ]ty
        ≈⟨ reflexive≈ty (assoc-ty _ _ A) ⟩
      ((A [ wedge-inc-right t _ ]ty) [ sub-from-wedge σ ⟨ τ , s ⟩ ]ty) ∎

sub-between-wedges-Ty : Typing-Sub Γ Δ σ
                        → Typing-Tm Γ t ⋆
                        → Typing-Sub Υ Θ τ
                        → Typing-Tm Δ s ⋆
                        → t [ σ ]tm ≈[ Δ ]tm s
                        → Var (fromℕ _) [ τ ]tm ≈[ Θ ]tm Var (fromℕ l′)
                        → Typing-Sub (wedge Γ t Υ) (wedge Δ s Θ) (sub-between-wedges σ τ s)
sub-between-wedges-Ty {Δ = Δ} {σ = σ} {t = t} {Θ = Θ} {τ = τ} {s = s} σty tty τty sty p q
  = sub-from-wedge-Ty (apply-sub-sub-typing σty (wedge-inc-left-Ty sty Θ)) tty (apply-sub-sub-typing τty (wedge-inc-right-Ty sty)) (begin
  t [ σ ● wedge-inc-left s _ ]tm
    ≈⟨ reflexive≈tm (assoc-tm σ (wedge-inc-left s _) t) ⟩
  t [ σ ]tm [ wedge-inc-left s _ ]tm
    ≈⟨ apply-sub-tm-eq (wedge-inc-left-Ty sty Θ) p ⟩
  s [ wedge-inc-left s _ ]tm
    ≈⟨ reflexive≈tm (wedge-inc-fst-var s _) ⟩
  Var (fromℕ _) [ wedge-inc-right s _ ]tm
    ≈˘⟨ apply-sub-tm-eq (wedge-inc-right-Ty sty) q ⟩
  Var (fromℕ _) [ τ ]tm [ wedge-inc-right s _ ]tm
    ≈˘⟨ reflexive≈tm (assoc-tm τ (wedge-inc-right s _) (Var (fromℕ _))) ⟩
  Var (fromℕ _) [ τ ● wedge-inc-right s _ ]tm ∎)
  where
    open Reasoning (tm-setoid-≈ (wedge Δ s Θ))

sub-between-wedge-susps-Ty : Typing-Sub Γ Δ σ
                             → Typing-Sub Υ Θ τ
                             → Var (fromℕ _) [ τ ]tm ≈[ Θ ]tm Var (fromℕ _)
                             → Typing-Sub (wedge-susp Γ Υ) (wedge-susp Δ Θ) (sub-between-wedge-susps σ τ)
sub-between-wedge-susps-Ty {σ = σ} σty τty p = sub-between-wedges-Ty (susp-subTy σty) get-sndTy τty get-sndTy (reflexive≈tm (sym≃tm (susp-sub-preserve-get-snd σ))) p

between-wedge-from-wedge-≈ : (σ : Sub (suc n) (suc l) ⋆)
                           → (τ : Sub (suc m) (suc l′) ⋆)
                           → (s : Tm (suc l))
                           → (σ′ : Sub (suc l) o A)
                           → (τ′ : Sub (suc l′) o A)
                           → s [ σ′ ]tm ≈[ Γ ]tm Var (fromℕ _) [ τ′ ]tm
                           → sub-between-wedges σ τ s ● sub-from-wedge σ′ τ′
                             ≈[ Γ ]s
                             sub-from-wedge (σ ● σ′) (τ ● τ′)
between-wedge-from-wedge-≈ {Γ = Γ} σ ⟨ ⟨ _ ⟩′ , t ⟩ s σ′ τ′ p = reflexive≈s (begin
  < (σ ● wedge-inc-left s _) ● sub-from-wedge σ′ τ′ >s
    ≈˘⟨ ●-assoc σ (wedge-inc-left s _) (sub-from-wedge σ′ τ′) ⟩
  < σ ● wedge-inc-left s _ ● sub-from-wedge σ′ τ′ >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-wedge-inc-left σ′ s τ′) ⟩
  < σ ● σ′ >s ∎)
  where
    open Reasoning sub-setoid
between-wedge-from-wedge-≈ {Γ = Γ} σ ⟨ ⟨ τ , u ⟩ , t ⟩ s σ′ τ′ p = Ext≈ (between-wedge-from-wedge-≈ σ ⟨ τ , u ⟩ s σ′ τ′ p) tm-lem
  where
    tm-lem : t [ wedge-inc-right s _ ]tm [ sub-from-wedge σ′ τ′ ]tm
         ≈[ Γ ]tm t [ τ′ ]tm
    tm-lem = begin
      t [ wedge-inc-right s _ ]tm [ sub-from-wedge σ′ τ′ ]tm
        ≈˘⟨ reflexive≈tm (assoc-tm (wedge-inc-right s _) (sub-from-wedge σ′ τ′) t) ⟩
      t [ wedge-inc-right s _ ● sub-from-wedge σ′ τ′ ]tm
        ≈⟨ apply-sub-eq-tm t (sub-from-wedge-inc-right-≈ σ′ s τ′ p) ⟩
      t [ τ′ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

sub-from-wedge-≈ : σ ≈[ Γ ]s σ′ → τ ≈[ Γ ]s τ′ → sub-from-wedge σ τ ≈[ Γ ]s sub-from-wedge σ′ τ′
sub-from-wedge-≈ p (Ext≈ (Null≈ y) x) = p
sub-from-wedge-≈ p (Ext≈ (Ext≈ q y) x) = Ext≈ (sub-from-wedge-≈ p (Ext≈ q y)) x
