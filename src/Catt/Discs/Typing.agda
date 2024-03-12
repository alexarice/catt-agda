open import Catt.Typing.Rule

module Catt.Discs.Typing (ops : Op)
                         (standard-op : StandardOp ops)
                         (rules : RuleSet)
                         (wk-cond : WkCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Globular
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Discs.Pasting
open import Catt.Discs.Support
open import Catt.Support
open import Catt.Support.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Weakening ops rules wk-cond
open import Catt.Globular.Typing ops rules

open import Catt.Discs.Typing.Base ops rules wk-cond

open import Catt.Typing.Weak ops

disc-term-Ty : (n : ℕ) → .⦃ NonZero n ⦄ → {σ : Sub (disc-size n) m ⋆} → Typing-Sub (Disc n) Γ σ → Typing-Tm Γ (disc-term n σ) (sphere-type n [ sub-proj₁ σ ]ty)
disc-term-Ty n@(suc n′) σty = let
  instance _ = disc-pd n
  in TyConv (TyCoh (subst₂ (ops (Disc n))
                           (sym (var2-disc-supp n′))
                           (sym (var1-disc-supp n′))
                           (standard-op (Disc n) n′ (≤-reflexive (disc-dim n))))
                   (wk-ty-typing (sphere-type-Ty n)) σty)
            (reflexive≈ty (apply-sub-wk-ty-≃ (sphere-type n) _))

sub-from-sphere-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Sub (Sphere d) Γ (sub-from-sphere d A p)
sub-from-sphere-Ty zero TyStar p = TyNull TyStar
sub-from-sphere-Ty (suc d) (TyArr {A = A} sty Aty tty) p
  = TyExt (TyExt (sub-from-sphere-Ty d Aty (cong pred p))
                 (TyConv sty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ (cong pred p))))))
          (TyConv tty (reflexive≈ty lem))
  where
    open Reasoning ty-setoid
    lem : A ≃ty
            (wk-ty (sphere-type d) [ ⟨ sub-from-sphere d A (cong pred p) , _ ⟩ ]ty)
    lem = begin
      < A >ty
        ≈˘⟨ sub-from-sphere-prop d A (cong pred p) ⟩
      < sphere-type d [ sub-from-sphere d A (cong pred p) ]ty >ty
        ≈˘⟨ apply-sub-wk-ty-≃ (sphere-type d) ⟨ sub-from-sphere d A _ , _ ⟩ ⟩
      < wk-ty (sphere-type d) [ ⟨ sub-from-sphere d A (cong pred p) , _ ⟩ ]ty >ty ∎

sub-from-disc-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Tm Γ t A → Typing-Sub (Disc d) Γ (sub-from-disc d A p t)
sub-from-disc-Ty {t = t} d Aty p tty
  = TyExt (sub-from-sphere-Ty d Aty p)
          (TyConv tty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ p))))

sub-from-sphere-≈ : (d : ℕ) → (q : A ≈[ Γ ]ty B) → .(p : ty-dim A ≡ d) → sub-from-sphere d A p ≈[ Γ ]s sub-from-sphere d B (trans (sym (ty-dim-≈ q)) p)
sub-from-sphere-≈ zero Star≈ q = Null≈ Star≈
sub-from-sphere-≈ (suc d) (Arr≈ x p y) q = Ext≈ (Ext≈ (sub-from-sphere-≈ d p (cong pred q)) x) y

sub-from-disc-≈ : (d : ℕ) → (q : A ≈[ Γ ]ty B) → .(p : ty-dim A ≡ d) → s ≈[ Γ ]tm t → sub-from-disc d A p s ≈[ Γ ]s sub-from-disc d B (trans (sym (ty-dim-≈ q)) p) t
sub-from-disc-≈ d q p r = Ext≈ (sub-from-sphere-≈ d q p) r

sub-from-sphere-Eq : (d : ℕ) → {σ : Sub (sphere-size d) n A} → {τ : Sub (sphere-size d) n A} → Typing-Sub (Sphere d) Γ σ → Typing-Sub (Sphere d) Γ τ → sphere-type d [ σ ]ty ≈[ Γ ]ty sphere-type d [ τ ]ty → σ ≈[ Γ ]s τ
sub-from-sphere-Eq zero (TyNull x) (TyNull x₁) p = Null≈ refl≈ty
sub-from-sphere-Eq {Γ = Γ} (suc d) (TyExt (TyExt {σ = σ} σty y) x) (TyExt (TyExt {σ = τ} τty y′) x′) (Arr≈ p q r) = Ext≈ (Ext≈ (sub-from-sphere-Eq d σty τty lem) p) r
  where
    lem : (sphere-type d [ σ ]ty) ≈[ Γ ]ty (sphere-type d [ τ ]ty)
    lem = begin
      sphere-type d [ σ ]ty
        ≈˘⟨ reflexive≈ty (apply-sub-wk-ty-≃ (sphere-type d) ⟨ σ , _ ⟩) ⟩
      wk-ty (sphere-type d) [ ⟨ σ , _ ⟩ ]ty
        ≈˘⟨ reflexive≈ty (apply-sub-wk-ty-≃ (wk-ty (sphere-type d)) ⟨ ⟨ σ , _ ⟩ , _ ⟩) ⟩
      wk-ty (wk-ty (sphere-type d)) [ ⟨ ⟨ σ , _ ⟩ , _ ⟩ ]ty
        ≈⟨ q ⟩
      wk-ty (wk-ty (sphere-type d)) [ ⟨ ⟨ τ , _ ⟩ , _ ⟩ ]ty
        ≈⟨ reflexive≈ty (apply-sub-wk-ty-≃ (wk-ty (sphere-type d)) ⟨ ⟨ τ , _ ⟩ , _ ⟩) ⟩
      wk-ty (sphere-type d) [ ⟨ τ , _ ⟩ ]ty
        ≈⟨ reflexive≈ty (apply-sub-wk-ty-≃ (sphere-type d) ⟨ τ , _ ⟩) ⟩
      sphere-type d [ τ ]ty ∎
      where
        open Reasoning (ty-setoid-≈ Γ)

sub-from-disc-Eq : (d : ℕ) → {σ : Sub (disc-size d) n A} → {τ : Sub (disc-size d) n A} → Typing-Sub (Disc d) Γ σ → Typing-Sub (Disc d) Γ τ → 0V [ σ ]tm ≃tm 0V [ τ ]tm → σ ≈[ Γ ]s τ
sub-from-disc-Eq d (TyExt σty x) (TyExt τty y) p = Ext≈ (sub-from-sphere-Eq d σty τty (Ty-unique-≃ p x y)) (reflexive≈tm p)

identity-Ty : (n : ℕ) → ∀ {σ} → Typing-Sub (Disc n) Γ σ → Typing-Tm Γ (identity n σ) ((0V ─⟨ wk-ty (sphere-type n) ⟩⟶ 0V) [ σ ]ty)
identity-Ty n σty = let
  instance _ = disc-pd n
  in TyCoh (subst₂ (ops (Disc n))
                   (trans (pd-bd-supp-full n (Disc n) false (≤-reflexive (disc-dim n))) (sym (var0-disc-full n)))
                   (trans (pd-bd-supp-full n (Disc n) true (≤-reflexive (disc-dim n))) (sym (var0-disc-full n)))
                   (standard-op (Disc n) n (≤-trans (≤-reflexive (disc-dim n)) (n≤1+n n))))
           (TyArr (TyVar zero) (wk-ty-typing (sphere-type-Ty n)) (TyVar zero))
           σty
  where
    open ≡-Reasoning

identity-term-Ty : Typing-Ty Γ A → Typing-Tm Γ t A → Typing-Tm Γ (identity-term A t) (t ─⟨ A ⟩⟶ t)
identity-term-Ty {A = A} Aty tty
  = TyConv (identity-Ty (ty-dim A) (sub-from-disc-Ty (ty-dim A) Aty refl tty)) (Arr≈ refl≈tm (reflexive≈ty lem) refl≈tm)
  where
    open Reasoning ty-setoid
    lem : wk-ty (sphere-type (ty-dim A)) [ sub-from-disc (ty-dim A) A _ _ ]ty ≃ty A
    lem = begin
      < wk-ty (sphere-type (ty-dim A)) [ sub-from-disc (ty-dim A) A _ _ ]ty >ty
        ≈⟨ apply-sub-wk-ty-≃ (sphere-type (ty-dim A)) (sub-from-disc (ty-dim A) A _ _) ⟩
      < sphere-type (ty-dim A) [ sub-from-sphere (ty-dim A) A _ ]ty >ty
        ≈⟨ sub-from-sphere-prop (ty-dim A) A refl ⟩
      < A >ty ∎

identity-term-≈ : A ≈[ Γ ]ty B → s ≈[ Γ ]tm t → identity-term A s ≈[ Γ ]tm identity-term B t
identity-term-≈ {A = A} {B = B} {s = s} {t = t} p q = begin
  identity-term A s
    ≈⟨ Coh≈ refl≈ty (sub-from-disc-≈ (ty-dim A) p refl q) ⟩
  identity (ty-dim A) (sub-from-disc (ty-dim A) B _ t)
    ≈⟨ reflexive≈tm (identity-≃ (ty-dim-≈ p) (sub-from-disc-≃ (ty-dim A) (ty-dim B) refl≃ty (sym (ty-dim-≈ p)) refl refl≃tm)) ⟩
  identity-term B t ∎
  where
    open Reasoning (tm-setoid-≈ _)

identity-to-term-Ty : Typing-Tm Γ (identity-term A t) B → Typing-Tm Γ t A
identity-to-term-Ty (TyConv tty p) = identity-to-term-Ty tty
identity-to-term-Ty {A = A} (TyCoh supp Aty (TyExt σty x))
  = TyConv x (reflexive≈ty (sub-from-sphere-prop (ty-dim A) A refl))

identity-to-type-Ty : Typing-Tm Γ (identity-term A t) B → Typing-Ty Γ A
identity-to-type-Ty (TyConv tty p) = identity-to-type-Ty tty
identity-to-type-Ty {A = A} (TyCoh supp Aty (TyExt σty _))
  = transport-typing-ty (apply-sub-weak-ty-typing (W.sphere-type-Ty (ty-dim A)) σty) refl≃c (sub-from-sphere-prop (ty-dim A) A refl)
  where
    import Catt.Discs.Typing.Base ops Weak-Rules weak-wk as W
