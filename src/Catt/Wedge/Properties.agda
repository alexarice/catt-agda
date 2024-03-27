module Catt.Wedge.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Wedge

wedge-≃ : Γ ≃c Γ′ → t ≃tm t′ → Δ ≃c Δ′ → wedge Γ t Δ ≃c wedge Γ′ t′ Δ′
wedge-inc-right-≃ : {t : Tm (suc n)} → {t′ : Tm (suc n′)} → n ≡ n′ → t ≃tm t′ → m ≡ m′ → wedge-inc-right t m ≃s wedge-inc-right t′ m′

wedge-≃ p q (Add≃ Emp≃ r) = p
wedge-≃ p q (Add≃ (Add≃ r s) t) = Add≃ (wedge-≃ p q (Add≃ r s)) (sub-action-≃-ty t (wedge-inc-right-≃ (cong pred (≃c-preserve-length p)) q (cong pred (≃c-preserve-length (Add≃ r s)))))

wedge-inc-right-≃ {m = zero} refl q refl = Ext≃ refl≃s q
wedge-inc-right-≃ {m = suc m} refl q refl = Ext≃ (wk-sub-≃ (wedge-inc-right-≃ refl q refl)) (Var≃ refl refl)

wedge-inc-left-≃ : {t : Tm (suc n)} → {t′ : Tm (suc n′)} → n ≡ n′ → m ≡ m′ → wedge-inc-left t m ≃s wedge-inc-left t′ m′
wedge-inc-left-≃ {m = zero} refl refl = refl≃s
wedge-inc-left-≃ {m = suc m} {t = t} {t′} refl refl = wk-sub-≃ (wedge-inc-left-≃ {t = t} {t′} refl refl)

wedge-susp-≃ : Γ ≃c Γ′ → Δ ≃c Δ′ → wedge-susp Γ Δ ≃c wedge-susp Γ′ Δ′
wedge-susp-≃ p q = wedge-≃ (susp-ctx-≃ p) (Var≃ (cong (2 +_) (≃c-preserve-length p)) (cong (λ - → toℕ (inject₁ (fromℕ -))) (≃c-preserve-length p))) q

wedge-susp-inc-right-≃ : n ≡ n′ → m ≡ m′ → wedge-susp-inc-right n m ≃s wedge-susp-inc-right n′ m′
wedge-susp-inc-right-≃ refl refl = refl≃s

wedge-susp-inc-left-≃ : n ≡ n′ → m ≡ m′ → wedge-susp-inc-left n m ≃s wedge-susp-inc-left n′ m′
wedge-susp-inc-left-≃ refl refl = refl≃s

sub-from-wedge-≃ : σ ≃s σ′ → τ ≃s τ′ → sub-from-wedge σ τ ≃s sub-from-wedge σ′ τ′
sub-from-wedge-≃ p (Ext≃ (Null≃ y) x) = p
sub-from-wedge-≃ p (Ext≃ (Ext≃ q y) x) = Ext≃ (sub-from-wedge-≃ p (Ext≃ q y)) x

sub-between-wedges-≃ : (σ : Sub (suc n) (suc l) ⋆)
                       → (σ′ : Sub (suc n′) (suc l) ⋆)
                       → (τ : Sub (suc m) (suc l′) ⋆)
                       → (s : Tm (suc l))
                       → (τ′ : Sub (suc m′) (suc l′) ⋆)
                       → (s′ : Tm (suc l))
                       → n ≡ n′ → m ≡ m′ → σ ≃s σ′ → τ ≃s τ′ → s ≃tm s′
                       → sub-between-wedges σ τ s ≃s sub-between-wedges σ′ τ′ s′
sub-between-wedges-≃ σ σ′ τ s τ′ s′ refl refl a b c with ≃s-to-≡ a | ≃s-to-≡ b | ≃tm-to-≡ c
... | refl | refl | refl = refl≃s

sub-between-wedge-susps-≃ : (σ : Sub (suc n) (suc l) ⋆)
                            → (σ′ : Sub (suc n′) (suc l) ⋆)
                            → (τ : Sub (suc m) (suc l′) ⋆)
                            → (τ′ : Sub (suc m′) (suc l′) ⋆)
                            → n ≡ n′ → m ≡ m′ → σ ≃s σ′ → τ ≃s τ′
                            → sub-between-wedge-susps σ τ ≃s sub-between-wedge-susps σ′ τ′
sub-between-wedge-susps-≃ σ σ′ τ τ′ refl refl p q = sub-between-wedges-≃ (susp-sub σ) (susp-sub σ′) τ get-snd τ′ get-snd refl refl (susp-sub-≃ p) q refl≃tm

-- wedge left unit

wedge-left-unit : (Γ : Ctx (suc n)) → wedge (∅ , ⋆) 0V Γ ≃c Γ
wedge-inc-right-left-unit : {m : ℕ} → wedge-inc-right 0V m ≃s idSub {suc m}

wedge-left-unit (∅ , A) = Add≃ Emp≃ (sym≃ty (⋆-is-only-ty-in-empty-context A))
wedge-left-unit (Γ , A , B) = Add≃ (wedge-left-unit (Γ , A)) (trans≃ty (sub-action-≃-ty refl≃ty wedge-inc-right-left-unit) (id-on-ty B))

wedge-inc-right-left-unit {zero} = refl≃s
wedge-inc-right-left-unit {suc m} = Ext≃ (wk-sub-≃ (wedge-inc-right-left-unit {m})) (Var≃ (cong suc (cong suc (+-identityʳ m))) refl)

wedge-inc-right-assoc : (t : Tm (suc l)) → (s : Tm (suc m)) → (n : ℕ)
                      → wedge-inc-right (s [ wedge-inc-right t m ]tm) n
                        ≃s
                        wedge-inc-right s n ● wedge-inc-right t (n + m)
wedge-inc-right-assoc t s zero = refl≃s
wedge-inc-right-assoc t s (suc n) = Ext≃ lem (Var≃ (cong suc (cong suc (sym (+-assoc n _ _)))) refl)
  where
    open Reasoning sub-setoid
    lem : wk-sub (wedge-inc-right (s [ wedge-inc-right t _ ]tm) n)
          ≃s
          wk-sub (wedge-inc-right s n) ● (wedge-inc-right t (suc n + _))
    lem = begin
      < wk-sub (wedge-inc-right (s [ wedge-inc-right t _ ]tm) n) >s
        ≈⟨ wk-sub-≃ (wedge-inc-right-assoc t s n) ⟩
      < wk-sub (wedge-inc-right s n ● wedge-inc-right t (n + _)) >s
        ≈˘⟨ apply-wk-sub-sub-≃ (wedge-inc-right s n) (wedge-inc-right t (n + _)) ⟩
      < wedge-inc-right s n ● wk-sub (wedge-inc-right t (n + _)) >s
        ≈˘⟨ apply-sub-wk-sub-≃ (wedge-inc-right s n) (wedge-inc-right t (suc n + _)) ⟩
      < wk-sub (wedge-inc-right s n) ● ⟨ wk-sub (wedge-inc-right t (n + _)) , Var zero ⟩ >s ∎

wedge-inc-left-assoc : (t : Tm (suc l)) → (s : Tm (suc m)) → (n : ℕ)
                     → wedge-inc-left t m ● wedge-inc-left (s [ wedge-inc-right t m ]tm) n
                       ≃s
                       wedge-inc-left t (n + m)
wedge-inc-left-assoc t s zero = id-right-unit (wedge-inc-left t _)
wedge-inc-left-assoc {m = m} t s (suc n) = begin
  < wedge-inc-left t m ● wk-sub (wedge-inc-left (s [ wedge-inc-right t m ]tm) n) >s
    ≈⟨ apply-wk-sub-sub-≃ (wedge-inc-left t m) _ ⟩
  < wk-sub (wedge-inc-left t m ● wedge-inc-left (s [ wedge-inc-right t m ]tm) n) >s
    ≈⟨ wk-sub-≃ (wedge-inc-left-assoc t s n) ⟩
  < wk-sub (wedge-inc-left t (n + m)) >s ∎
  where
    open Reasoning sub-setoid

wedge-incs-assoc : (t : Tm (suc l)) → (s : Tm (suc m)) → (n : ℕ)
                 → wedge-inc-right t m ● wedge-inc-left (s [ wedge-inc-right t m ]tm) n
                   ≃s
                   wedge-inc-left s n ● wedge-inc-right t (n + m)
wedge-incs-assoc {m = m} t s zero = begin
  < wedge-inc-right t m ● idSub >s
    ≈⟨ id-right-unit (wedge-inc-right t m) ⟩
  < wedge-inc-right t m >s
    ≈˘⟨ id-left-unit (wedge-inc-right t m) ⟩
  < idSub ● wedge-inc-right t m >s ∎
  where
    open Reasoning sub-setoid
wedge-incs-assoc {m = m} t s (suc n) = begin
  < wedge-inc-right t m ●
      wk-sub (wedge-inc-left (s [ wedge-inc-right t m ]tm) n) >s
    ≈⟨ apply-wk-sub-sub-≃ (wedge-inc-right t m) _ ⟩
  < wk-sub (wedge-inc-right t m ● wedge-inc-left (s [ wedge-inc-right t m ]tm) n) >s
    ≈⟨ wk-sub-≃ (wedge-incs-assoc t s n) ⟩
  < wk-sub (wedge-inc-left s n ● wedge-inc-right t (n + m)) >s
    ≈˘⟨ apply-wk-sub-sub-≃ (wedge-inc-left s n) _ ⟩
  < wedge-inc-left s n ● wk-sub (wedge-inc-right t (n + m)) >s
    ≈˘⟨ apply-sub-wk-sub-≃ (wedge-inc-left s n) _ ⟩
  < wk-sub (wedge-inc-left s n) ●
      ⟨ wk-sub (wedge-inc-right t (n + m)) , Var 0F ⟩ >s ∎
  where
    open Reasoning sub-setoid

wedge-assoc : (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m)) → (s : Tm (suc m)) → (Υ : Ctx (suc l))
              → wedge (wedge Γ t Δ) (s [ wedge-inc-right t m ]tm) Υ ≃c wedge Γ t (wedge Δ s Υ)
wedge-assoc Γ t Δ s (∅ , A) = refl≃c
wedge-assoc Γ t (Δ , A′) s (∅ , B , A) = Add≃ refl≃c (assoc-ty _ _ A)
wedge-assoc Γ t (Δ , A′) s (Υ , C , B , A) = Add≃ (wedge-assoc Γ t (Δ , A′) s (Υ , C , B)) (begin
  < A [ wedge-inc-right (s [ wedge-inc-right t _ ]tm) (ctxLength (Υ , C)) ]ty
    >ty ≈⟨ sub-action-≃-ty (refl≃ty {A = A}) (wedge-inc-right-assoc t s _) ⟩
  < A [ wedge-inc-right s (ctxLength (Υ , C))
      ● wedge-inc-right t (ctxLength (wedge (Δ , A′) s (Υ , C))) ]ty >ty
    ≈⟨ assoc-ty _ _ A ⟩
  < A [ wedge-inc-right s (ctxLength (Υ , C)) ]ty
      [ wedge-inc-right t (ctxLength (wedge (Δ , A′) s (Υ , C))) ]ty >ty ∎)
  where
    open Reasoning ty-setoid

wedge-susp-assoc : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → (s : Tm (suc m)) → (Υ : Ctx (suc l))
              → wedge (wedge-susp Γ Δ) (s [ wedge-susp-inc-right n m ]tm) Υ ≃c wedge-susp Γ (wedge Δ s Υ)
wedge-susp-assoc Γ Δ s Υ = wedge-assoc (susp-ctx Γ) get-snd Δ s Υ

sub-from-wedge-inc-left : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → wedge-inc-left t m ● sub-from-wedge σ τ ≃s σ
sub-from-wedge-inc-left σ t τ@(⟨ ⟨ _ ⟩′ , s ⟩) = id-left-unit (sub-from-wedge σ τ)
sub-from-wedge-inc-left σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = begin
  < wedge-inc-left t (suc _) ● sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩ >s
    ≈⟨ apply-sub-wk-sub-≃ (wedge-inc-left t _) (sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩) ⟩
  < wedge-inc-left t _ ● sub-from-wedge σ ⟨ τ , s ⟩ >s
    ≈⟨ sub-from-wedge-inc-left σ t ⟨ τ , s ⟩ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid

sub-from-wedge-inc-right : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → (t [ σ ]tm ≃tm Var (fromℕ _) [ τ ]tm) → wedge-inc-right t m ● sub-from-wedge σ τ ≃s τ
sub-from-wedge-inc-right σ t ⟨ ⟨ _ ⟩′ , s ⟩ p = Ext≃ refl≃s p
sub-from-wedge-inc-right σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≃ lem refl≃tm
  where
    open Reasoning sub-setoid
    lem : wk-sub (wedge-inc-right t _) ● sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩ ≃s ⟨ τ , s ⟩
    lem = begin
      < wk-sub (wedge-inc-right t _) ● sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩ >s
        ≈⟨ apply-sub-wk-sub-≃ (wedge-inc-right t _) (sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩) ⟩
      < wedge-inc-right t _ ● sub-from-wedge σ ⟨ τ , s ⟩ >s
        ≈⟨ sub-from-wedge-inc-right σ t ⟨ τ , s ⟩ p ⟩
      < ⟨ τ , s ⟩ >s ∎

sub-between-wedges-inc-left : (σ : Sub (suc n) (suc l) ⋆)
                              → (t : Tm (suc n))
                              → (τ : Sub (suc m) (suc l′) ⋆)
                              → (s : Tm (suc l))
                              → wedge-inc-left t m ● sub-between-wedges σ τ s
                                ≃s
                                σ ● wedge-inc-left s l′
sub-between-wedges-inc-left {l′ = l′} σ t τ s = sub-from-wedge-inc-left (σ ● wedge-inc-left s l′) t (τ ● wedge-inc-right s l′)

sub-between-wedge-susps-inc-left : (σ : Sub (suc n) (suc l) ⋆)
                                   → (τ : Sub (suc m) (suc l′) ⋆)
                                   → wedge-susp-inc-left n m ● sub-between-wedge-susps σ τ
                                     ≃s
                                     susp-sub σ ● wedge-susp-inc-left l l′
sub-between-wedge-susps-inc-left σ τ = sub-between-wedges-inc-left (susp-sub σ) get-snd τ get-snd

wedge-inc-fst-var : (t : Tm (suc n)) → (m : ℕ) → t [ wedge-inc-left t m ]tm ≃tm Var (fromℕ _) [ wedge-inc-right t m ]tm
wedge-inc-fst-var t zero = id-on-tm t
wedge-inc-fst-var t (suc m) = begin
  < t [ wedge-inc-left t (suc m) ]tm >tm ≈⟨ apply-wk-sub-tm-≃ t (wedge-inc-left t m) ⟩
  < wk-tm (t [ wedge-inc-left t m ]tm) >tm ≈⟨ wk-tm-≃ (wedge-inc-fst-var t m) ⟩
  < wk-tm (Var (fromℕ _) [ wedge-inc-right t m ]tm) >tm ≈˘⟨ apply-wk-sub-tm-≃ (Var (fromℕ _)) (wedge-inc-right t m) ⟩
  < Var (fromℕ (suc _)) [ wedge-inc-right t (suc m) ]tm >tm ∎
  where
    open Reasoning tm-setoid

sub-between-wedges-inc-right : (σ : Sub (suc n) (suc l) ⋆)
                               → (t : Tm (suc n))
                               → (τ : Sub (suc m) (suc l′) ⋆)
                               → (s : Tm (suc l))
                               → t [ σ ]tm ≃tm s
                               → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                               → wedge-inc-right t m ● sub-between-wedges σ τ s
                                 ≃s
                                 τ ● wedge-inc-right s l′
sub-between-wedges-inc-right {l′ = l′} σ t τ s p q = sub-from-wedge-inc-right (σ ● wedge-inc-left s l′) t (τ ● wedge-inc-right s l′) (begin
  < t [ σ ● wedge-inc-left s l′ ]tm >tm
    ≈⟨ assoc-tm σ (wedge-inc-left s l′) t ⟩
  < (t [ σ ]tm) [ wedge-inc-left s l′ ]tm >tm
    ≈⟨ sub-action-≃-tm p refl≃s ⟩
  < s [ wedge-inc-left s l′ ]tm >tm
    ≈⟨ wedge-inc-fst-var s l′ ⟩
  < Var (fromℕ l′) [ wedge-inc-right s l′ ]tm >tm
    ≈˘⟨ sub-action-≃-tm q refl≃s ⟩
  < (Var (fromℕ _) [ τ ]tm) [ wedge-inc-right s l′ ]tm >tm
    ≈˘⟨ assoc-tm τ (wedge-inc-right s l′) (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ τ ● wedge-inc-right s l′ ]tm >tm ∎)
  where
    open Reasoning tm-setoid

sub-between-wedge-susps-inc-right : (σ : Sub (suc n) (suc l) ⋆)
                                    → (τ : Sub (suc m) (suc l′) ⋆)
                                    → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                                    → wedge-susp-inc-right n m ● sub-between-wedge-susps σ τ
                                      ≃s
                                      τ ● wedge-susp-inc-right l l′
sub-between-wedge-susps-inc-right σ τ p = sub-between-wedges-inc-right (susp-sub σ) get-snd τ get-snd (sym≃tm (susp-sub-preserve-get-snd σ)) p

wedge-inc-left-fst-var : (t : Tm (suc n)) → (m : ℕ) → Var (fromℕ _) [ wedge-inc-left t m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
wedge-inc-left-fst-var t zero = id-on-tm (Var (fromℕ _))
wedge-inc-left-fst-var t (suc m) = trans≃tm (apply-wk-sub-tm-≃ (Var (fromℕ _)) (wedge-inc-left t m)) (wk-tm-≃ (wedge-inc-left-fst-var t m))

sub-from-wedge-fst-var : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A) → Var (fromℕ _) [ sub-from-wedge σ τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-wedge-fst-var σ ⟨ ⟨ _ ⟩′ , s ⟩ = refl≃tm
sub-from-wedge-fst-var σ ⟨ ⟨ τ , s ⟩ , u ⟩ = sub-from-wedge-fst-var σ ⟨ τ , s ⟩

sub-between-wedges-fst-var : (σ : Sub (suc n) (suc l) ⋆)
                             → (τ : Sub (suc m) (suc l′) ⋆)
                             → (s : Tm (suc l))
                             → Var (fromℕ _) [ σ ]tm ≃tm Var (fromℕ l)
                             → Var (fromℕ _) [ sub-between-wedges σ τ s ]tm ≃tm Var (fromℕ (l′ + l))
sub-between-wedges-fst-var {l′ = l′} σ τ s p = begin
  < Var (fromℕ _)
    [ sub-from-wedge (σ ● wedge-inc-left s l′) (τ ● wedge-inc-right s l′) ]tm >tm
    ≈⟨ sub-from-wedge-fst-var (σ ● wedge-inc-left s l′) (τ ● wedge-inc-right s l′) ⟩
  < Var (fromℕ _) [ σ ● wedge-inc-left s l′ ]tm >tm
    ≈⟨ assoc-tm σ (wedge-inc-left s l′) (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ σ ]tm [ wedge-inc-left s l′ ]tm >tm
    ≈⟨ sub-action-≃-tm p refl≃s ⟩
  < Var (fromℕ _) [ wedge-inc-left s l′ ]tm >tm
    ≈⟨ wedge-inc-left-fst-var s l′ ⟩
  < Var (fromℕ _) >tm ∎
  where
    open Reasoning tm-setoid

sub-between-wedge-susps-fst-var : (σ : Sub (suc n) (suc l) ⋆)
                                  → (τ : Sub (suc m) (suc l′) ⋆)
                                  → Var (fromℕ _) [ sub-between-wedge-susps σ τ ]tm ≃tm Var (fromℕ (l′ + (2 + l)))
sub-between-wedge-susps-fst-var σ τ = sub-between-wedges-fst-var (susp-sub σ) τ get-snd (sym≃tm (susp-sub-preserve-get-fst σ))

between-wedge-from-wedge : (σ : Sub (suc n) (suc l) ⋆)
                         → (τ : Sub (suc m) (suc l′) ⋆)
                         → (s : Tm (suc l))
                         → (σ′ : Sub (suc l) o A)
                         → (τ′ : Sub (suc l′) o A)
                         → s [ σ′ ]tm ≃tm Var (fromℕ _) [ τ′ ]tm
                         → sub-between-wedges σ τ s ● sub-from-wedge σ′ τ′
                           ≃s
                           sub-from-wedge (σ ● σ′) (τ ● τ′)
between-wedge-from-wedge σ ⟨ ⟨ _ ⟩′ , t ⟩ s σ′ τ′ p = begin
  < (σ ● wedge-inc-left s _) ● sub-from-wedge σ′ τ′ >s
    ≈˘⟨ ●-assoc σ (wedge-inc-left s _) (sub-from-wedge σ′ τ′) ⟩
  < σ ● wedge-inc-left s _ ● sub-from-wedge σ′ τ′ >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-wedge-inc-left σ′ s τ′) ⟩
  < σ ● σ′ >s ∎
  where
    open Reasoning sub-setoid
between-wedge-from-wedge σ ⟨ ⟨ τ , u ⟩ , t ⟩ s σ′ τ′ p = Ext≃ (between-wedge-from-wedge σ ⟨ τ , u ⟩ s σ′ τ′ p) tm-lem
  where
    tm-lem : t [ wedge-inc-right s _ ]tm [ sub-from-wedge σ′ τ′ ]tm
         ≃tm t [ τ′ ]tm
    tm-lem = begin
      < t [ wedge-inc-right s _ ]tm [ sub-from-wedge σ′ τ′ ]tm >tm
        ≈˘⟨ assoc-tm (wedge-inc-right s _) (sub-from-wedge σ′ τ′) t ⟩
      < t [ wedge-inc-right s _ ● sub-from-wedge σ′ τ′ ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = t}) (sub-from-wedge-inc-right σ′ s τ′ p) ⟩
      < t [ τ′ ]tm >tm ∎
      where
        open Reasoning tm-setoid

sub-between-wedges-comp : (σ : Sub (suc n) (suc l) ⋆)
                        → (τ : Sub (suc m) (suc l′) ⋆)
                        → (s : Tm (suc l))
                        → (σ′ : Sub (suc l) (suc n′) ⋆)
                        → (u : Tm (suc n′))
                        → (τ′ : Sub (suc l′) (suc m′) ⋆)
                        → s [ σ′ ]tm ≃tm u
                        → Var (fromℕ l′) [ τ′ ]tm ≃tm Var (fromℕ m′)
                        → sub-between-wedges σ τ s ● sub-between-wedges σ′ τ′ u
                          ≃s
                          sub-between-wedges (σ ● σ′) (τ ● τ′) u
sub-between-wedges-comp {l′ = l′} {m′ = m′} σ ⟨ ⟨ _ ⟩′ , x ⟩ s σ′ u τ′ p q = begin
  < (σ ● wedge-inc-left s l′) ● sub-from-wedge (σ′ ● wedge-inc-left u m′) (τ′ ● wedge-inc-right u m′) >s
    ≈˘⟨ ●-assoc σ
                (wedge-inc-left s l′)
                (sub-from-wedge (σ′ ● wedge-inc-left u m′) (τ′ ● wedge-inc-right u m′)) ⟩
  < σ ● wedge-inc-left s l′ ● sub-from-wedge (σ′ ● wedge-inc-left u m′) (τ′ ● wedge-inc-right u m′) >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-wedge-inc-left (σ′ ● wedge-inc-left u m′) s (τ′ ● wedge-inc-right u m′)) ⟩
  < σ ● σ′ ● wedge-inc-left u m′ >s
    ≈⟨ ●-assoc σ σ′ (wedge-inc-left u m′) ⟩
  < (σ ● σ′) ● wedge-inc-left u m′ >s ∎
  where
    open Reasoning sub-setoid
sub-between-wedges-comp {l′ = l′} {m′ = m′} σ ⟨ ⟨ τ , y ⟩ , x ⟩ s σ′ u τ′ p q = Ext≃ (sub-between-wedges-comp σ ⟨ τ , y ⟩ s σ′ u τ′ p q) (begin
  < x [ wedge-inc-right s l′ ]tm
      [ sub-between-wedges σ′ τ′ u ]tm >tm
    ≈˘⟨ assoc-tm (wedge-inc-right s l′) (sub-between-wedges σ′ τ′ u) x ⟩
  < x [ wedge-inc-right s l′ ● sub-between-wedges σ′ τ′ u ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = x}) (sub-between-wedges-inc-right σ′ s τ′ u p q) ⟩
  < x [ τ′ ● wedge-inc-right u m′ ]tm >tm
    ≈⟨ assoc-tm τ′ (wedge-inc-right u m′) x ⟩
  < x [ τ′ ]tm [ wedge-inc-right u m′ ]tm >tm ∎)
  where
    open Reasoning tm-setoid

sub-between-wedge-susps-comp : (σ : Sub (suc n) (suc l) ⋆)
                             → (τ : Sub (suc m) (suc l′) ⋆)
                             → (σ′ : Sub (suc l) (suc n′) ⋆)
                             → (τ′ : Sub (suc l′) (suc m′) ⋆)
                             → Var (fromℕ l′) [ τ′ ]tm ≃tm Var (fromℕ m′)
                             → sub-between-wedge-susps σ τ ● sub-between-wedge-susps σ′ τ′
                               ≃s
                               sub-between-wedge-susps (σ ● σ′) (τ ● τ′)
sub-between-wedge-susps-comp σ τ σ′ τ′ p = begin
  < sub-between-wedges (susp-sub σ) τ get-snd ● sub-between-wedges (susp-sub σ′) τ′ get-snd >s
    ≈⟨ sub-between-wedges-comp (susp-sub σ) τ get-snd (susp-sub σ′) get-snd τ′
                               (sym≃tm (susp-sub-preserve-get-snd σ′)) p ⟩
  < sub-between-wedges (susp-sub σ ● susp-sub σ′) (τ ● τ′) get-snd >s
    ≈⟨ sub-between-wedges-≃ (susp-sub σ ● susp-sub σ′)
                            (susp-sub (σ ● σ′))
                            (τ ● τ′) get-snd (τ ● τ′) get-snd refl refl
                            (sym≃s (susp-functorial σ σ′)) refl≃s refl≃tm ⟩
  < sub-between-wedges (susp-sub (σ ● σ′)) (τ ● τ′) get-snd >s ∎
  where
    open Reasoning sub-setoid

sub-from-wedge-wk : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A) → wk-sub (sub-from-wedge σ τ) ≃s sub-from-wedge (wk-sub σ) (wk-sub τ)
sub-from-wedge-wk σ ⟨ ⟨ _ ⟩′ , t ⟩ = refl≃s
sub-from-wedge-wk σ ⟨ ⟨ τ , s ⟩ , t ⟩ = Ext≃ (sub-from-wedge-wk σ ⟨ τ , s ⟩) refl≃tm

sub-from-wedge-susp-↑ : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A) → susp-sub-↑ (sub-from-wedge σ τ) ≃s sub-from-wedge (susp-sub-↑ σ) (susp-sub-↑ τ)
sub-from-wedge-susp-↑ σ ⟨ ⟨ _ ⟩′ , t ⟩ = refl≃s
sub-from-wedge-susp-↑ σ ⟨ ⟨ τ , s ⟩ , t ⟩ = Ext≃ (sub-from-wedge-susp-↑ σ ⟨ τ , s ⟩) refl≃tm

sub-from-wedge-sub : (σ : Sub (suc n) l A)
                   → (τ : Sub (suc m) l A)
                   → (μ : Sub l l′ B)
                   → sub-from-wedge σ τ ● μ ≃s sub-from-wedge (σ ● μ) (τ ● μ)
sub-from-wedge-sub σ ⟨ ⟨ _ ⟩′ , t ⟩ μ = refl≃s
sub-from-wedge-sub σ ⟨ ⟨ τ , s ⟩ , t ⟩ μ = Ext≃ (sub-from-wedge-sub σ ⟨ τ , s ⟩ μ) refl≃tm

sub-from-wedge-prop : (t : Tm (suc n)) → {m : ℕ}
                      → sub-from-wedge (wedge-inc-left t m)
                                         (wedge-inc-right t m)
                      ≃s idSub {suc (m + n)}
sub-from-wedge-prop t {zero} = refl≃s
sub-from-wedge-prop t {suc zero} = refl≃s
sub-from-wedge-prop t {suc (suc m)} = Ext≃ (trans≃s (sym≃s (sub-from-wedge-wk (wedge-inc-left t (suc m)) (wedge-inc-right t (suc m)))) (wk-sub-≃ (sub-from-wedge-prop t {suc m}))) refl≃tm

sub-from-wedge-prop′ : (t : Tm (suc n)) → (m : ℕ)
                     → (σ : Sub (suc (m + n)) l A)
                     → sub-from-wedge (wedge-inc-left t m ● σ)
                                      (wedge-inc-right t m ● σ)
                       ≃s σ
sub-from-wedge-prop′ t m σ = begin
  < sub-from-wedge (wedge-inc-left t m ● σ) (wedge-inc-right t m ● σ) >s
    ≈˘⟨ sub-from-wedge-sub (wedge-inc-left t m) (wedge-inc-right t m) σ ⟩
  < sub-from-wedge (wedge-inc-left t m) (wedge-inc-right t m) ● σ >s
    ≈⟨ sub-action-≃-sub (sub-from-wedge-prop t) refl≃s ⟩
  < idSub ● σ >s
    ≈⟨ id-left-unit σ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid

wedge-inc-left-var-to-var : (t : Tm (suc n)) → (m : ℕ) → varToVar (wedge-inc-left t m)
wedge-inc-left-var-to-var {n = n} t zero = id-is-var-to-var
wedge-inc-left-var-to-var t (suc m) = wk-sub-preserve-var-to-var (wedge-inc-left t m) ⦃ wedge-inc-left-var-to-var t m ⦄

wedge-inc-right-var-to-var : (t : Tm (suc n)) → (m : ℕ) → .⦃ isVar t ⦄ → varToVar (wedge-inc-right t m)
wedge-inc-right-var-to-var t zero = extend-var-to-var ⟨ _ ⟩′ t
wedge-inc-right-var-to-var t (suc m) = wk-sub-preserve-var-to-var (wedge-inc-right t m) ⦃ wedge-inc-right-var-to-var t m ⦄ ,, tt

wedge-glob : (Γ : Ctx (suc n)) → ⦃ ctx-is-globular Γ ⦄ → (t : Tm (suc n)) → .⦃ isVar t ⦄ → (Δ : Ctx (suc m)) → ⦃ ctx-is-globular Δ ⦄ → ctx-is-globular (wedge Γ t Δ)
wedge-glob Γ t (∅ , A) = it
wedge-glob Γ t (Δ , B , A) ⦃ p ⦄ = (wedge-glob Γ t (Δ , B) ⦃ proj₁ p ⦄) ,, var-to-var-comp-ty A ⦃ proj₂ p ⦄ (wedge-inc-right t (ctxLength Δ)) ⦃ wedge-inc-right-var-to-var t _ ⦄

wedge-susp-glob : (Γ : Ctx (suc n)) → ⦃ ctx-is-globular Γ ⦄ → (Δ : Ctx (suc m)) → ⦃ ctx-is-globular Δ ⦄ → ctx-is-globular (wedge-susp Γ Δ)
wedge-susp-glob Γ Δ = wedge-glob (susp-ctx Γ) ⦃ susp-ctx-glob Γ ⦄ get-snd Δ

wedge-susp-inc-left-var-to-var : (n m : ℕ) → varToVar (wedge-susp-inc-left n m)
wedge-susp-inc-left-var-to-var n m = wedge-inc-left-var-to-var get-snd m

wedge-susp-inc-right-var-to-var : (n m : ℕ) → varToVar (wedge-susp-inc-right n m)
wedge-susp-inc-right-var-to-var n m = wedge-inc-right-var-to-var get-snd m

sub-between-wedges-id : (t : Tm (suc n))
                      → {m : ℕ}
                      → sub-between-wedges idSub (idSub {suc m}) t
                        ≃s
                        idSub {suc (m + n)}
sub-between-wedges-id t {m} = begin
  < sub-from-wedge (idSub ● wedge-inc-left t m) (idSub ● wedge-inc-right t m) >s
    ≈⟨ sub-from-wedge-≃ (id-left-unit (wedge-inc-left t m)) (id-left-unit (wedge-inc-right t m)) ⟩
  < sub-from-wedge (wedge-inc-left t m) (wedge-inc-right t m) >s
    ≈⟨ sub-from-wedge-prop t ⟩
  < idSub >s ∎
  where
    open Reasoning sub-setoid

sub-between-wedge-susps-id : (n m : ℕ) → sub-between-wedge-susps (idSub {suc n}) (idSub {suc m}) ≃s idSub {suc (m + (2 + n))}
sub-between-wedge-susps-id n m = begin
  < sub-between-wedges (susp-sub idSub) idSub get-snd >s
    ≈⟨ sub-between-wedges-≃ (susp-sub idSub) idSub idSub get-snd idSub get-snd refl refl susp-functorial-id refl≃s refl≃tm ⟩
  < sub-between-wedges idSub idSub get-snd >s
    ≈⟨ sub-between-wedges-id get-snd ⟩
  < idSub >s ∎
  where
    open Reasoning sub-setoid
