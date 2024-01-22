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
wedge-inc-right-≃ {m = suc m} refl q refl = Ext≃ (lift-sub-≃ (wedge-inc-right-≃ refl q refl)) (Var≃ refl refl)

wedge-inc-left-≃ : {t : Tm (suc n)} → {t′ : Tm (suc n′)} → n ≡ n′ → m ≡ m′ → wedge-inc-left t m ≃s wedge-inc-left t′ m′
wedge-inc-left-≃ {m = zero} refl refl = refl≃s
wedge-inc-left-≃ {m = suc m} {t = t} {t′} refl refl = lift-sub-≃ (wedge-inc-left-≃ {t = t} {t′} refl refl)

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
wedge-inc-right-left-unit {suc m} = Ext≃ (lift-sub-≃ (wedge-inc-right-left-unit {m})) (Var≃ (cong suc (cong suc (+-identityʳ m))) refl)

wedge-inc-right-assoc : (t : Tm (suc l)) → (s : Tm (suc m)) → (n : ℕ)
                        → wedge-inc-right (s [ wedge-inc-right t m ]tm) n
                          ≃s
                          wedge-inc-right t (n + m) ● wedge-inc-right s n
wedge-inc-right-assoc t s zero = refl≃s
wedge-inc-right-assoc t s (suc n) = Ext≃ lem (Var≃ (cong suc (cong suc (sym (+-assoc n _ _)))) refl)
  where
    open Reasoning sub-setoid
    lem : lift-sub (wedge-inc-right (s [ wedge-inc-right t _ ]tm) n) ≃s
          (wedge-inc-right t (suc n + _) ● lift-sub (wedge-inc-right s n))
    lem = begin
      < lift-sub (wedge-inc-right (s [ wedge-inc-right t _ ]tm) n) >s
        ≈⟨ lift-sub-≃ (wedge-inc-right-assoc t s n) ⟩
      < lift-sub (wedge-inc-right t (n + _) ● wedge-inc-right s n) >s
        ≈˘⟨ apply-lifted-sub-sub-≃ (wedge-inc-right s n) (wedge-inc-right t (n + _)) ⟩
      < lift-sub (wedge-inc-right t (n + _)) ● wedge-inc-right s n >s
        ≈˘⟨ apply-sub-lifted-sub-≃ (wedge-inc-right s n) (wedge-inc-right t (suc n + _)) ⟩
      < ⟨ lift-sub (wedge-inc-right t (n + _)) , Var zero ⟩ ● lift-sub (wedge-inc-right s n) >s ∎

wedge-assoc : (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m)) → (s : Tm (suc m)) → (Υ : Ctx (suc l))
              → wedge (wedge Γ t Δ) (s [ wedge-inc-right t m ]tm) Υ ≃c wedge Γ t (wedge Δ s Υ)
wedge-assoc Γ t Δ s (∅ , A) = refl≃c
wedge-assoc Γ t (Δ , A′) s (∅ , B , A) = Add≃ refl≃c (assoc-ty _ _ A)
wedge-assoc Γ t (Δ , A′) s (Υ , C , B , A) = Add≃ (wedge-assoc Γ t (Δ , A′) s (Υ , C , B)) (begin
  < A [ wedge-inc-right (s [ wedge-inc-right t _ ]tm) (ctxLength (Υ , C)) ]ty
    >ty ≈⟨ sub-action-≃-ty (refl≃ty {A = A}) (wedge-inc-right-assoc t s _) ⟩
  < A [ wedge-inc-right t (ctxLength (wedge (Δ , A′) s (Υ , C)))
      ● wedge-inc-right s (ctxLength (Υ , C)) ]ty >ty
    ≈⟨ assoc-ty _ _ A ⟩
  < A [ wedge-inc-right s (ctxLength (Υ , C)) ]ty
      [ wedge-inc-right t (ctxLength (wedge (Δ , A′) s (Υ , C))) ]ty >ty ∎)
  where
    open Reasoning ty-setoid

wedge-susp-assoc : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → (s : Tm (suc m)) → (Υ : Ctx (suc l))
              → wedge (wedge-susp Γ Δ) (s [ wedge-susp-inc-right n m ]tm) Υ ≃c wedge-susp Γ (wedge Δ s Υ)
wedge-susp-assoc Γ Δ s Υ = wedge-assoc (susp-ctx Γ) get-snd Δ s Υ

sub-from-wedge-inc-left : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → sub-from-wedge σ τ ● wedge-inc-left t m ≃s σ
sub-from-wedge-inc-left σ t τ@(⟨ ⟨⟩ , s ⟩) = id-right-unit (sub-from-wedge σ τ)
sub-from-wedge-inc-left σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = begin
  < sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩ ● wedge-inc-left t (suc _) >s
    ≈⟨ apply-sub-lifted-sub-≃ (wedge-inc-left t _) (sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩) ⟩
  < sub-from-wedge σ ⟨ τ , s ⟩ ● wedge-inc-left t _ >s
    ≈⟨ sub-from-wedge-inc-left σ t ⟨ τ , s ⟩ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid

sub-from-wedge-inc-right : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → (t [ σ ]tm ≃tm Var (fromℕ _) [ τ ]tm) → sub-from-wedge σ τ ● wedge-inc-right t m ≃s τ
sub-from-wedge-inc-right σ t ⟨ ⟨⟩ , s ⟩ p = Ext≃ refl≃s p
sub-from-wedge-inc-right σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≃ lem refl≃tm
  where
    open Reasoning sub-setoid
    lem : sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩ ● lift-sub (wedge-inc-right t _) ≃s ⟨ τ , s ⟩
    lem = begin
      < sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩ ● lift-sub (wedge-inc-right t _) >s
        ≈⟨ apply-sub-lifted-sub-≃ (wedge-inc-right t _) (sub-from-wedge σ ⟨ ⟨ τ , s ⟩ , u ⟩) ⟩
      < sub-from-wedge σ ⟨ τ , s ⟩ ● wedge-inc-right t _ >s
        ≈⟨ sub-from-wedge-inc-right σ t ⟨ τ , s ⟩ p ⟩
      < ⟨ τ , s ⟩ >s ∎

sub-between-wedges-inc-left : (σ : Sub (suc n) (suc l) ⋆)
                              → (t : Tm (suc n))
                              → (τ : Sub (suc m) (suc l′) ⋆)
                              → (s : Tm (suc l))
                              → sub-between-wedges σ τ s ● wedge-inc-left t m
                              ≃s wedge-inc-left s l′ ● σ
sub-between-wedges-inc-left {l′ = l′} σ t τ s = sub-from-wedge-inc-left (wedge-inc-left s l′ ● σ) t (wedge-inc-right s l′ ● τ)

sub-between-wedge-susps-inc-left : (σ : Sub (suc n) (suc l) ⋆)
                                   → (τ : Sub (suc m) (suc l′) ⋆)
                                   → sub-between-wedge-susps σ τ ● wedge-susp-inc-left n m
                                     ≃s wedge-susp-inc-left l l′ ● susp-sub σ
sub-between-wedge-susps-inc-left σ τ = sub-between-wedges-inc-left (susp-sub σ) get-snd τ get-snd

wedge-inc-fst-var : (t : Tm (suc n)) → (m : ℕ) → t [ wedge-inc-left t m ]tm ≃tm Var (fromℕ _) [ wedge-inc-right t m ]tm
wedge-inc-fst-var t zero = id-on-tm t
wedge-inc-fst-var t (suc m) = begin
  < t [ wedge-inc-left t (suc m) ]tm >tm ≈⟨ apply-lifted-sub-tm-≃ t (wedge-inc-left t m) ⟩
  < lift-tm (t [ wedge-inc-left t m ]tm) >tm ≈⟨ lift-tm-≃ (wedge-inc-fst-var t m) ⟩
  < lift-tm (Var (fromℕ _) [ wedge-inc-right t m ]tm) >tm ≈˘⟨ apply-lifted-sub-tm-≃ (Var (fromℕ _)) (wedge-inc-right t m) ⟩
  < Var (fromℕ (suc _)) [ wedge-inc-right t (suc m) ]tm >tm ∎
  where
    open Reasoning tm-setoid

sub-between-wedges-inc-right : (σ : Sub (suc n) (suc l) ⋆)
                               → (t : Tm (suc n))
                               → (τ : Sub (suc m) (suc l′) ⋆)
                               → (s : Tm (suc l))
                               → t [ σ ]tm ≃tm s
                               → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                               → sub-between-wedges σ τ s ● wedge-inc-right t m
                               ≃s wedge-inc-right s l′ ● τ
sub-between-wedges-inc-right {l′ = l′} σ t τ s p q = sub-from-wedge-inc-right (wedge-inc-left s l′ ● σ ) t (wedge-inc-right s l′ ● τ) (begin
  < t [ wedge-inc-left s l′ ● σ ]tm >tm
    ≈⟨ assoc-tm (wedge-inc-left s l′) σ t ⟩
  < (t [ σ ]tm) [ wedge-inc-left s l′ ]tm >tm
    ≈⟨ sub-action-≃-tm p refl≃s ⟩
  < s [ wedge-inc-left s l′ ]tm >tm
    ≈⟨ wedge-inc-fst-var s l′ ⟩
  < Var (fromℕ l′) [ wedge-inc-right s l′ ]tm >tm
    ≈˘⟨ sub-action-≃-tm q refl≃s ⟩
  < (Var (fromℕ _) [ τ ]tm) [ wedge-inc-right s l′ ]tm >tm
    ≈˘⟨ assoc-tm (wedge-inc-right s l′) τ (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ wedge-inc-right s l′ ● τ ]tm >tm ∎)
  where
    open Reasoning tm-setoid

sub-between-wedge-susps-inc-right : (σ : Sub (suc n) (suc l) ⋆)
                                    → (τ : Sub (suc m) (suc l′) ⋆)
                                    → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                                    → sub-between-wedge-susps σ τ ● wedge-susp-inc-right n m
                                    ≃s wedge-susp-inc-right l l′ ● τ
sub-between-wedge-susps-inc-right σ τ p = sub-between-wedges-inc-right (susp-sub σ) get-snd τ get-snd (sym≃tm (susp-sub-preserve-get-snd σ)) p

wedge-inc-left-fst-var : (t : Tm (suc n)) → (m : ℕ) → Var (fromℕ _) [ wedge-inc-left t m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
wedge-inc-left-fst-var t zero = id-on-tm (Var (fromℕ _))
wedge-inc-left-fst-var t (suc m) = trans≃tm (apply-lifted-sub-tm-≃ (Var (fromℕ _)) (wedge-inc-left t m)) (lift-tm-≃ (wedge-inc-left-fst-var t m))

sub-from-wedge-fst-var : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A) → Var (fromℕ _) [ sub-from-wedge σ τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-wedge-fst-var σ ⟨ ⟨⟩ , s ⟩ = refl≃tm
sub-from-wedge-fst-var σ ⟨ ⟨ τ , s ⟩ , u ⟩ = sub-from-wedge-fst-var σ ⟨ τ , s ⟩

sub-between-wedges-fst-var : (σ : Sub (suc n) (suc l) ⋆)
                             → (τ : Sub (suc m) (suc l′) ⋆)
                             → (s : Tm (suc l))
                             → Var (fromℕ _) [ σ ]tm ≃tm Var (fromℕ l)
                             → Var (fromℕ _) [ sub-between-wedges σ τ s ]tm ≃tm Var (fromℕ (l′ + l))
sub-between-wedges-fst-var {l′ = l′} σ τ s p = begin
  < Var (fromℕ _)
    [ sub-from-wedge (wedge-inc-left s l′ ● σ) (wedge-inc-right s l′ ● τ) ]tm >tm
    ≈⟨ sub-from-wedge-fst-var (wedge-inc-left s l′ ● σ) (wedge-inc-right s l′ ● τ) ⟩
  < Var (fromℕ _) [ wedge-inc-left s l′ ● σ ]tm >tm
    ≈⟨ assoc-tm (wedge-inc-left s l′) σ (Var (fromℕ _)) ⟩
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
                             → sub-from-wedge σ′ τ′ ● sub-between-wedges σ τ s ≃s sub-from-wedge (σ′ ● σ) (τ′ ● τ)
between-wedge-from-wedge σ ⟨ ⟨⟩ , t ⟩ s σ′ τ′ p = begin
  < sub-from-wedge σ′ τ′ ● (wedge-inc-left s _ ● σ) >s
    ≈˘⟨ ●-assoc (sub-from-wedge σ′ τ′) (wedge-inc-left s _) σ ⟩
  < sub-from-wedge σ′ τ′ ● wedge-inc-left s _ ● σ >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-wedge-inc-left σ′ s τ′) ⟩
  < σ′ ● σ >s ∎
  where
    open Reasoning sub-setoid
between-wedge-from-wedge σ ⟨ ⟨ τ , u ⟩ , t ⟩ s σ′ τ′ p = Ext≃ (between-wedge-from-wedge σ ⟨ τ , u ⟩ s σ′ τ′ p) tm-lem
  where
    tm-lem : t [ wedge-inc-right s _ ]tm [ sub-from-wedge σ′ τ′ ]tm
         ≃tm t [ τ′ ]tm
    tm-lem = begin
      < t [ wedge-inc-right s _ ]tm [ sub-from-wedge σ′ τ′ ]tm >tm
        ≈˘⟨ assoc-tm (sub-from-wedge σ′ τ′) (wedge-inc-right s _) t ⟩
      < t [ sub-from-wedge σ′ τ′ ● wedge-inc-right s _ ]tm >tm
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
                          → sub-between-wedges σ′ τ′ u ● sub-between-wedges σ τ s
                          ≃s sub-between-wedges (σ′ ● σ) (τ′ ● τ) u
sub-between-wedges-comp {l′ = l′} {m′ = m′} σ ⟨ ⟨⟩ , x ⟩ s σ′ u τ′ p q = begin
  < sub-from-wedge (wedge-inc-left u m′ ● σ′) (wedge-inc-right u m′ ● τ′)
    ● (wedge-inc-left s l′ ● σ) >s
    ≈˘⟨ ●-assoc (sub-from-wedge (wedge-inc-left u m′ ● σ′)
                  (wedge-inc-right u m′ ● τ′)) (wedge-inc-left s l′) σ ⟩
  < sub-from-wedge (wedge-inc-left u m′ ● σ′) (wedge-inc-right u m′ ● τ′)
    ● wedge-inc-left s l′
    ● σ >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-wedge-inc-left (wedge-inc-left u m′ ● σ′) s (wedge-inc-right u m′ ● τ′)) ⟩
  < wedge-inc-left u m′ ● σ′ ● σ >s
    ≈⟨ ●-assoc (wedge-inc-left u m′) σ′ σ ⟩
  < wedge-inc-left u m′ ● (σ′ ● σ) >s ∎
  where
    open Reasoning sub-setoid
sub-between-wedges-comp {l′ = l′} {m′ = m′} σ ⟨ ⟨ τ , y ⟩ , x ⟩ s σ′ u τ′ p q = Ext≃ (sub-between-wedges-comp σ ⟨ τ , y ⟩ s σ′ u τ′ p q) (begin
  < x [ wedge-inc-right s l′ ]tm
      [ sub-between-wedges σ′ τ′ u ]tm >tm
    ≈˘⟨ assoc-tm (sub-between-wedges σ′ τ′ u) (wedge-inc-right s l′) x ⟩
  < x [ sub-between-wedges σ′ τ′ u ● wedge-inc-right s l′ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = x}) (sub-between-wedges-inc-right σ′ s τ′ u p q) ⟩
  < x [ wedge-inc-right u m′ ● τ′ ]tm >tm
    ≈⟨ assoc-tm (wedge-inc-right u m′) τ′ x ⟩
  < x [ τ′ ]tm [ wedge-inc-right u m′ ]tm >tm ∎)
  where
    open Reasoning tm-setoid

sub-between-wedge-susps-comp : (σ : Sub (suc n) (suc l) ⋆)
                               → (τ : Sub (suc m) (suc l′) ⋆)
                               → (σ′ : Sub (suc l) (suc n′) ⋆)
                               → (τ′ : Sub (suc l′) (suc m′) ⋆)
                               → Var (fromℕ l′) [ τ′ ]tm ≃tm Var (fromℕ m′)
                               → sub-between-wedge-susps σ′ τ′ ● sub-between-wedge-susps σ τ
                               ≃s sub-between-wedge-susps (σ′ ● σ) (τ′ ● τ)
sub-between-wedge-susps-comp σ τ σ′ τ′ p = trans≃s (sub-between-wedges-comp (susp-sub σ) τ get-snd (susp-sub σ′) get-snd τ′ (sym≃tm (susp-sub-preserve-get-snd σ′)) p) (sub-between-wedges-≃ (susp-sub σ′ ● susp-sub σ) (susp-sub (σ′ ● σ)) (τ′ ● τ) get-snd (τ′ ● τ) get-snd refl refl (sym≃s (susp-functorial σ′ σ)) refl≃s refl≃tm)

sub-from-wedge-lift : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A) → lift-sub (sub-from-wedge σ τ) ≃s sub-from-wedge (lift-sub σ) (lift-sub τ)
sub-from-wedge-lift σ ⟨ ⟨⟩ , t ⟩ = refl≃s
sub-from-wedge-lift σ ⟨ ⟨ τ , s ⟩ , t ⟩ = Ext≃ (sub-from-wedge-lift σ ⟨ τ , s ⟩) refl≃tm

sub-from-wedge-susp-res : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A) → susp-sub-res (sub-from-wedge σ τ) ≃s sub-from-wedge (susp-sub-res σ) (susp-sub-res τ)
sub-from-wedge-susp-res σ ⟨ ⟨⟩ , t ⟩ = refl≃s
sub-from-wedge-susp-res σ ⟨ ⟨ τ , s ⟩ , t ⟩ = Ext≃ (sub-from-wedge-susp-res σ ⟨ τ , s ⟩) refl≃tm

sub-from-wedge-sub : (σ : Sub (suc n) l A)
                     → (τ : Sub (suc m) l A)
                     → (μ : Sub l l′ B)
                     → μ ● sub-from-wedge σ τ ≃s sub-from-wedge (μ ● σ) (μ ● τ)
sub-from-wedge-sub σ ⟨ ⟨⟩ , t ⟩ μ = refl≃s
sub-from-wedge-sub σ ⟨ ⟨ τ , s ⟩ , t ⟩ μ = Ext≃ (sub-from-wedge-sub σ ⟨ τ , s ⟩ μ) refl≃tm

sub-from-wedge-prop : (t : Tm (suc n)) → {m : ℕ}
                      → sub-from-wedge (wedge-inc-left t m)
                                         (wedge-inc-right t m)
                      ≃s idSub {suc (m + n)}
sub-from-wedge-prop t {zero} = refl≃s
sub-from-wedge-prop t {suc zero} = refl≃s
sub-from-wedge-prop t {suc (suc m)} = Ext≃ (trans≃s (sym≃s (sub-from-wedge-lift (wedge-inc-left t (suc m)) (wedge-inc-right t (suc m)))) (lift-sub-≃ (sub-from-wedge-prop t {suc m}))) refl≃tm

sub-from-wedge-prop′ : (t : Tm (suc n)) → (m : ℕ)
                       → (σ : Sub (suc (m + n)) l A)
                       → sub-from-wedge (σ ● wedge-inc-left t m)
                                          (σ ● wedge-inc-right t m)
                       ≃s σ
sub-from-wedge-prop′ t m σ = begin
  < sub-from-wedge (σ ● wedge-inc-left t m) (σ ● wedge-inc-right t m) >s
    ≈˘⟨ sub-from-wedge-sub (wedge-inc-left t m) (wedge-inc-right t m) σ ⟩
  < σ ● sub-from-wedge (wedge-inc-left t m) (wedge-inc-right t m) >s
    ≈⟨ sub-action-≃-sub (sub-from-wedge-prop t) refl≃s ⟩
  < σ ● idSub >s
    ≈⟨ id-right-unit σ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid

wedge-inc-left-var-to-var : (t : Tm (suc n)) → (m : ℕ) → varToVar (wedge-inc-left t m)
wedge-inc-left-var-to-var {n = n} t zero = id-is-var-to-var
wedge-inc-left-var-to-var t (suc m) = lift-sub-preserve-var-to-var (wedge-inc-left t m) ⦃ wedge-inc-left-var-to-var t m ⦄

wedge-inc-right-var-to-var : (t : Tm (suc n)) → (m : ℕ) → .⦃ isVar t ⦄ → varToVar (wedge-inc-right t m)
wedge-inc-right-var-to-var t zero = extend-var-to-var ⟨⟩ t
wedge-inc-right-var-to-var t (suc m) = lift-sub-preserve-var-to-var (wedge-inc-right t m) ⦃ wedge-inc-right-var-to-var t m ⦄ ,, tt

wedge-glob : (Γ : Ctx (suc n)) → ⦃ ctx-is-globular Γ ⦄ → (t : Tm (suc n)) → .⦃ isVar t ⦄ → (Δ : Ctx (suc m)) → ⦃ ctx-is-globular Δ ⦄ → ctx-is-globular (wedge Γ t Δ)
wedge-glob Γ t (∅ , A) = it
wedge-glob Γ t (Δ , B , A) ⦃ p ⦄ = (wedge-glob Γ t (Δ , B) ⦃ proj₁ p ⦄) ,, var-to-var-comp-ty A ⦃ proj₂ p ⦄ (wedge-inc-right t (ctxLength Δ)) ⦃ wedge-inc-right-var-to-var t _ ⦄

wedge-susp-glob : (Γ : Ctx (suc n)) → ⦃ ctx-is-globular Γ ⦄ → (Δ : Ctx (suc m)) → ⦃ ctx-is-globular Δ ⦄ → ctx-is-globular (wedge-susp Γ Δ)
wedge-susp-glob Γ Δ = wedge-glob (susp-ctx Γ) ⦃ susp-ctx-glob Γ ⦄ get-snd Δ

wedge-susp-inc-left-var-to-var : (n m : ℕ) → varToVar (wedge-susp-inc-left n m)
wedge-susp-inc-left-var-to-var n m = wedge-inc-left-var-to-var get-snd m

wedge-susp-inc-right-var-to-var : (n m : ℕ) → varToVar (wedge-susp-inc-right n m)
wedge-susp-inc-right-var-to-var n m = wedge-inc-right-var-to-var get-snd m

sub-between-wedges-id : (t : Tm (suc n)) → {m : ℕ} → sub-between-wedges idSub (idSub {suc m}) t ≃s idSub {suc (m + n)}
sub-between-wedges-id t {m} = begin
  < sub-from-wedge (wedge-inc-left t m ● idSub) (wedge-inc-right t m ● idSub) >s
    ≈⟨ sub-from-wedge-≃ (id-right-unit (wedge-inc-left t m)) (id-right-unit (wedge-inc-right t m)) ⟩
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
