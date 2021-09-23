{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Connection
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false) renaming (T to Truth)
-- open import Data.Bool.Properties using (T?)
open import Relation.Nullary

connect-≃ : Γ ≃c Γ′ → t ≃tm t′ → Δ ≃c Δ′ → connect Γ t Δ ≃c connect Γ′ t′ Δ′
connect-inc-right-≃ : {t : Tm (suc n)} → {t′ : Tm (suc n′)} → n ≡ n′ → t ≃tm t′ → m ≡ m′ → connect-inc-right t m ≃s connect-inc-right t′ m′

connect-≃ p q (Add≃ Emp≃ r) = p
connect-≃ p q (Add≃ (Add≃ r s) t) = Add≃ (connect-≃ p q (Add≃ r s)) (sub-action-≃-ty t (connect-inc-right-≃ (cong pred (≃c-preserve-length p)) q (cong pred (≃c-preserve-length (Add≃ r s)))))

connect-inc-right-≃ {m = zero} refl q refl = Ext≃ refl≃s q
connect-inc-right-≃ {m = suc m} refl q refl = Ext≃ (lift-sub-≃ (connect-inc-right-≃ refl q refl)) (Var≃ refl refl)

sub-between-connects-≃ : (σ : Sub (suc n) (suc l) ⋆)
                       → (t : Tm (suc n))
                       → (σ′ : Sub (suc n′) (suc l) ⋆)
                       → (t′ : Tm (suc n′))
                       → (τ : Sub (suc m) (suc l′) ⋆)
                       → (s : Tm (suc l))
                       → (τ′ : Sub (suc m′) (suc l′) ⋆)
                       → (s′ : Tm (suc l))
                       → n ≡ n′ → m ≡ m′ → σ ≃s σ′ → t ≃tm t′ → τ ≃s τ′ → s ≃tm s′
                       → sub-between-connects σ t τ s ≃s sub-between-connects σ′ t′ τ′ s′
sub-between-connects-≃ σ t σ′ t′ τ s τ′ s′ refl refl a b c d with ≃s-to-≡ a | ≃tm-to-≡ b | ≃s-to-≡ c | ≃tm-to-≡ d
... | refl | refl | refl | refl = refl≃s

sub-between-connect-susps-≃ : (σ : Sub (suc n) (suc l) ⋆)
                            → (σ′ : Sub (suc n′) (suc l) ⋆)
                            → (τ : Sub (suc m) (suc l′) ⋆)
                            → (τ′ : Sub (suc m′) (suc l′) ⋆)
                            → n ≡ n′ → m ≡ m′ → σ ≃s σ′ → τ ≃s τ′
                            → sub-between-connect-susps σ τ ≃s sub-between-connect-susps σ′ τ′
sub-between-connect-susps-≃ σ σ′ τ τ′ refl refl p q = sub-between-connects-≃ (suspSub σ) getSnd (suspSub σ′) getSnd τ getSnd τ′ getSnd refl refl (susp-sub-≃ p) refl≃tm q refl≃tm

-- connect left unit

connect-left-unit : (Γ : Ctx (suc n)) → connect (∅ , ⋆) 0V Γ ≃c Γ
connect-inc-right-left-unit : (m : ℕ) → connect-inc-right 0V m ≃s idSub (suc m)

connect-left-unit (∅ , A) = Add≃ Emp≃ (sym≃ty (⋆-is-only-ty-in-empty-context A))
connect-left-unit (Γ , A , B) = Add≃ (connect-left-unit (Γ , A)) (trans≃ty (sub-action-≃-ty refl≃ty (connect-inc-right-left-unit _)) (id-on-ty B))

connect-inc-right-left-unit zero = refl≃s
connect-inc-right-left-unit (suc m) = Ext≃ (lift-sub-≃ (connect-inc-right-left-unit m)) (Var≃ (cong suc (cong suc (+-identityʳ m))) refl)

connect-inc-right-assoc : (t : Tm (suc l)) → (s : Tm (suc m)) → (n : ℕ)
                        → connect-inc-right (s [ connect-inc-right t m ]tm) n
                          ≃s
                          connect-inc-right t (n + m) ∘ connect-inc-right s n
connect-inc-right-assoc t s zero = refl≃s
connect-inc-right-assoc t s (suc n) = Ext≃ lem (Var≃ (cong suc (cong suc (sym (+-assoc n _ _)))) refl)
  where
    open Reasoning sub-setoid
    lem : liftSub (connect-inc-right (s [ connect-inc-right t _ ]tm) n) ≃s
          (connect-inc-right t (suc n + _) ∘ liftSub (connect-inc-right s n))
    lem = begin
      < liftSub (connect-inc-right (s [ connect-inc-right t _ ]tm) n) >s
        ≈⟨ lift-sub-≃ (connect-inc-right-assoc t s n) ⟩
      < liftSub (connect-inc-right t (n + _) ∘ connect-inc-right s n) >s
        ≈˘⟨ apply-lifted-sub-sub-≃ (connect-inc-right s n) (connect-inc-right t (n + _)) ⟩
      < liftSub (connect-inc-right t (n + _)) ∘ connect-inc-right s n >s
        ≈˘⟨ lift-sub-comp-lem-sub (liftSub (connect-inc-right t (n + _))) (connect-inc-right s n) ⟩
      < ⟨ liftSub (connect-inc-right t (n + _)) , Var zero ⟩ ∘ liftSub (connect-inc-right s n) >s ∎

connect-assoc : (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m)) → (s : Tm (suc m)) → (Υ : Ctx (suc l))
              → connect (connect Γ t Δ) (s [ connect-inc-right t m ]tm) Υ ≃c connect Γ t (connect Δ s Υ)
connect-assoc Γ t Δ s (∅ , A) = refl≃c
connect-assoc Γ t (Δ , A′) s (∅ , B , A) = Add≃ refl≃c (assoc-ty _ _ A)
connect-assoc Γ t (Δ , A′) s (Υ , C , B , A) = Add≃ (connect-assoc Γ t (Δ , A′) s (Υ , C , B)) (begin
  < A [ connect-inc-right (s [ connect-inc-right t _ ]tm) (ctxLength (Υ , C)) ]ty
    >ty ≈⟨ sub-action-≃-ty (refl≃ty {A = A}) (connect-inc-right-assoc t s _) ⟩
  < A [ connect-inc-right t (ctxLength (connect (Δ , A′) s (Υ , C)))
      ∘ connect-inc-right s (ctxLength (Υ , C)) ]ty >ty
    ≈⟨ assoc-ty _ _ A ⟩
  < A [ connect-inc-right s (ctxLength (Υ , C)) ]ty
      [ connect-inc-right t (ctxLength (connect (Δ , A′) s (Υ , C))) ]ty >ty ∎)
  where
    open Reasoning ty-setoid

connect-susp-assoc : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → (s : Tm (suc m)) → (Υ : Ctx (suc l))
              → connect (connect-susp Γ Δ) (s [ connect-susp-inc-right n m ]tm) Υ ≃c connect-susp Γ (connect Δ s Υ)
connect-susp-assoc Γ Δ s Υ = connect-assoc (suspCtx Γ) getSnd Δ s Υ

sub-from-connect-inc-left : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → sub-from-connect σ t τ ∘ connect-inc-left t m ≃s σ
sub-from-connect-inc-left σ t τ@(⟨ ⟨⟩ , s ⟩) = id-right-unit (sub-from-connect σ t τ)
sub-from-connect-inc-left σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = trans≃s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-left t _)) (sub-from-connect-inc-left σ t ⟨ τ , s ⟩)

sub-from-connect-inc-right : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → (t [ σ ]tm ≃tm Var (fromℕ _) [ τ ]tm) → sub-from-connect σ t τ ∘ connect-inc-right t m ≃s τ
sub-from-connect-inc-right σ t ⟨ ⟨⟩ , s ⟩ p = Ext≃ refl≃s p
sub-from-connect-inc-right σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≃ (trans≃s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-right t _)) (sub-from-connect-inc-right σ t ⟨ τ , s ⟩ p)) refl≃tm

sub-between-connects-inc-left : (σ : Sub (suc n) (suc l) ⋆)
                              → (t : Tm (suc n))
                              → (τ : Sub (suc m) (suc l′) ⋆)
                              → (s : Tm (suc l))
                              → sub-between-connects σ t τ s ∘ connect-inc-left t m
                              ≃s connect-inc-left s l′ ∘ σ
sub-between-connects-inc-left {l′ = l′} σ t τ s = sub-from-connect-inc-left (connect-inc-left s l′ ∘ σ) t (connect-inc-right s l′ ∘ τ)

sub-between-connect-susps-inc-left : (σ : Sub (suc n) (suc l) ⋆)
                                   → (τ : Sub (suc m) (suc l′) ⋆)
                                   → sub-between-connect-susps σ τ ∘ connect-susp-inc-left n m
                                     ≃s connect-susp-inc-left l l′ ∘ suspSub σ
sub-between-connect-susps-inc-left σ τ = sub-between-connects-inc-left (suspSub σ) getSnd τ getSnd

connect-inc-fst-var : (t : Tm (suc n)) → (m : ℕ) → t [ connect-inc-left t m ]tm ≃tm Var (fromℕ _) [ connect-inc-right t m ]tm
connect-inc-fst-var t zero = id-on-tm t
connect-inc-fst-var t (suc m) = begin
  < t [ connect-inc-left t (suc m) ]tm >tm ≈⟨ apply-lifted-sub-tm-≃ t (connect-inc-left t m) ⟩
  < liftTerm (t [ connect-inc-left t m ]tm) >tm ≈⟨ lift-tm-≃ (connect-inc-fst-var t m) ⟩
  < liftTerm (Var (fromℕ _) [ connect-inc-right t m ]tm) >tm ≈˘⟨ apply-lifted-sub-tm-≃ (Var (fromℕ _)) (connect-inc-right t m) ⟩
  < Var (fromℕ (suc _)) [ connect-inc-right t (suc m) ]tm >tm ∎
  where
    open Reasoning tm-setoid

sub-between-connects-inc-right : (σ : Sub (suc n) (suc l) ⋆)
                               → (t : Tm (suc n))
                               → (τ : Sub (suc m) (suc l′) ⋆)
                               → (s : Tm (suc l))
                               → t [ σ ]tm ≃tm s
                               → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                               → sub-between-connects σ t τ s ∘ connect-inc-right t m
                               ≃s connect-inc-right s l′ ∘ τ
sub-between-connects-inc-right {l′ = l′} σ t τ s p q = sub-from-connect-inc-right (connect-inc-left s l′ ∘ σ ) t (connect-inc-right s l′ ∘ τ) (begin
  < t [ connect-inc-left s l′ ∘ σ ]tm >tm
    ≈⟨ assoc-tm (connect-inc-left s l′) σ t ⟩
  < (t [ σ ]tm) [ connect-inc-left s l′ ]tm >tm
    ≈⟨ sub-action-≃-tm p refl≃s ⟩
  < s [ connect-inc-left s l′ ]tm >tm
    ≈⟨ connect-inc-fst-var s l′ ⟩
  < Var (fromℕ l′) [ connect-inc-right s l′ ]tm >tm
    ≈˘⟨ sub-action-≃-tm q refl≃s ⟩
  < (Var (fromℕ _) [ τ ]tm) [ connect-inc-right s l′ ]tm >tm
    ≈˘⟨ assoc-tm (connect-inc-right s l′) τ (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ connect-inc-right s l′ ∘ τ ]tm >tm ∎)
  where
    open Reasoning tm-setoid

sub-between-connect-susps-inc-right : (σ : Sub (suc n) (suc l) ⋆)
                                    → (τ : Sub (suc m) (suc l′) ⋆)
                                    → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                                    → sub-between-connect-susps σ τ ∘ connect-susp-inc-right n m
                                    ≃s connect-susp-inc-right l l′ ∘ τ
sub-between-connect-susps-inc-right σ τ p = sub-between-connects-inc-right (suspSub σ) getSnd τ getSnd (sym≃tm (susp-sub-preserve-getSnd σ)) p

connect-inc-left-fst-var : (t : Tm (suc n)) → (m : ℕ) → Var (fromℕ _) [ connect-inc-left t m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
connect-inc-left-fst-var t zero = id-on-tm (Var (fromℕ _))
connect-inc-left-fst-var t (suc m) = trans≃tm (apply-lifted-sub-tm-≃ (Var (fromℕ _)) (connect-inc-left t m)) (lift-tm-≃ (connect-inc-left-fst-var t m))

sub-from-connect-fst-var : (σ : Sub (suc n) l A) → (t : Tm (suc n)) → (τ : Sub (suc m) l A) → Var (fromℕ _) [ sub-from-connect σ t τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-fst-var σ t ⟨ ⟨⟩ , s ⟩ = refl≃tm
sub-from-connect-fst-var σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = sub-from-connect-fst-var σ t ⟨ τ , s ⟩

sub-between-connects-fst-var : (σ : Sub (suc n) (suc l) ⋆)
                             → (t : Tm (suc n))
                             → (τ : Sub (suc m) (suc l′) ⋆)
                             → (s : Tm (suc l))
                             → Var (fromℕ _) [ σ ]tm ≃tm Var (fromℕ l)
                             → Var (fromℕ _) [ sub-between-connects σ t τ s ]tm ≃tm Var (fromℕ (l′ + l))
sub-between-connects-fst-var {l′ = l′} σ t τ s p = begin
  < Var (fromℕ _)
    [ sub-from-connect (connect-inc-left s l′ ∘ σ) t (connect-inc-right s l′ ∘ τ) ]tm >tm
    ≈⟨ sub-from-connect-fst-var (connect-inc-left s l′ ∘ σ) t (connect-inc-right s l′ ∘ τ) ⟩
  < Var (fromℕ _) [ connect-inc-left s l′ ∘ σ ]tm >tm
    ≈⟨ assoc-tm (connect-inc-left s l′) σ (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ σ ]tm [ connect-inc-left s l′ ]tm >tm
    ≈⟨ sub-action-≃-tm p refl≃s ⟩
  < Var (fromℕ _) [ connect-inc-left s l′ ]tm >tm
    ≈⟨ connect-inc-left-fst-var s l′ ⟩
  < Var (fromℕ _) >tm ∎
  where
    open Reasoning tm-setoid

sub-between-connect-susps-fst-var : (σ : Sub (suc n) (suc l) ⋆)
                                  → (τ : Sub (suc m) (suc l′) ⋆)
                                  → Var (fromℕ _) [ sub-between-connect-susps σ τ ]tm ≃tm Var (fromℕ (l′ + (2 + l)))
sub-between-connect-susps-fst-var σ τ = sub-between-connects-fst-var (suspSub σ) getSnd τ getSnd (sym≃tm (susp-sub-preserve-getFst σ))

sub-between-connects-comp : (σ : Sub (suc n) (suc l) ⋆)
                          → (t : Tm (suc n))
                          → (τ : Sub (suc m) (suc l′) ⋆)
                          → (s : Tm (suc l))
                          → (σ′ : Sub (suc l) (suc n′) ⋆)
                          → (u : Tm (suc n′))
                          → (τ′ : Sub (suc l′) (suc m′) ⋆)
                          → s [ σ′ ]tm ≃tm u
                          → Var (fromℕ l′) [ τ′ ]tm ≃tm Var (fromℕ m′)
                          → sub-between-connects σ′ s τ′ u ∘ sub-between-connects σ t τ s
                          ≃s sub-between-connects (σ′ ∘ σ) t (τ′ ∘ τ) u
sub-between-connects-comp {l′ = l′} {m′ = m′} σ t ⟨ ⟨⟩ , x ⟩ s σ′ u τ′ p q = begin
  < sub-from-connect (connect-inc-left u m′ ∘ σ′) s (connect-inc-right u m′ ∘ τ′)
    ∘ (connect-inc-left s l′ ∘ σ) >s
    ≈˘⟨ ∘-assoc (sub-from-connect (connect-inc-left u m′ ∘ σ′) s
                  (connect-inc-right u m′ ∘ τ′)) (connect-inc-left s l′) σ ⟩
  < sub-from-connect (connect-inc-left u m′ ∘ σ′) s (connect-inc-right u m′ ∘ τ′)
    ∘ connect-inc-left s l′
    ∘ σ >s
    ≈⟨ sub-action-≃-sub refl≃s (sub-from-connect-inc-left (connect-inc-left u m′ ∘ σ′) s (connect-inc-right u m′ ∘ τ′)) ⟩
  < connect-inc-left u m′ ∘ σ′ ∘ σ >s
    ≈⟨ ∘-assoc (connect-inc-left u m′) σ′ σ ⟩
  < connect-inc-left u m′ ∘ (σ′ ∘ σ) >s ∎
  where
    open Reasoning sub-setoid
sub-between-connects-comp {l′ = l′} {m′ = m′} σ t ⟨ ⟨ τ , y ⟩ , x ⟩ s σ′ u τ′ p q = Ext≃ (sub-between-connects-comp σ t ⟨ τ , y ⟩ s σ′ u τ′ p q) (begin
  < x [ connect-inc-right s l′ ]tm
      [ sub-between-connects σ′ s τ′ u ]tm >tm
    ≈˘⟨ assoc-tm (sub-between-connects σ′ s τ′ u) (connect-inc-right s l′) x ⟩
  < x [ sub-between-connects σ′ s τ′ u ∘ connect-inc-right s l′ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = x}) (sub-between-connects-inc-right σ′ s τ′ u p q) ⟩
  < x [ connect-inc-right u m′ ∘ τ′ ]tm >tm
    ≈⟨ assoc-tm (connect-inc-right u m′) τ′ x ⟩
  < x [ τ′ ]tm [ connect-inc-right u m′ ]tm >tm ∎)
  where
    open Reasoning tm-setoid

sub-between-connect-susps-comp : (σ : Sub (suc n) (suc l) ⋆)
                               → (τ : Sub (suc m) (suc l′) ⋆)
                               → (σ′ : Sub (suc l) (suc n′) ⋆)
                               → (τ′ : Sub (suc l′) (suc m′) ⋆)
                               → Var (fromℕ l′) [ τ′ ]tm ≃tm Var (fromℕ m′)
                               → sub-between-connect-susps σ′ τ′ ∘ sub-between-connect-susps σ τ
                               ≃s sub-between-connect-susps (σ′ ∘ σ) (τ′ ∘ τ)
sub-between-connect-susps-comp σ τ σ′ τ′ p = trans≃s (sub-between-connects-comp (suspSub σ) getSnd τ getSnd (suspSub σ′) getSnd τ′ (sym≃tm (susp-sub-preserve-getSnd σ′)) p) (sub-between-connects-≃ (suspSub σ′ ∘ suspSub σ) getSnd (suspSub (σ′ ∘ σ)) getSnd (τ′ ∘ τ) getSnd (τ′ ∘ τ) getSnd refl refl (sym≃s (susp-functorial σ′ σ)) refl≃tm refl≃s refl≃tm)

connect-var-split-compat : (t : Tm (suc n)) → (m : ℕ) → VarSplitCompat (connect-inc-left t m) (connect-inc-right t m) (connect-var-split n m)
connect-var-split-compat t zero i = id-on-tm (Var i)
connect-var-split-compat t (suc m) zero = refl≃tm
connect-var-split-compat {n = n} t (suc m) (suc i) with connect-var-split n m i | connect-var-split-compat t m i
... | inj₁ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-left t m)) (lift-tm-≃ p)
... | inj₂ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-right t m)) (lift-tm-≃ p)

connect-var-split-right-compat : (t : Tm (suc n)) → .⦃ _ : isVar t ⦄ → (m : ℕ) → VarSplitCompat (connect-inc-left t m) (connect-inc-right t m) (connect-var-split-right t m)
connect-var-split-right-compat t zero i with toℕ (getVarFin t) ≟ toℕ i
... | no p = id-on-tm (Var i)
... | yes eq = trans≃tm (getVarFinProp t) (Var≃ refl eq)
connect-var-split-right-compat t (suc m) zero = refl≃tm
connect-var-split-right-compat t (suc m) (suc i) with connect-var-split-right t m i | connect-var-split-right-compat t m i
... | inj₁ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-left t m)) (lift-tm-≃ p)
... | inj₂ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-right t m)) (lift-tm-≃ p)

connect-inc-left-var-to-var : (t : Tm (suc n)) → (m : ℕ) → varToVar (connect-inc-left t m)
connect-inc-left-var-to-var {n = n} t zero = id-is-var-to-var (suc n)
connect-inc-left-var-to-var t (suc m) = liftSub-preserve-var-to-var (connect-inc-left t m) ⦃ connect-inc-left-var-to-var t m ⦄

connect-inc-right-var-to-var : (t : Tm (suc n)) → (m : ℕ) → .⦃ isVar t ⦄ → varToVar (connect-inc-right t m)
connect-inc-right-var-to-var t zero = extend-var-to-var ⟨⟩ t
connect-inc-right-var-to-var t (suc m) = liftSub-preserve-var-to-var (connect-inc-right t m) ⦃ connect-inc-right-var-to-var t m ⦄ ,, tt

connect-susp-inc-left-var-to-var : (n m : ℕ) → varToVar (connect-susp-inc-left n m)
connect-susp-inc-left-var-to-var n m = connect-inc-left-var-to-var getSnd m

connect-susp-inc-right-var-to-var : (n m : ℕ) → varToVar (connect-susp-inc-right n m)
connect-susp-inc-right-var-to-var n m = connect-inc-right-var-to-var getSnd m

connect-var-split-full : (t : Tm (suc n)) → (m : ℕ) → VarSplitFull₁ (connect-inc-left t m) ⦃ connect-inc-left-var-to-var t m ⦄ (connect-var-split n m)
connect-var-split-full t zero i = cong inj₁ (varToVarFunction-idSub (suc _) i)
connect-var-split-full {n} t (suc m) i = trans (cong (connect-var-split n (suc m)) (varToVarFunction-lift (connect-inc-left t m) ⦃ connect-inc-left-var-to-var t m ⦄ i)) lem
  where
    instance _ = connect-inc-left-var-to-var t m
    lem : connect-var-split n (suc m)
            (suc (varToVarFunction (connect-inc-left t m) i))
            ≡ inj₁ i
    lem with connect-var-split n m (varToVarFunction (connect-inc-left t m) i) | connect-var-split-full t m i
    ... | inj₁ x | refl = refl
    ... | inj₂ y | ()

connect-var-split-right-full : (t : Tm (suc n)) → .⦃ _ : isVar t ⦄ → (m : ℕ) → VarSplitFull₂ (connect-inc-right t m) ⦃ connect-inc-right-var-to-var t m ⦄ (connect-var-split-right t m)
connect-var-split-right-full (Var j) zero zero with toℕ j ≟ toℕ j
... | yes p = refl
... | no p = ⊥-elim (p refl)
connect-var-split-right-full (Var j) (suc m) zero = refl
connect-var-split-right-full (Var j) (suc m) (suc i) = trans (cong (connect-var-split-right (Var j) (suc m)) (varToVarFunction-lift (connect-inc-right (Var j) m) ⦃ connect-inc-right-var-to-var (Var j) m ⦄ i)) lem
  where
    instance _ = connect-inc-right-var-to-var (Var j) m
    lem : connect-var-split-right (Var j) (suc m)
            (suc (varToVarFunction (connect-inc-right (Var j) m) i))
            ≡ inj₂ (suc i)
    lem with connect-var-split-right (Var j) m (varToVarFunction (connect-inc-right (Var j) m) i) | connect-var-split-right-full (Var j) m i
    ... | inj₁ x | ()
    ... | inj₂ y | refl = refl
