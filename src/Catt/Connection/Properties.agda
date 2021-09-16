{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Connection
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles
open import Catt.Variables
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; T; if_then_else_; not)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary

connect-≃ : Γ ≃c Γ′ → t ≃tm t′ → Δ ≃c Δ′ → connect Γ t Δ ≃c connect Γ′ t′ Δ′
connect-inc-right-≃ : {t : Tm (suc n)} → {t′ : Tm (suc n′)} → n ≡ n′ → t ≃tm t′ → m ≡ m′ → connect-inc-right t m ≃s connect-inc-right t′ m′

connect-≃ p q (Add≃ Emp≃ r) = p
connect-≃ p q (Add≃ (Add≃ r s) t) = Add≃ (connect-≃ p q (Add≃ r s)) (sub-action-≃-ty t (connect-inc-right-≃ (cong pred (≃c-preserve-length p)) q (cong pred (≃c-preserve-length (Add≃ r s)))))

connect-inc-right-≃ {m = zero} refl q refl = Ext≃ (Null≃ refl) q
connect-inc-right-≃ {m = suc m} refl q refl = Ext≃ (lift-sub-≃ (connect-inc-right-≃ refl q refl)) (Var≃ refl refl)
-- Ext≃ (Null≃ p) q
--  Ext≃ (lift-sub-≃ (sub-action-≃-ty t (connect-inc-right-≃ p q (Add≃ r s))) (connect-inc-right-≃ p q (Add≃ r s))) (Var≃ (connect-≃ p q (Add≃ (Add≃ r s) t)) refl)

-- connect-is-non-empty : ⦃ _ : NonZero′ (ctxLength Γ) ⦄ ⦃ _ : NonZero′ (ctxLength Δ) ⦄ → NonZero′ (ctxLength (connect Γ t Δ))
-- connect-is-non-empty {Δ = ∅ , A} = it
-- connect-is-non-empty {Δ = Δ , A , B} = it

-- connect left unit

connect-left-unit : (Γ : Ctx (suc n)) → connect (∅ , ⋆) 0V Γ ≃c Γ
connect-inc-right-left-unit : (m : ℕ) → connect-inc-right 0V m ≃s idSub (suc m)

connect-left-unit (∅ , A) = Add≃ Emp≃ (sym≃ty (⋆-is-only-ty-in-empty-context A))
connect-left-unit (Γ , A , B) = Add≃ (connect-left-unit (Γ , A)) (trans≃ty (sub-action-≃-ty refl≃ty (connect-inc-right-left-unit _)) (id-on-ty B))

connect-inc-right-left-unit zero = refl≃s
connect-inc-right-left-unit (suc m) = Ext≃ (lift-sub-≃ (connect-inc-right-left-unit m)) (Var≃ (cong suc (cong suc (+-identityʳ m))) refl)

connect-pdb-left-unit : (Γ : Ctx (suc n)) → connect-pdb Base Γ ≃c Γ
connect-pdb-left-unit Γ = connect-left-unit Γ

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

connect-pdb-assoc : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ]) → (Υ : Ctx (suc l)) → connect-pdb (connect-pdb-pdb pdb pdb2) Υ ≃c connect-pdb pdb (connect-pdb pdb2 Υ)
connect-pdb-assoc {Γ = Γ} {Δ = Δ} pdb pdb2 Υ = trans≃c (connect-≃ (refl≃c {Γ = connect Γ (getFocusTerm pdb) Δ}) (sym≃tm (connect-pdb-foc-tm pdb pdb2)) (refl≃c {Γ = Υ})) (connect-assoc _ (getFocusTerm pdb) _ (getFocusTerm pdb2) Υ)

connect-pd-assoc : (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → (Υ : Ctx (suc l)) → connect-pd (connect-pd-pd pd pd2) Υ ≃c connect-pd pd (connect-pd pd2 Υ)
connect-pd-assoc (Finish pdb) (Finish pdb2) = connect-pdb-assoc pdb pdb2

sub-from-connect-inc-left : (σ : Sub (suc n) l) → (t : Tm (suc n)) → (τ : Sub (suc m) l) → sub-from-connect σ t τ ∘ connect-inc-left t m ≃s σ
sub-from-connect-inc-left σ t τ@(⟨ ⟨⟩ , s ⟩) = id-right-unit (sub-from-connect σ t τ)
sub-from-connect-inc-left σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = trans≃s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-left t _)) (sub-from-connect-inc-left σ t ⟨ τ , s ⟩)

sub-from-connect-pdb-inc-left : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → sub-from-connect-pdb pdb σ τ ∘ connect-pdb-inc-left pdb m ≃s σ
sub-from-connect-pdb-inc-left pdb σ τ = sub-from-connect-inc-left σ (getFocusTerm pdb) τ

sub-from-connect-pd-inc-left : (pd : Γ ⊢pd₀ d) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → sub-from-connect-pd pd σ τ ∘ connect-pd-inc-left pd m ≃s σ
sub-from-connect-pd-inc-left (Finish pdb) σ τ = sub-from-connect-pdb-inc-left pdb σ τ

sub-from-connect-inc-right : (σ : Sub (suc n) l) → (t : Tm (suc n)) → (τ : Sub (suc m) l) → (t [ σ ]tm ≃tm Var (fromℕ _) [ τ ]tm) → sub-from-connect σ t τ ∘ connect-inc-right t m ≃s τ
sub-from-connect-inc-right σ t ⟨ ⟨⟩ , s ⟩ p = Ext≃ (Null≃ refl) p
sub-from-connect-inc-right σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≃ (trans≃s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-right t _)) (sub-from-connect-inc-right σ t ⟨ τ , s ⟩ p)) refl≃tm

sub-from-connect-pdb-inc-right : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → (getFocusTerm pdb [ σ ]tm ≃tm (Var (fromℕ _) [ τ ]tm)) → sub-from-connect-pdb pdb σ τ ∘ connect-pdb-inc-right pdb m ≃s τ
sub-from-connect-pdb-inc-right pdb σ τ p = sub-from-connect-inc-right σ (getFocusTerm pdb) τ p

sub-from-connect-pd-inc-right : (pd : Γ ⊢pd₀ d) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → (pd-focus-tm pd [ σ ]tm ≃tm (Var (fromℕ _) [ τ ]tm)) → sub-from-connect-pd pd σ τ ∘ connect-pd-inc-right pd m ≃s τ
sub-from-connect-pd-inc-right (Finish pdb) σ τ p = sub-from-connect-pdb-inc-right pdb σ τ p

sub-between-connects-inc-left : (σ : Sub (suc n) (suc l))
                              → (t : Tm (suc n))
                              → (τ : Sub (suc m) (suc l′))
                              → (s : Tm (suc l))
                              → sub-between-connects σ t τ s ∘ connect-inc-left t m
                              ≃s connect-inc-left s l′ ∘ σ
sub-between-connects-inc-left {l′ = l′} σ t τ s = sub-from-connect-inc-left (connect-inc-left s l′ ∘ σ) t (connect-inc-right s l′ ∘ τ)

sub-between-connect-pdbs-inc-left : {Γ : Ctx (suc n)}
                                 → (pdb : Γ ⊢pd[ submax ][ 0 ])
                                 → {Δ : Ctx (suc l)}
                                 → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ])
                                 → (σ : Sub (suc n) (suc l))
                                 → (τ : Sub (suc m) (suc l′))
                                 → sub-between-connect-pdbs pdb pdb2 σ τ ∘ connect-pdb-inc-left pdb m
                                 ≃s connect-pdb-inc-left pdb2 l′ ∘ σ
sub-between-connect-pdbs-inc-left pdb pdb2 σ τ = sub-between-connects-inc-left σ (getFocusTerm pdb) τ (getFocusTerm pdb2)

sub-between-connect-pds-inc-left : {Γ : Ctx (suc n)}
                                 → (pd : Γ ⊢pd₀ d)
                                 → {Δ : Ctx (suc l)}
                                 → (pd2 : Δ ⊢pd₀ d′)
                                 → (σ : Sub (suc n) (suc l))
                                 → (τ : Sub (suc m) (suc l′))
                                 → sub-between-connect-pds pd pd2 σ τ ∘ connect-pd-inc-left pd m
                                 ≃s connect-pd-inc-left pd2 l′ ∘ σ
sub-between-connect-pds-inc-left (Finish pdb) (Finish pdb2) = sub-between-connect-pdbs-inc-left pdb pdb2

connect-inc-fst-var : (t : Tm (suc n)) → (m : ℕ) → t [ connect-inc-left t m ]tm ≃tm Var (fromℕ _) [ connect-inc-right t m ]tm
connect-inc-fst-var t zero = id-on-tm t
connect-inc-fst-var t (suc m) = begin
  < t [ connect-inc-left t (suc m) ]tm >tm ≈⟨ apply-lifted-sub-tm-≃ t (connect-inc-left t m) ⟩
  < liftTerm (t [ connect-inc-left t m ]tm) >tm ≈⟨ lift-tm-≃ (connect-inc-fst-var t m) ⟩
  < liftTerm (Var (fromℕ _) [ connect-inc-right t m ]tm) >tm ≈˘⟨ apply-lifted-sub-tm-≃ (Var (fromℕ _)) (connect-inc-right t m) ⟩
  < Var (fromℕ (suc _)) [ connect-inc-right t (suc m) ]tm >tm ∎
  where
    open Reasoning tm-setoid

connect-pdb-inc-fst-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → (getFocusTerm pdb) [ connect-pdb-inc-left pdb m ]tm ≃tm Var (fromℕ _) [ connect-pdb-inc-right pdb m ]tm
connect-pdb-inc-fst-var pdb = connect-inc-fst-var (getFocusTerm pdb)

connect-pd-inc-fst-var : (pd : Γ ⊢pd₀ d) → (m : ℕ)
  → pd-focus-tm pd [ connect-pd-inc-left pd m ]tm ≃tm Var (fromℕ _) [ connect-pd-inc-right pd m ]tm
connect-pd-inc-fst-var (Finish pdb) = connect-pdb-inc-fst-var pdb

sub-between-connects-inc-right : (σ : Sub (suc n) (suc l))
                               → (t : Tm (suc n))
                               → (τ : Sub (suc m) (suc l′))
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

sub-between-connect-pdbs-inc-right : {Γ : Ctx (suc n)}
                                   → (pdb : Γ ⊢pd[ submax ][ 0 ])
                                   → {Δ : Ctx (suc l)}
                                   → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ])
                                   → (σ : Sub (suc n) (suc l))
                                   → (τ : Sub (suc m) (suc l′))
                                   → getFocusTerm pdb [ σ ]tm ≃tm getFocusTerm pdb2
                                   → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                                   → sub-between-connect-pdbs pdb pdb2 σ τ ∘ connect-pdb-inc-right pdb m
                                   ≃s connect-pdb-inc-right pdb2 l′ ∘ τ
sub-between-connect-pdbs-inc-right pdb pdb2 σ τ = sub-between-connects-inc-right σ (getFocusTerm pdb) τ (getFocusTerm pdb2)

sub-between-connect-pds-inc-right : {Γ : Ctx (suc n)}
                                   → (pd : Γ ⊢pd₀ d)
                                   → {Δ : Ctx (suc l)}
                                   → (pd2 : Δ ⊢pd₀ d′)
                                   → (σ : Sub (suc n) (suc l))
                                   → (τ : Sub (suc m) (suc l′))
                                   → pd-focus-tm pd [ σ ]tm ≃tm pd-focus-tm pd2
                                   → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                                   → sub-between-connect-pds pd pd2 σ τ ∘ connect-pd-inc-right pd m
                                   ≃s connect-pd-inc-right pd2 l′ ∘ τ
sub-between-connect-pds-inc-right (Finish pdb) (Finish pdb2) = sub-between-connect-pdbs-inc-right pdb pdb2

connect-inc-left-fst-var : (t : Tm (suc n)) → (m : ℕ) → Var (fromℕ _) [ connect-inc-left t m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
connect-inc-left-fst-var t zero = id-on-tm (Var (fromℕ _))
connect-inc-left-fst-var t (suc m) = trans≃tm (apply-lifted-sub-tm-≃ (Var (fromℕ _)) (connect-inc-left t m)) (lift-tm-≃ (connect-inc-left-fst-var t m))

connect-pdb-inc-left-fst-var : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → Var (fromℕ _) [ connect-pdb-inc-left pdb m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
connect-pdb-inc-left-fst-var pdb = connect-inc-left-fst-var (getFocusTerm pdb)

connect-pd-inc-left-fst-var : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (m : ℕ) → Var (fromℕ _) [ connect-pd-inc-left pd m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
connect-pd-inc-left-fst-var (Finish pdb) = connect-pdb-inc-left-fst-var pdb

sub-from-connect-fst-var : (σ : Sub (suc n) l) → (t : Tm (suc n)) → (τ : Sub (suc m) l) → Var (fromℕ _) [ sub-from-connect σ t τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-fst-var σ t ⟨ ⟨⟩ , s ⟩ = refl≃tm
sub-from-connect-fst-var σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = sub-from-connect-fst-var σ t ⟨ τ , s ⟩

sub-from-connect-pdb-fst-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → Var (fromℕ _) [ sub-from-connect-pdb pdb σ τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-pdb-fst-var pdb σ τ = sub-from-connect-fst-var σ (getFocusTerm pdb) τ

sub-from-connect-pd-fst-var : (pd : Γ ⊢pd₀ d) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) →
  Var (fromℕ _) [ sub-from-connect-pd pd σ τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-pd-fst-var (Finish pdb) σ τ = sub-from-connect-pdb-fst-var pdb σ τ

sub-between-connects-fst-var : (σ : Sub (suc n) (suc l))
                             → (t : Tm (suc n))
                             → (τ : Sub (suc m) (suc l′))
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

sub-between-connect-pdbs-fst-var : {Γ : Ctx (suc n)}
                                 → (pdb : Γ ⊢pd[ submax ][ 0 ])
                                 → {Δ : Ctx (suc l)}
                                 → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ])
                                 → (σ : Sub (suc n) (suc l))
                                 → (τ : Sub (suc m) (suc l′))
                                 → Var (fromℕ _) [ σ ]tm ≃tm Var (fromℕ l)
                                 → Var (fromℕ _) [ sub-between-connect-pdbs pdb pdb2 σ τ ]tm ≃tm Var (fromℕ (l′ + l))
sub-between-connect-pdbs-fst-var pdb pdb2 σ τ = sub-between-connects-fst-var σ (getFocusTerm pdb) τ (getFocusTerm pdb2)

sub-between-connect-pds-fst-var : {Γ : Ctx (suc n)}
                                 → (pd : Γ ⊢pd₀ d)
                                 → {Δ : Ctx (suc l)}
                                 → (pd2 : Δ ⊢pd₀ d′)
                                 → (σ : Sub (suc n) (suc l))
                                 → (τ : Sub (suc m) (suc l′))
                                 → Var (fromℕ _) [ σ ]tm ≃tm Var (fromℕ l)
                                 → Var (fromℕ _) [ sub-between-connect-pds pd pd2 σ τ ]tm ≃tm Var (fromℕ (l′ + l))
sub-between-connect-pds-fst-var (Finish pdb) (Finish pdb2) = sub-between-connect-pdbs-fst-var pdb pdb2

sub-between-connects-comp : (σ : Sub (suc n) (suc l))
                          → (t : Tm (suc n))
                          → (τ : Sub (suc m) (suc l′))
                          → (s : Tm (suc l))
                          → (σ′ : Sub (suc l) (suc n′))
                          → (u : Tm (suc n′))
                          → (τ′ : Sub (suc l′) (suc m′))
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

sub-between-connect-pdbs-comp : {Γ : Ctx (suc n)}
                              → (pdb : Γ ⊢pd[ submax ][ 0 ])
                              → {Δ : Ctx (suc l)}
                              → (pdb2 : Δ ⊢pd[ submax′ ][ 0 ])
                              → {Υ : Ctx (suc n′)}
                              → (pdb3 : Υ ⊢pd[ submax″ ][ 0 ])
                              → (σ : Sub (suc n) (suc l))
                              → (τ : Sub (suc m) (suc l′))
                              → (σ′ : Sub (suc l) (suc n′))
                              → (τ′ : Sub (suc l′) (suc m′))
                              → getFocusTerm pdb2 [ σ′ ]tm ≃tm getFocusTerm pdb3
                              → Var (fromℕ l′) [ τ′ ]tm ≃tm Var (fromℕ m′)
                              → sub-between-connect-pdbs pdb2 pdb3 σ′ τ′ ∘ sub-between-connect-pdbs pdb pdb2 σ τ
                              ≃s sub-between-connect-pdbs pdb pdb3 (σ′ ∘ σ) (τ′ ∘ τ)
sub-between-connect-pdbs-comp pdb pdb2 pdb3 σ τ σ′ τ′ = sub-between-connects-comp σ (getFocusTerm pdb) τ (getFocusTerm pdb2) σ′ (getFocusTerm pdb3) τ′

sub-between-connect-pds-comp : {Γ : Ctx (suc n)}
                              → (pd : Γ ⊢pd₀ d)
                              → {Δ : Ctx (suc l)}
                              → (pd2 : Δ ⊢pd₀ d′)
                              → {Υ : Ctx (suc n′)}
                              → (pd3 : Υ ⊢pd₀ d″)
                              → (σ : Sub (suc n) (suc l))
                              → (τ : Sub (suc m) (suc l′))
                              → (σ′ : Sub (suc l) (suc n′))
                              → (τ′ : Sub (suc l′) (suc m′))
                              → pd-focus-tm pd2 [ σ′ ]tm ≃tm pd-focus-tm pd3
                              → Var (fromℕ l′) [ τ′ ]tm ≃tm Var (fromℕ m′)
                              → sub-between-connect-pds pd2 pd3 σ′ τ′ ∘ sub-between-connect-pds pd pd2 σ τ
                              ≃s sub-between-connect-pds pd pd3 (σ′ ∘ σ) (τ′ ∘ τ)
sub-between-connect-pds-comp (Finish pdb) (Finish pdb2) (Finish pdb3) = sub-between-connect-pdbs-comp pdb pdb2 pdb3

connect-var-split : (t : Tm (suc n)) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-var-split t zero i = inj₁ i
connect-var-split t (suc m) zero = inj₂ zero
connect-var-split t (suc m) (suc i) with connect-var-split t m i
... | inj₁ j = inj₁ j
... | inj₂ j = inj₂ (suc j)

connect-var-split-compat : (t : Tm (suc n)) → (m : ℕ) → VarSplitCompat (connect-inc-left t m) (connect-inc-right t m) (connect-var-split t m)
connect-var-split-compat t zero i = id-on-tm (Var i)
connect-var-split-compat t (suc m) zero = refl≃tm
connect-var-split-compat t (suc m) (suc i) with connect-var-split t m i | connect-var-split-compat t m i
... | inj₁ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-left t m)) (lift-tm-≃ p)
... | inj₂ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-right t m)) (lift-tm-≃ p)

connect-pdb-var-split : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-pdb-var-split pdb = connect-var-split (getFocusTerm pdb)

connect-pdb-var-split-compat : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → VarSplitCompat (connect-pdb-inc-left pdb m) (connect-pdb-inc-right pdb m) (connect-pdb-var-split pdb m)
connect-pdb-var-split-compat pdb = connect-var-split-compat (getFocusTerm pdb)

connect-pd-var-split : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-pd-var-split (Finish pdb) Δ = connect-pdb-var-split pdb Δ

connect-pd-var-split-compat : (pd : Γ ⊢pd₀ d) → (m : ℕ) → VarSplitCompat (connect-pd-inc-left pd m) (connect-pd-inc-right pd m) (connect-pd-var-split pd m)
connect-pd-var-split-compat (Finish pdb) = connect-pdb-var-split-compat pdb

connect-var-split-right : (t : Tm (suc n)) → .⦃ isVar t ⦄ → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-var-split-right t zero i with toℕ (getVarFin t) ≡ᵇ toℕ i
... | true = inj₂ zero
... | false = inj₁ i
connect-var-split-right t (suc m) zero = inj₂ zero
connect-var-split-right t (suc m) (suc i) with connect-var-split-right t m i
... | inj₁ j = inj₁ j
... | inj₂ j = inj₂ (suc j)

-- record Reveal_·_is-bool_ {A : Set}
--                     (f : (x : A) → Bool) (x : A) (y : Bool):
--                     Set where
--   constructor [_]
--   field eq : if y then T (f x) else T (not (f x))

-- inspect-bool : ∀ {A : Set} (f : (x : A) → Bool) (x : A) → Reveal f · x is-bool f x
-- inspect-bool f x with f x | inspect f x
-- ... | false | [ eq ] = [ subst (λ - → T (not -)) (sym eq) tt ]
-- ... | true | [ eq ] = [ subst T (sym eq) tt ]

connect-var-split-right-compat : (t : Tm (suc n)) → .⦃ _ : isVar t ⦄ → (m : ℕ) → VarSplitCompat (connect-inc-left t m) (connect-inc-right t m) (connect-var-split-right t m)
connect-var-split-right-compat t zero i with toℕ (getVarFin t) ≡ᵇ toℕ i | inspect (λ i → toℕ (getVarFin t) ≡ᵇ toℕ i) i
... | false | p = id-on-tm (Var i)
... | true | [ eq ] = trans≃tm (getVarFinProp t) (Var≃ refl (≡ᵇ⇒≡ (toℕ (getVarFin t)) (toℕ i) (subst T (sym eq) tt)))
connect-var-split-right-compat t (suc m) zero = refl≃tm
connect-var-split-right-compat t (suc m) (suc i) with connect-var-split-right t m i | connect-var-split-right-compat t m i
... | inj₁ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-left t m)) (lift-tm-≃ p)
... | inj₂ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-right t m)) (lift-tm-≃ p)

connect-pdb-var-split-right : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-pdb-var-split-right pdb = connect-var-split-right (getFocusTerm pdb) ⦃ focus-term-is-var pdb ⦄

connect-pdb-var-split-right-compat : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → VarSplitCompat (connect-pdb-inc-left pdb m) (connect-pdb-inc-right pdb m) (connect-pdb-var-split-right pdb m)
connect-pdb-var-split-right-compat pdb = connect-var-split-right-compat (getFocusTerm pdb) ⦃ focus-term-is-var pdb ⦄

connect-pd-var-split-right : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-pd-var-split-right (Finish pdb) = connect-pdb-var-split-right pdb

connect-pd-var-split-right-compat : (pd : Γ ⊢pd₀ d) → (m : ℕ) → VarSplitCompat (connect-pd-inc-left pd m) (connect-pd-inc-right pd m) (connect-pd-var-split-right pd m)
connect-pd-var-split-right-compat (Finish pdb) = connect-pdb-var-split-right-compat pdb

-- connect-var-split : (Γ : Ctx (suc n)) → (t : Tm Γ 2) → (Δ : Ctx (suc m)) → VarSplit (connect Γ t Δ) (connect-inc-left Γ t Δ) (connect-inc-right Γ t Δ)
-- connect-var-split Γ t (∅ , A) i = inj₁ (i ,, id-on-tm (Var i))
-- connect-var-split Γ t (Δ , A , B) zero = inj₂ (zero ,, Var≃ refl)
-- connect-var-split Γ t (Δ , A , B) (suc i) with connect-var-split Γ t (Δ , A) i
-- ... | inj₁ (j ,, p) = inj₁ (j ,, trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-left Γ t (Δ , A))) (lift-tm-≃ p))
-- ... | inj₂ (j ,, p) = inj₂ (suc j ,, trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-right Γ t (Δ , A))) (lift-tm-≃ p))

-- connect-pdb-var-split : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → VarSplit (connect-pdb pdb Δ) (connect-pdb-inc-left pdb Δ) (connect-pdb-inc-right pdb Δ)
-- connect-pdb-var-split pdb Δ = connect-var-split _ (getFocusTerm pdb) Δ

connect-inc-left-var-to-var : (t : Tm (suc n)) → (m : ℕ) → varToVar (connect-inc-left t m)
connect-inc-left-var-to-var {n = n} t zero = id-is-var-to-var (suc n)
connect-inc-left-var-to-var t (suc m) = liftSub-preserve-var-to-var (connect-inc-left t m) ⦃ connect-inc-left-var-to-var t m ⦄

connect-pdb-inc-left-var-to-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → varToVar (connect-pdb-inc-left pdb m)
connect-pdb-inc-left-var-to-var pdb = connect-inc-left-var-to-var (getFocusTerm pdb)

connect-pd-inc-left-var-to-var : (pd : Γ ⊢pd₀ d) → (m : ℕ) → varToVar (connect-pd-inc-left pd m)
connect-pd-inc-left-var-to-var (Finish pdb) = connect-pdb-inc-left-var-to-var pdb

connect-inc-right-var-to-var : (t : Tm (suc n)) → (m : ℕ) → .⦃ isVar t ⦄ → varToVar (connect-inc-right t m)
connect-inc-right-var-to-var t zero = extend-var-to-var ⟨⟩ t
connect-inc-right-var-to-var t (suc m) = liftSub-preserve-var-to-var (connect-inc-right t m) ⦃ connect-inc-right-var-to-var t m ⦄

connect-pdb-inc-right-var-to-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → varToVar (connect-pdb-inc-right pdb m)
connect-pdb-inc-right-var-to-var pdb m = connect-inc-right-var-to-var (getFocusTerm pdb) m ⦃ focus-term-is-var pdb ⦄

connect-pd-inc-right-var-to-var : (pd : Γ ⊢pd₀ d) → (m : ℕ) → varToVar (connect-pd-inc-right pd m)
connect-pd-inc-right-var-to-var (Finish pdb) = connect-pdb-inc-right-var-to-var pdb

{-
ty-dim-≥-1 : Ty Γ d → d ≥ 1
ty-dim-≥-1 ⋆ = ≤-refl
ty-dim-≥-1 (s ─⟨ A ⟩⟶ t) = s≤s z≤n

non-empty-context-dim-≥-1 : (Γ : Ctx (suc n)) → ctx-dim Γ ≥ 1
non-empty-context-dim-≥-1 (Γ , A) = m≤n⇒m≤o⊔n (ctx-dim Γ) (ty-dim-≥-1 A)

connect-ctx-dim : (Γ : Ctx (suc n)) → (t : Tm Γ 2) → (Δ : Ctx (suc m)) → ctx-dim (connect Γ t Δ) ≡ ctx-dim Γ ⊔ ctx-dim Δ
connect-ctx-dim Γ t (∅ , ⋆) = sym (m≥n⇒m⊔n≡m (non-empty-context-dim-≥-1 Γ))
connect-ctx-dim Γ t (∅ , s ─⟨ A ⟩⟶ t₁) = ⊥-elim (no-term-in-empty-context s)
connect-ctx-dim Γ t (Δ , A , B) = begin
  ctx-dim (connect Γ t (Δ , A , B)) ≡⟨⟩
  ctx-dim (connect Γ t (Δ , A)) ⊔
      ty-dim (B [ connect-inc-right Γ t (Δ , A) ]ty) ≡⟨ cong (_⊔ ty-dim B) (connect-ctx-dim Γ t (Δ , A)) ⟩
  (ctx-dim Γ ⊔ ctx-dim (Δ , A)) ⊔ ty-dim B ≡⟨ ⊔-assoc (ctx-dim Γ) (ctx-dim (Δ , A)) (ty-dim B) ⟩
  ctx-dim Γ ⊔ (ctx-dim (Δ , A) ⊔ ty-dim B) ≡⟨⟩
  ctx-dim Γ ⊔ ctx-dim (Δ , A , B) ∎
  where
    open ≡-Reasoning

connect-pdb-ctx-dim : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → ctx-dim (connect-pdb pdb Δ) ≡ ctx-dim Γ ⊔ ctx-dim Δ
connect-pdb-ctx-dim pdb Δ = connect-ctx-dim _ (getFocusTerm pdb) Δ
-}
