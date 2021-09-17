{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection.Support where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Suspension
open import Data.Nat
open import Data.Vec
open import Data.Fin using (fromℕ;inject₁)
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Bool.Properties
open import Tactic.MonoidSolver
import Relation.Binary.Reasoning.Setoid as Reasoning

connect-supp : VarSet (suc n) → VarSet (suc m) → VarSet (suc (m + n))
connect-supp xs (x ∷ emp) = xs
connect-supp xs (x ∷ y ∷ ys) = x ∷ connect-supp xs (y ∷ ys)

connect-supp-incs : (xs : VarSet (suc n)) → (t : Tm (suc n)) → (ys : VarSet (suc m))
                  → xs ∪ FVTm t ≡ xs
                  → TransportVarSet xs (connect-inc-left t m) ∪ TransportVarSet ys (connect-inc-right t m) ≡ connect-supp xs ys
connect-supp-incs xs t (ewf emp) p = trans (∪-right-unit (TransportVarSet xs (idSub _))) (TransportVarSet-id xs)
connect-supp-incs xs t (ewt emp) p = trans (cong (TransportVarSet xs (idSub _) ∪_) (∪-left-unit (FVTm t))) (trans (cong (_∪ FVTm t) (TransportVarSet-id xs)) p)
connect-supp-incs xs t (ewf (y ∷ ys)) p = trans (cong₂ _∪_ (TransportVarSet-lift xs (connect-inc-left t _)) (TransportVarSet-lift (y ∷ ys) (connect-inc-right t _))) (cong ewf (connect-supp-incs xs t (y ∷ ys) p))
connect-supp-incs xs t (ewt (y ∷ ys)) p = trans (cong₂ (λ a b → a ∪ (b ∪ ewt empty)) (TransportVarSet-lift xs (connect-inc-left t _)) (TransportVarSet-lift (y ∷ ys) (connect-inc-right t _))) (cong ewt (trans (cong (TransportVarSet xs (connect-inc-left t _) ∪_) (∪-right-unit (TransportVarSet (y ∷ ys) (connect-inc-right t _)))) (connect-supp-incs xs t (y ∷ ys) p)))

connect-susp-supp-incs : (xs : VarSet (suc n)) → (ys : VarSet (suc m))
                      → TransportVarSet (suspSupp xs) (connect-susp-inc-left n m) ∪ TransportVarSet ys (connect-susp-inc-right n m) ≡ connect-supp (suspSupp xs) ys
connect-susp-supp-incs xs ys = connect-supp-incs (suspSupp xs) getSnd ys (suspSuppSnd xs)

sub-from-connect-supp : (σ : Sub (suc n) l) → (t : Tm (suc n)) → (τ : Sub (suc m) l)
                      → FVSub σ ≡ FVSub σ ∪ FVTm (Var (fromℕ _) [ τ ]tm)
                      → FVSub (sub-from-connect σ t τ) ≡ FVSub σ ∪ FVSub τ
sub-from-connect-supp {l = l} σ t ⟨ ⟨⟩ , x ⟩ p = trans p (solve (∪-monoid {l}))
sub-from-connect-supp {l = l} σ t ⟨ ⟨ τ , y ⟩ , x ⟩ p = trans (cong (_∪ FVTm x) (sub-from-connect-supp σ t ⟨ τ , y ⟩ p)) (solve (∪-monoid {l}))

sub-between-connect-supp : (σ : Sub (suc n) (suc l))
                         → (t : Tm (suc n))
                         → (τ : Sub (suc m) (suc l′))
                         → (s : Tm (suc l))
                         → FVSub (connect-inc-left s l′ ∘ σ) ≡ FVSub (connect-inc-left s l′ ∘ σ) ∪ FVTm (Var (fromℕ m) [ connect-inc-right s l′ ∘ τ ]tm)
                         → FVSub σ ∪ FVTm s ≡ FVSub σ
                         → FVSub (sub-between-connects σ t τ s) ≡ connect-supp (FVSub σ) (FVSub τ)
sub-between-connect-supp σ t τ s p q = begin
  FVSub (sub-from-connect (connect-inc-left s _ ∘ σ) t (connect-inc-right s _ ∘ τ))
    ≡⟨ sub-from-connect-supp (connect-inc-left s _ ∘ σ) t (connect-inc-right s _ ∘ τ) p ⟩
  FVSub (connect-inc-left s _ ∘ σ) ∪
    FVSub (connect-inc-right s _ ∘ τ)
    ≡˘⟨ cong₂ _∪_ (TransportVarSet-sub σ (connect-inc-left s _)) (TransportVarSet-sub τ (connect-inc-right s _)) ⟩
  TransportVarSet (FVSub σ) (connect-inc-left s _) ∪
    TransportVarSet (FVSub τ) (connect-inc-right s _)
    ≡⟨ connect-supp-incs (FVSub σ) s (FVSub τ) q ⟩
  connect-supp (FVSub σ) (FVSub τ) ∎
  where
    open ≡-Reasoning

sub-between-connect-susps-supp : (σ : Sub (suc n) (suc l))
                               → (τ : Sub (suc m) (suc l′))
                               → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                               → FVSub (sub-between-connect-susps σ τ) ≡ connect-supp (suspSupp (FVSub σ)) (FVSub τ)
sub-between-connect-susps-supp {n = n} {l = l} {m = m} {l′ = l′} σ τ p = trans (sub-between-connect-supp (suspSub σ) getSnd τ getSnd lem2 (trans (trans (cong (_∪ trueAt (inject₁ (fromℕ _))) (suspSuppSub σ)) (suspSuppSnd (FVSub σ))) (sym (suspSuppSub σ)))) (cong (λ - → connect-supp - (FVSub τ)) (suspSuppSub σ))
  where
    lem : Var (fromℕ m) [ connect-susp-inc-right l l′ ∘ τ ]tm ≃tm getSnd [ connect-susp-inc-left l l′ ]tm
    lem = begin
      < Var (fromℕ m) [ connect-susp-inc-right l l′ ∘ τ ]tm >tm
        ≈⟨ assoc-tm (connect-susp-inc-right l l′) τ (Var (fromℕ m)) ⟩
      < (Var (fromℕ m) [ τ ]tm) [ connect-susp-inc-right l l′ ]tm >tm
        ≈⟨ sub-action-≃-tm p refl≃s ⟩
      < Var (fromℕ l′) [ connect-susp-inc-right l l′ ]tm >tm
        ≈˘⟨ connect-inc-fst-var getSnd l′ ⟩
      < getSnd [ connect-susp-inc-left l l′ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    open ≡-Reasoning
    lem2 : FVSub (connect-susp-inc-left l l′ ∘ suspSub σ) ≡
             FVSub (connect-susp-inc-left l l′ ∘ suspSub σ) ∪
             FVTm (Var (fromℕ m) [ connect-inc-right getSnd l′ ∘ τ ]tm)
    lem2 = begin
      FVSub (connect-susp-inc-left l l′ ∘ suspSub σ)
        ≡˘⟨ TransportVarSet-sub (suspSub σ) (connect-susp-inc-left l l′) ⟩
      TransportVarSet (FVSub (suspSub σ)) (connect-susp-inc-left l l′)
        ≡⟨ cong (λ - → TransportVarSet - (connect-susp-inc-left l l′)) (trans (suspSuppSub σ) (sym (trans (cong (_∪ trueAt (inject₁ (fromℕ (suc l)))) (suspSuppSub σ)) (suspSuppSnd (FVSub σ))))) ⟩
      TransportVarSet (FVSub (suspSub σ) ∪ FVTm getSnd)
        (connect-susp-inc-left l l′)
        ≡⟨ TransportVarSet-∪ (FVSub (suspSub σ)) (FVTm getSnd) (connect-susp-inc-left l l′) ⟩
      TransportVarSet (FVSub (suspSub σ)) (connect-susp-inc-left l l′) ∪
        TransportVarSet (FVTm getSnd) (connect-susp-inc-left l l′)
        ≡⟨ cong₂ _∪_ (TransportVarSet-sub (suspSub σ) (connect-susp-inc-left l l′)) (TransportVarSet-tm getSnd (connect-susp-inc-left l l′)) ⟩
      FVSub (connect-susp-inc-left l l′ ∘ suspSub σ) ∪
        FVTm (getSnd [ connect-susp-inc-left l l′ ]tm)
        ≡˘⟨ cong (FVSub (connect-susp-inc-left l l′ ∘ suspSub σ) ∪_) (cong FVTm (≃tm-to-≡ lem)) ⟩
      FVSub (connect-susp-inc-left l l′ ∘ suspSub σ) ∪
        FVTm (Var (fromℕ m) [ connect-inc-right getSnd l′ ∘ τ ]tm) ∎
