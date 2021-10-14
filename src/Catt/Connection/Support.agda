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
open import Data.Bool renaming (T to Truth)
open import Data.Bool.Properties
open import Tactic.MonoidSolver
import Relation.Binary.Reasoning.Setoid as Reasoning
import Relation.Binary.Reasoning.PartialOrder as PReasoning
open import Catt.Variables
open import Catt.Tree
open import Data.Unit using (tt)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using (Pointwise; Pointwise-≡⇒≡)

connect-supp-full : ∀ n m → connect-supp {n} {m} full full ≡ full
connect-supp-full n zero = refl
connect-supp-full n (suc m) = cong ewt (connect-supp-full n m)

connect-supp-incs : (xs : VarSet (suc n)) → (t : Tm (suc n)) → (ys : VarSet (suc m))
                  → FVTm t ⊆ xs
                  → TransportVarSet xs (connect-inc-left t m) ∪ TransportVarSet ys (connect-inc-right t m) ≡ connect-supp xs ys
connect-supp-incs xs t (ewf emp) p = trans (∪-right-unit (TransportVarSet xs (idSub _))) (TransportVarSet-id xs)
connect-supp-incs xs t (ewt emp) p = trans (cong (TransportVarSet xs (idSub _) ∪_) (∪-left-unit (FVTm t))) (trans (cong (_∪ FVTm t) (TransportVarSet-id xs)) (sym p))
connect-supp-incs xs t (ewf (y ∷ ys)) p = trans (cong₂ _∪_ (TransportVarSet-lift xs (connect-inc-left t _)) (TransportVarSet-lift (y ∷ ys) (connect-inc-right t _))) (cong ewf (connect-supp-incs xs t (y ∷ ys) p))
connect-supp-incs xs t (ewt (y ∷ ys)) p = trans (cong₂ (λ a b → a ∪ (b ∪ ewt empty)) (TransportVarSet-lift xs (connect-inc-left t _)) (TransportVarSet-lift (y ∷ ys) (connect-inc-right t _))) (cong ewt (trans (cong (TransportVarSet xs (connect-inc-left t _) ∪_) (∪-right-unit (TransportVarSet (y ∷ ys) (connect-inc-right t _)))) (connect-supp-incs xs t (y ∷ ys) p)))

connect-susp-supp-incs : (xs : VarSet (suc n)) → (ys : VarSet (suc m))
                      → TransportVarSet (suspSupp xs) (connect-susp-inc-left n m) ∪ TransportVarSet ys (connect-susp-inc-right n m) ≡ connect-supp (suspSupp xs) ys
connect-susp-supp-incs xs ys = connect-supp-incs (suspSupp xs) getSnd ys (suspSuppSnd xs)

sub-from-connect-supp : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A)
                      → FVTm (Var (fromℕ _) [ τ ]tm) ⊆ FVSub σ
                      → FVSub (sub-from-connect σ τ) ≡ FVSub σ ∪ FVSub τ
sub-from-connect-supp {l = l} {A = A} σ ⟨ ⟨⟩ , x ⟩ p = begin
  FVSub σ
    ≡⟨ p ⟩
  FVSub σ ∪ FVTm x
    ≡⟨ cong (_∪ FVTm x) (sub-type-⊆ σ) ⟩
  FVSub σ ∪ FVTy A ∪ FVTm x
    ≡⟨ ∪-assoc (FVSub σ) (FVTy A) (FVTm x) ⟩
  FVSub σ ∪ (FVTy A ∪ FVTm x) ∎
  where
    open ≡-Reasoning
sub-from-connect-supp {l = l} σ ⟨ ⟨ τ , y ⟩ , x ⟩ p = trans (cong (_∪ FVTm x) (sub-from-connect-supp σ ⟨ τ , y ⟩ p)) (solve (∪-monoid {l}))

sub-from-connect-Transport : (σ : Sub (suc n) l ⋆)
                           → (τ : Sub (suc m) l ⋆)
                           → (xs : VarSet (suc n))
                           → (ys : VarSet (suc m))
                           → (t : Tm (suc n))
                           → .⦃ _ : isVar t ⦄
                           → (Var (fromℕ _) [ τ ]tm ≃tm t [ σ ]tm)
                           → Truth (lookup-isVar xs t)
                           → TransportVarSet (connect-supp xs ys) (sub-from-connect σ τ) ≡ (TransportVarSet xs σ) ∪ (TransportVarSet ys τ)
sub-from-connect-Transport σ ⟨ ⟨⟩ , t ⟩ xs (ewf emp) s p q = sym (∪-right-unit (TransportVarSet xs σ))
sub-from-connect-Transport σ ⟨ ⟨⟩ , t ⟩ xs (ewt emp) s p q = begin
  empty ∪ FVTm t ≡⟨ ∪-left-unit (FVTm t) ⟩
  FVTm t ≡⟨ cong FVTm (≃tm-to-≡ p) ⟩
  FVTm (s [ σ ]tm) ≡˘⟨ TransportVarSet-tm s σ ⟩
  TransportVarSet (FVTm s) σ ≤⟨ ⊆-TransportVarSet σ (lookup-isVar-⊆ xs s q) ⟩
  TransportVarSet xs σ ∎
  where
    open PReasoning (⊆-poset _)
sub-from-connect-Transport σ ⟨ ⟨ τ , s ⟩ , t ⟩ xs (ewf (y ∷ ys)) u p q = sub-from-connect-Transport σ ⟨ τ , s ⟩ xs (y ∷ ys) u p q
sub-from-connect-Transport σ ⟨ ⟨ τ , s ⟩ , t ⟩ xs (ewt (y ∷ ys)) u p q = trans (cong (_∪ FVTm t) (sub-from-connect-Transport σ ⟨ τ , s ⟩ xs (y ∷ ys) u p q)) (∪-assoc (TransportVarSet xs σ) (TransportVarSet (y ∷ ys) ⟨ τ , s ⟩) (FVTm t))

sub-between-connect-supp : (σ : Sub (suc n) (suc l) ⋆)
                         → (τ : Sub (suc m) (suc l′) ⋆)
                         → (s : Tm (suc l))
                         → FVSub (connect-inc-left s l′ ∘ σ) ≡ FVSub (connect-inc-left s l′ ∘ σ) ∪ FVTm (Var (fromℕ m) [ connect-inc-right s l′ ∘ τ ]tm)
                         → FVTm s ⊆ FVSub σ
                         → FVSub (sub-between-connects σ τ s) ≡ connect-supp (FVSub σ) (FVSub τ)
sub-between-connect-supp σ τ s p q = begin
  FVSub (sub-from-connect (connect-inc-left s _ ∘ σ) (connect-inc-right s _ ∘ τ))
    ≡⟨ sub-from-connect-supp (connect-inc-left s _ ∘ σ) (connect-inc-right s _ ∘ τ) p ⟩
  FVSub (connect-inc-left s _ ∘ σ) ∪
    FVSub (connect-inc-right s _ ∘ τ)
    ≡˘⟨ cong₂ _∪_ (TransportVarSet-sub σ (connect-inc-left s _)) (TransportVarSet-sub τ (connect-inc-right s _)) ⟩
  TransportVarSet (FVSub σ) (connect-inc-left s _) ∪
    TransportVarSet (FVSub τ) (connect-inc-right s _)
    ≡⟨ connect-supp-incs (FVSub σ) s (FVSub τ) q ⟩
  connect-supp (FVSub σ) (FVSub τ) ∎
  where
    open ≡-Reasoning

sub-between-connect-Transport : (σ : Sub (suc n) (suc l) ⋆)
                              → (τ : Sub (suc m) (suc l′) ⋆)
                              → (s : Tm (suc l))
                              → (xs : VarSet (suc n))
                              → (ys : VarSet (suc m))
                              → (t : Tm (suc n))
                              → .⦃ _ : isVar t ⦄
                              → Var (fromℕ _) [ connect-inc-right s l′ ∘ τ ]tm ≃tm t [ connect-inc-left s l′ ∘ σ ]tm
                              → Truth (lookup-isVar xs t)
                              → FVTm s ⊆ TransportVarSet xs σ
                              → TransportVarSet (connect-supp xs ys) (sub-between-connects σ τ s)
                              ≡ connect-supp (TransportVarSet xs σ) (TransportVarSet ys τ)
sub-between-connect-Transport {l = l} {l′ = l′} σ τ s xs ys t p q r = begin
  TransportVarSet (connect-supp xs ys) (sub-between-connects σ τ s)
    ≡⟨ sub-from-connect-Transport (connect-inc-left s l′ ∘ σ) (connect-inc-right s l′ ∘ τ) xs ys t p q ⟩
  TransportVarSet xs (connect-inc-left s l′ ∘ σ)
  ∪ TransportVarSet ys (connect-inc-right s l′ ∘ τ)
    ≡⟨ cong₂ _∪_ (TransportVarSet-comp xs (connect-inc-left s l′) σ) (TransportVarSet-comp ys (connect-inc-right s l′) τ) ⟩
  TransportVarSet (TransportVarSet xs σ) (connect-inc-left s l′)
  ∪ TransportVarSet (TransportVarSet ys τ) (connect-inc-right s l′)
    ≡⟨ connect-supp-incs (TransportVarSet xs σ) s (TransportVarSet ys τ) r ⟩
  connect-supp (TransportVarSet xs σ) (TransportVarSet ys τ) ∎
  where
    open ≡-Reasoning

sub-between-connect-susps-supp : (σ : Sub (suc n) (suc l) ⋆)
                               → (τ : Sub (suc m) (suc l′) ⋆)
                               → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                               → FVSub (sub-between-connect-susps σ τ) ≡ connect-supp (suspSupp (FVSub σ)) (FVSub τ)
sub-between-connect-susps-supp {n = n} {l = l} {m = m} {l′ = l′} σ τ p = trans (sub-between-connect-supp (suspSub σ) τ getSnd lem2 l1) (cong (λ - → connect-supp - (FVSub τ)) (suspSuppSub σ))
  where
    l1 : FVTm getSnd ⊆ FVSub (suspSub σ)
    l1 = begin
      FVTm getSnd
        ≤⟨ suspSuppSnd (FVSub σ) ⟩
      suspSupp (FVSub σ)
        ≡˘⟨ suspSuppSub σ ⟩
      FVSub (suspSub σ) ∎
      where
        open PReasoning (⊆-poset _)

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
        ≡⟨ cong (λ - → TransportVarSet - (connect-susp-inc-left l l′)) (trans (suspSuppSub σ) (sym (trans (cong (_∪ trueAt (inject₁ (fromℕ (suc l)))) (suspSuppSub σ)) (sym (suspSuppSnd (FVSub σ)))))) ⟩
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

sub-between-connect-susps-Transport : (σ : Sub (suc n) (suc l) ⋆)
                                    → (τ : Sub (suc m) (suc l′) ⋆)
                                    → (xs : VarSet (suc n))
                                    → (ys : VarSet (suc m))
                                    → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                                    -- → Var (fromℕ _) [ connect-inc-right s l′ ∘ τ ]tm ≃tm getSnd [ connect-susp-inc-left s l′ ∘ σ ]tm
                                    -- → Truth (lookup-isVar xs t)
                                    -- → FVTm s ⊆ TransportVarSet xs σ
                                    → TransportVarSet (connect-supp (suspSupp xs) ys) (sub-between-connect-susps σ τ)
                                    ≡ connect-supp (suspSupp (TransportVarSet xs σ)) (TransportVarSet ys τ)
sub-between-connect-susps-Transport σ τ xs ys p = begin
  TransportVarSet (connect-supp (suspSupp xs) ys)
    (sub-between-connect-susps σ τ)
    ≡⟨ sub-between-connect-Transport (suspSub σ) τ getSnd (suspSupp xs) ys getSnd l1 (suspSuppSndTruth xs) l2 ⟩
  connect-supp (TransportVarSet (suspSupp xs) (suspSub σ))
    (TransportVarSet ys τ)
    ≡⟨ cong (λ - → connect-supp - (TransportVarSet ys τ)) (TransportVarSet-susp xs σ) ⟩
  connect-supp (suspSupp (TransportVarSet xs σ))
    (TransportVarSet ys τ) ∎
  where
    l1 : Var (fromℕ _) [ connect-inc-right getSnd _ ∘ τ ]tm
     ≃tm getSnd [ connect-inc-left getSnd _ ∘ suspSub σ ]tm
    l1 = begin
      < Var (fromℕ _) [ connect-inc-right getSnd _ ∘ τ ]tm >tm
        ≈⟨ assoc-tm (connect-inc-right getSnd _) τ (Var (fromℕ _)) ⟩
      < (Var (fromℕ _) [ τ ]tm) [ connect-inc-right getSnd _ ]tm >tm
        ≈⟨ sub-action-≃-tm p refl≃s ⟩
      < Var (fromℕ _) [ connect-inc-right getSnd _ ]tm >tm
        ≈˘⟨ connect-inc-fst-var getSnd _ ⟩
      < getSnd [ connect-inc-left getSnd _ ]tm >tm
        ≈⟨ sub-action-≃-tm (susp-sub-preserve-getSnd σ) refl≃s ⟩
      < getSnd [ suspSub σ ]tm [ connect-inc-left getSnd _ ]tm >tm
        ≈˘⟨ assoc-tm (connect-inc-left getSnd _) (suspSub σ) getSnd ⟩
      < getSnd [ connect-inc-left getSnd _ ∘ suspSub σ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : FVTm getSnd ⊆ TransportVarSet (suspSupp xs) (suspSub σ)
    l2 = begin
      FVTm getSnd
        ≤⟨ suspSuppSnd (TransportVarSet xs σ) ⟩
      suspSupp (TransportVarSet xs σ)
        ≡˘⟨ TransportVarSet-susp xs σ ⟩
      TransportVarSet (suspSupp xs) (suspSub σ) ∎
      where
        open PReasoning (⊆-poset _)

    open ≡-Reasoning

connect-supp-unit-left : (xs : VarSet (suc n))
                       → Truth (lookup-isVar xs (Var (fromℕ _)))
                       → connect-supp (full {1}) xs ≡ᵖ xs
connect-supp-unit-left (ewt emp) p = P.refl refl
connect-supp-unit-left (ewf (y ∷ xs)) p = refl P.∷ connect-supp-unit-left (y ∷ xs) p
connect-supp-unit-left (ewt (y ∷ xs)) p = refl P.∷ connect-supp-unit-left (y ∷ xs) p

connect-supp-fst : (xs : VarSet (suc n)) → (ys : VarSet (suc m)) → Truth (lookup-isVar xs (Var (fromℕ _))) → Truth (lookup-isVar (connect-supp xs ys) (Var (fromℕ _)))
connect-supp-fst xs (x ∷ emp) p = p
connect-supp-fst xs (x ∷ y ∷ ys) p = connect-supp-fst xs (y ∷ ys) p

connect-supp-assoc : (xs : VarSet (suc n)) → (ys : VarSet (suc m)) → (zs : VarSet (suc l))
                   → connect-supp (connect-supp xs ys) zs ≡ᵖ connect-supp xs (connect-supp ys zs)
connect-supp-assoc xs ys (x ∷ emp) = P.refl refl
connect-supp-assoc xs (x′ ∷ ys) (x ∷ y ∷ emp) = P.refl refl
connect-supp-assoc xs (x′ ∷ ys) (x ∷ y ∷ z ∷ zs) = refl P.∷ connect-supp-assoc xs (x′ ∷ ys) (y ∷ z ∷ zs)

connect-supp-≡ᵖ : {xs : VarSet (suc n)} → {xs′ : VarSet (suc n′)} → {ys : VarSet (suc m)} → {ys′ : VarSet (suc m′)} → xs ≡ᵖ xs′ → ys ≡ᵖ ys′ → connect-supp xs ys ≡ᵖ connect-supp xs′ ys′
connect-supp-≡ᵖ p (x∼y P.∷ P.[]) = p
connect-supp-≡ᵖ p (x∼y P.∷ z P.∷ q) = x∼y Pointwise.∷ (connect-supp-≡ᵖ p (z P.∷ q))