{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Support.Properties where

open import Catt.Syntax
open import Catt.Support
open import Catt.Variables
open import Relation.Binary
open import Data.Nat
open import Data.Bool
open import Data.Bool.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (Fin; zero; suc)
open import Tactic.MonoidSolver
open import Data.Product renaming (_,_ to _,,_)
open import Algebra.Bundles

open import Algebra.Definitions

∪-assoc : Associative _≡_ (_∪_ {n})
∪-assoc emp emp emp = refl
∪-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (∨-assoc x y z) (∪-assoc xs ys zs)

∪-left-unit : LeftIdentity _≡_ empty (_∪_ {n})
∪-left-unit emp = refl
∪-left-unit (x ∷ xs) = cong₂ _∷_ refl (∪-left-unit xs)

∪-right-unit : RightIdentity _≡_ empty (_∪_ {n})
∪-right-unit emp = refl
∪-right-unit (x ∷ xs) = cong₂ _∷_ (∨-identityʳ x) (∪-right-unit xs)

∪-comm : Commutative _≡_ (_∪_ {n})
∪-comm emp emp = refl
∪-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (∨-comm x y) (∪-comm xs ys)

∪-idem : Idempotent _≡_ (_∪_ {n})
∪-idem emp = refl
∪-idem (x ∷ xs) = cong₂ _∷_ (∨-idem x) (∪-idem xs)

∪-left-zero : (xs : VarSet n) → full ∪ xs ≡ full
∪-left-zero emp = refl
∪-left-zero (x ∷ xs) = cong ewt (∪-left-zero xs)

∪-right-zero : (xs : VarSet n) → xs ∪ full ≡ full
∪-right-zero emp = refl
∪-right-zero (x ∷ xs) = cong₂ _∷_ (∨-zeroʳ x) (∪-right-zero xs)

FVTm-on-var : (t : Tm n) → .⦃ _ : isVar t ⦄ → FVTm t ≡ trueAt (getVarFin t)
FVTm-on-var (Var i) = refl

module _ {n : ℕ} where

  open import Algebra.Definitions {A = VarSet n} _≡_
  open import Algebra.Structures {A = VarSet n} _≡_

  ∪-isMagma : IsMagma (_∪_)
  ∪-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong = cong₂ _∪_
    }

  ∪-isSemigroup : IsSemigroup _∪_
  ∪-isSemigroup = record
    { isMagma = ∪-isMagma
    ; assoc = ∪-assoc
    }

  ∪-isMonoid : IsMonoid (zipWith _∨_) empty
  ∪-isMonoid = record
    { isSemigroup = ∪-isSemigroup
    ; identity = ∪-left-unit ,, ∪-right-unit
    }

  ∪-monoid : Monoid _ _
  ∪-monoid = record
    { isMonoid = ∪-isMonoid }

TransportVarSet-empty : (σ : Sub n m ⋆) → TransportVarSet empty σ ≡ empty
TransportVarSet-empty ⟨⟩ = refl
TransportVarSet-empty ⟨ σ , t ⟩ = TransportVarSet-empty σ

TransportVarSet-full : (σ : Sub n m ⋆) → TransportVarSet full σ ≡ FVSub σ
TransportVarSet-full ⟨⟩ = refl
TransportVarSet-full ⟨ σ , t ⟩ = cong (_∪ FVTm t) (TransportVarSet-full σ)

TransportVarSet-∪ : (xs ys : VarSet n) → (σ : Sub n m ⋆) → TransportVarSet (xs ∪ ys) σ ≡ TransportVarSet xs σ ∪ TransportVarSet ys σ
TransportVarSet-∪ xs ys ⟨⟩ = sym (∪-left-unit empty)
TransportVarSet-∪ (ewf xs) (ewf ys) ⟨ σ , t ⟩ = TransportVarSet-∪ xs ys σ
TransportVarSet-∪ (ewf xs) (ewt ys) ⟨ σ , t ⟩ = trans (cong (_∪ FVTm t) (TransportVarSet-∪ xs ys σ)) (∪-assoc (TransportVarSet xs σ) (TransportVarSet ys σ) (FVTm t))
TransportVarSet-∪ (ewt xs) (ewf ys) ⟨ σ , t ⟩ = begin
  TransportVarSet (xs ∪ ys) σ ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (TransportVarSet-∪ xs ys σ) ⟩
  TransportVarSet xs σ ∪ TransportVarSet ys σ ∪ FVTm t
    ≡⟨ ∪-assoc (TransportVarSet xs σ) (TransportVarSet ys σ) (FVTm t) ⟩
  TransportVarSet xs σ ∪ (TransportVarSet ys σ ∪ FVTm t)
    ≡⟨ cong (TransportVarSet xs σ ∪_) (∪-comm (TransportVarSet ys σ) (FVTm t)) ⟩
  TransportVarSet xs σ ∪ (FVTm t ∪ TransportVarSet ys σ)
    ≡˘⟨ ∪-assoc (TransportVarSet xs σ) (FVTm t) (TransportVarSet ys σ) ⟩
  TransportVarSet xs σ ∪ FVTm t ∪ TransportVarSet ys σ ∎
  where
    open ≡-Reasoning
TransportVarSet-∪ {n} {m} (ewt xs) (ewt ys) ⟨ σ , t ⟩ = begin
  TransportVarSet (xs ∪ ys) σ ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (TransportVarSet-∪ xs ys σ) ⟩
  TransportVarSet xs σ ∪ TransportVarSet ys σ ∪ FVTm t
    ≡⟨ ∪-assoc (TransportVarSet xs σ) (TransportVarSet ys σ) (FVTm t) ⟩
  TransportVarSet xs σ ∪ (TransportVarSet ys σ ∪ FVTm t)
    ≡˘⟨ cong (λ - → TransportVarSet xs σ ∪ (TransportVarSet ys σ ∪ -)) (∪-idem (FVTm t)) ⟩
  TransportVarSet xs σ ∪ (TransportVarSet ys σ ∪ (FVTm t ∪ FVTm t))
    ≡˘⟨ cong (TransportVarSet xs σ ∪_) (∪-assoc (TransportVarSet ys σ) (FVTm t) (FVTm t)) ⟩
  TransportVarSet xs σ ∪ (TransportVarSet ys σ ∪ FVTm t ∪ FVTm t)
    ≡⟨ cong (λ - → TransportVarSet xs σ ∪ (- ∪ FVTm t)) (∪-comm (TransportVarSet ys σ) (FVTm t)) ⟩
  TransportVarSet xs σ ∪ (FVTm t ∪ TransportVarSet ys σ ∪ FVTm t)
    ≡⟨ solve (∪-monoid {m}) ⟩
  TransportVarSet xs σ ∪ FVTm t ∪ (TransportVarSet ys σ ∪ FVTm t) ∎
  where
    open ≡-Reasoning

TransportVarSet-ty : (A : Ty n) → (σ : Sub n m ⋆) → TransportVarSet (FVTy A) σ ≡ FVTy (A [ σ ]ty)
TransportVarSet-tm : (t : Tm n) → (σ : Sub n m ⋆) → TransportVarSet (FVTm t) σ ≡ FVTm (t [ σ ]tm)
TransportVarSet-sub : (τ : Sub l n ⋆) → (σ : Sub n m ⋆) → TransportVarSet (FVSub τ) σ ≡ FVSub (σ ∘ τ)

TransportVarSet-ty ⋆ σ = TransportVarSet-empty σ
TransportVarSet-ty (s ─⟨ A ⟩⟶ t) σ = begin
  TransportVarSet (FVTy (s ─⟨ A ⟩⟶ t)) σ
    ≡⟨ TransportVarSet-∪ (FVTy A ∪ FVTm s) (FVTm t) σ ⟩
  TransportVarSet (FVTy A ∪ FVTm s) σ ∪ TransportVarSet (FVTm t) σ
    ≡⟨ cong (_∪ TransportVarSet (FVTm t) σ) (TransportVarSet-∪ (FVTy A) (FVTm s) σ) ⟩
  TransportVarSet (FVTy A) σ ∪ TransportVarSet (FVTm s) σ ∪ TransportVarSet (FVTm t) σ
    ≡⟨ cong₂ _∪_ (cong₂ _∪_ (TransportVarSet-ty A σ) (TransportVarSet-tm s σ)) (TransportVarSet-tm t σ) ⟩
  FVTy ((s ─⟨ A ⟩⟶ t) [ σ ]ty) ∎
  where
    open ≡-Reasoning

TransportVarSet-tm (Var zero) ⟨ σ , t ⟩ = trans (cong (_∪ FVTm t) (TransportVarSet-empty σ)) (∪-left-unit (FVTm t))
TransportVarSet-tm (Var (suc i)) ⟨ σ , t ⟩ = TransportVarSet-tm (Var i) σ
TransportVarSet-tm (Coh S A τ) σ = TransportVarSet-sub τ σ

TransportVarSet-sub ⟨⟩ σ = TransportVarSet-empty σ
TransportVarSet-sub ⟨ τ , t ⟩ σ = trans (TransportVarSet-∪ (FVSub τ) (FVTm t) σ) (cong₂ _∪_ (TransportVarSet-sub τ σ) (TransportVarSet-tm t σ))

supp-lift-ty : (A : Ty n) → FVTy (liftType A) ≡ ewf (FVTy A)
supp-lift-tm : (t : Tm n) → FVTm (liftTerm t) ≡ ewf (FVTm t)
supp-lift-sub : (σ : Sub n m ⋆) → FVSub (liftSub σ) ≡ ewf (FVSub σ)

supp-lift-ty ⋆ = refl
supp-lift-ty (s ─⟨ A ⟩⟶ t) = cong₂ _∪_ (cong₂ _∪_ (supp-lift-ty A) (supp-lift-tm s)) (supp-lift-tm t)

supp-lift-tm (Var i) = refl
supp-lift-tm (Coh S A σ) = supp-lift-sub σ

supp-lift-sub ⟨⟩ = refl
supp-lift-sub ⟨ σ , t ⟩ = cong₂ _∪_ (supp-lift-sub σ) (supp-lift-tm t)

idSub-supp : (n : ℕ) → FVSub (idSub n) ≡ full
idSub-supp zero = refl
idSub-supp (suc n) = trans (cong (_∪ ewt empty) (supp-lift-sub (idSub n))) (cong ewt (trans (∪-right-unit (FVSub (idSub n))) (idSub-supp n)))

TransportVarSet-lift : (xs : VarSet n) → (σ : Sub n m ⋆) → TransportVarSet xs (liftSub σ) ≡ ewf (TransportVarSet xs σ)
TransportVarSet-lift emp ⟨⟩ = refl
TransportVarSet-lift (ewf xs) ⟨ σ , t ⟩ = TransportVarSet-lift xs σ
TransportVarSet-lift (ewt xs) ⟨ σ , t ⟩ = cong₂ _∪_ (TransportVarSet-lift xs σ) (supp-lift-tm t)

TransportVarSet-id : (xs : VarSet n) → TransportVarSet xs (idSub n) ≡ xs
TransportVarSet-id emp = refl
TransportVarSet-id (ewf xs) = trans (TransportVarSet-lift xs (idSub _)) (cong ewf (TransportVarSet-id xs))
TransportVarSet-id (ewt xs) = trans (cong (_∪ ewt empty) (TransportVarSet-lift xs (idSub _))) (cong ewt (trans (∪-right-unit (TransportVarSet xs (idSub _))) (TransportVarSet-id xs)))
