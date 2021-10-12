{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Support.Properties where

open import Catt.Syntax
open import Catt.Support
open import Catt.Variables
open import Relation.Binary
open import Data.Nat
open import Data.Bool renaming (T to Truth)
open import Data.Bool.Properties
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (Fin; zero; suc)
open import Tactic.MonoidSolver
open import Data.Product renaming (_,_ to _,,_)
open import Algebra.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
import Relation.Binary.Reasoning.PartialOrder as PReasoning
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using (Pointwise)
open import Data.Sum
open import Data.Unit using (tt)

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

idSub≃-supp : (p : Γ ≃c Δ) → FVSub (idSub≃ p) ≡ full
idSub≃-supp Emp≃ = refl
idSub≃-supp (Add≃ p x) = trans (cong (_∪ ewt empty) (supp-lift-sub (idSub≃ p))) (cong ewt (trans (∪-right-unit (FVSub (idSub≃ p))) (idSub≃-supp p)))

TransportVarSet-lift : (xs : VarSet n) → (σ : Sub n m ⋆) → TransportVarSet xs (liftSub σ) ≡ ewf (TransportVarSet xs σ)
TransportVarSet-lift emp ⟨⟩ = refl
TransportVarSet-lift (ewf xs) ⟨ σ , t ⟩ = TransportVarSet-lift xs σ
TransportVarSet-lift (ewt xs) ⟨ σ , t ⟩ = cong₂ _∪_ (TransportVarSet-lift xs σ) (supp-lift-tm t)

TransportVarSet-id : (xs : VarSet n) → TransportVarSet xs (idSub n) ≡ xs
TransportVarSet-id emp = refl
TransportVarSet-id (ewf xs) = trans (TransportVarSet-lift xs (idSub _)) (cong ewf (TransportVarSet-id xs))
TransportVarSet-id (ewt xs) = trans (cong (_∪ ewt empty) (TransportVarSet-lift xs (idSub _))) (cong ewt (trans (∪-right-unit (TransportVarSet xs (idSub _))) (TransportVarSet-id xs)))

⊆-refl : {xs : VarSet n} → xs ⊆ xs
⊆-refl = sym (∪-idem _)

⊆-reflexive : {xs ys : VarSet n} → xs ≡ ys → xs ⊆ ys
⊆-reflexive refl = ⊆-refl

⊆-trans : {xs ys zs : VarSet n} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans {xs = xs} {ys} {zs} p q = begin
  zs
    ≡⟨ q ⟩
  zs ∪ ys
    ≡⟨ cong (zs ∪_) p ⟩
  zs ∪ (ys ∪ xs)
    ≡˘⟨ ∪-assoc zs ys xs ⟩
  zs ∪ ys ∪ xs
    ≡˘⟨ cong (_∪ xs) q ⟩
  zs ∪ xs ∎
  where
    open ≡-Reasoning

⊆-antisym : {xs ys : VarSet n} → xs ⊆ ys → ys ⊆ xs → xs ≡ ys
⊆-antisym {xs = xs} {ys} p q = begin
  xs
    ≡⟨ q ⟩
  xs ∪ ys
    ≡⟨ ∪-comm xs ys ⟩
  ys ∪ xs
    ≡˘⟨ p ⟩
  ys ∎
  where
    open ≡-Reasoning

⊆-preorder : (n : ℕ) → IsPreorder _≡_ (_⊆_ {n})
IsPreorder.isEquivalence (⊆-preorder n) = isEquivalence
IsPreorder.reflexive (⊆-preorder n) = ⊆-reflexive
IsPreorder.trans (⊆-preorder n) = ⊆-trans

⊆-partial-order : (n : ℕ) → IsPartialOrder _≡_ (_⊆_ {n})
IsPartialOrder.isPreorder (⊆-partial-order n) = ⊆-preorder n
IsPartialOrder.antisym (⊆-partial-order n) = ⊆-antisym

⊆-poset : (n : ℕ) → Poset _ _ _
Poset.Carrier (⊆-poset n) = VarSet n
Poset._≈_ (⊆-poset n) = _≡_
Poset._≤_ (⊆-poset n) = _⊆_
Poset.isPartialOrder (⊆-poset n) = ⊆-partial-order n

⊆-TransportVarSet : (σ : Sub n m ⋆) → {xs ys : VarSet n} → xs ⊆ ys → TransportVarSet xs σ ⊆ TransportVarSet ys σ
⊆-TransportVarSet σ {xs} {ys} p = begin
  TransportVarSet ys σ
    ≡⟨ cong (λ - → TransportVarSet - σ) p ⟩
  TransportVarSet (ys ∪ xs) σ
    ≡⟨ TransportVarSet-∪ ys xs σ ⟩
  TransportVarSet ys σ ∪ TransportVarSet xs σ ∎
  where
    open ≡-Reasoning

lookup-isVar-⊆ : (xs : VarSet n) → (s : Tm n) → .⦃ _ : isVar s ⦄ → Truth (lookup-isVar xs s) → FVTm s ⊆ xs
lookup-isVar-⊆ (ewt xs) (Var zero) p = cong ewt (sym (∪-right-unit xs))
lookup-isVar-⊆ (ewf xs) (Var (suc i)) p = cong ewf (lookup-isVar-⊆ xs (Var i) p)
lookup-isVar-⊆ (ewt xs) (Var (suc i)) p = cong ewt (lookup-isVar-⊆ xs (Var i) p)

TransportVarSet-comp : (xs : VarSet l) → (σ : Sub n m ⋆) → (τ : Sub l n ⋆) → TransportVarSet xs (σ ∘ τ) ≡ TransportVarSet (TransportVarSet xs τ) σ
TransportVarSet-comp emp σ ⟨⟩ = sym (TransportVarSet-empty σ)
TransportVarSet-comp (ewf xs) σ ⟨ τ , t ⟩ = TransportVarSet-comp xs σ τ
TransportVarSet-comp (ewt xs) σ ⟨ τ , t ⟩ = begin
  TransportVarSet xs (σ ∘ τ) ∪ FVTm (t [ σ ]tm)
    ≡⟨ cong₂ _∪_ (TransportVarSet-comp xs σ τ) (sym (TransportVarSet-tm t σ)) ⟩
  TransportVarSet (TransportVarSet xs τ) σ ∪ TransportVarSet (FVTm t) σ
    ≡˘⟨ TransportVarSet-∪ (TransportVarSet xs τ) (FVTm t) σ ⟩
  TransportVarSet (TransportVarSet xs τ ∪ FVTm t) σ ∎
  where
    open ≡-Reasoning

isVar-supp : (t : Tm n) → .⦃ _ : isVar t ⦄ → FVTm t ≡ trueAt (getVarFin t)
isVar-supp (Var i) = refl

unrestrict-supp : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → FVSub (unrestrict σ) ≡ FVSub σ
unrestrict-supp ⟨⟩ = refl
unrestrict-supp ⟨ σ , t ⟩ = cong (_∪ FVTm t) (unrestrict-supp σ)

∪-⊆-2 : (xs ys : VarSet n) → ys ⊆ xs ∪ ys
∪-⊆-2 xs ys = begin
  xs ∪ ys
    ≡˘⟨ cong (xs ∪_) (∪-idem ys) ⟩
  xs ∪ (ys ∪ ys)
    ≡˘⟨ ∪-assoc xs ys ys ⟩
  xs ∪ ys ∪ ys ∎
  where
    open ≡-Reasoning

∪-⊆-1 : (xs ys : VarSet n) → xs ⊆ xs ∪ ys
∪-⊆-1 xs ys = begin
  xs
    ≤⟨ ∪-⊆-2 ys xs ⟩
  ys ∪ xs
    ≡⟨ ∪-comm ys xs ⟩
  xs ∪ ys ∎
  where
    open PReasoning (⊆-poset _)

TransportVarSet-idSub≃ : (xs : VarSet n) → (p : Γ ≃c Δ) → TransportVarSet xs (idSub≃ p) ≡ᵖ xs
TransportVarSet-idSub≃ emp Emp≃ = P.refl refl
TransportVarSet-idSub≃ (ewf xs) (Add≃ p y) = P.trans trans (P.≡⇒Pointwise-≡ (TransportVarSet-lift xs (idSub≃ p))) (refl P.∷ TransportVarSet-idSub≃ xs p)
TransportVarSet-idSub≃ (ewt xs) (Add≃ p y) = P.trans trans (P.≡⇒Pointwise-≡ (trans (cong (_∪ ewt empty) (TransportVarSet-lift xs (idSub≃ p))) (cong ewt (∪-right-unit (TransportVarSet xs (idSub≃ p)))))) (refl P.∷ TransportVarSet-idSub≃ xs p)

∪-Truth : (xs ys : VarSet n) → (i : Fin n) → Truth (lookup (xs ∪ ys) i) → Truth (lookup xs i) ⊎ Truth (lookup ys i)
∪-Truth (x ∷ xs) (y ∷ ys) (suc i) truth = ∪-Truth xs ys i truth
∪-Truth (ewf xs) (y ∷ ys) zero truth = inj₂ truth
∪-Truth (ewt xs) (y ∷ ys) zero truth = inj₁ tt

sub-type-⊆ : (σ : Sub n m A) → FVTy A ⊆ FVSub σ
sub-type-⊆ ⟨⟩ = ⊆-refl
sub-type-⊆ ⟨ σ , t ⟩ = ⊆-trans (sub-type-⊆ σ) (∪-⊆-1 (FVSub σ) (FVTm t))
