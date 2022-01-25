{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Support.Properties where

open import Catt.Syntax
open import Catt.Support
open import Catt.Variables
open import Relation.Binary
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (true;false;Bool) renaming (T to Truth)
import Data.Bool.Properties as B
open import Data.Vec hiding (drop)
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (Fin; zero; suc; fromℕ) renaming (_≟_ to _f≟_)
open import Data.Fin.Properties using (toℕ-injective)
open import Tactic.MonoidSolver
open import Data.Product renaming (_,_ to _,,_)
open import Algebra.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
import Relation.Binary.Reasoning.PartialOrder as PReasoning
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using (Pointwise)
open import Data.Sum
open import Data.Unit using (⊤;tt)
open import Catt.Globular
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Connection
open import Catt.Connection.Pasting
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Data.Empty
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Tree
open import Catt.Tree.Pasting
open import Catt.Variables
open import Catt.Variables.Properties
open import Relation.Nullary

open import Algebra.Definitions

FVTm-≃ : s ≃tm t → FVTm s ≡ FVTm t
FVTy-≃ : A ≃ty B → FVTy A ≡ FVTy B
FVSub-≃ : σ ≃s τ → FVSub σ ≡ FVSub τ

FVTm-≃ (Var≃ x y) with toℕ-injective y
... | refl = refl
FVTm-≃ (Coh≃ x y z) = FVSub-≃ z

FVTy-≃ (Star≃ x) = refl
FVTy-≃ (Arr≃ p q r) = cong₂ _∪_ (cong₂ _∪_ (FVTy-≃ q) (FVTm-≃ p)) (FVTm-≃ r)

FVSub-≃ (Null≃ x) = FVTy-≃ x
FVSub-≃ (Ext≃ p x) = cong₂ _∪_ (FVSub-≃ p) (FVTm-≃ x)

∪-assoc : Associative _≡_ (_∪_ {n})
∪-assoc emp emp emp = refl
∪-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (B.∨-assoc x y z) (∪-assoc xs ys zs)

∪-left-unit : LeftIdentity _≡_ empty (_∪_ {n})
∪-left-unit emp = refl
∪-left-unit (x ∷ xs) = cong₂ _∷_ refl (∪-left-unit xs)

∪-right-unit : RightIdentity _≡_ empty (_∪_ {n})
∪-right-unit emp = refl
∪-right-unit (x ∷ xs) = cong₂ _∷_ (B.∨-identityʳ x) (∪-right-unit xs)

∪-comm : Commutative _≡_ (_∪_ {n})
∪-comm emp emp = refl
∪-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (B.∨-comm x y) (∪-comm xs ys)

∪-idem : Idempotent _≡_ (_∪_ {n})
∪-idem emp = refl
∪-idem (x ∷ xs) = cong₂ _∷_ (B.∨-idem x) (∪-idem xs)

∪-left-zero : (xs : VarSet n) → full ∪ xs ≡ full
∪-left-zero emp = refl
∪-left-zero (x ∷ xs) = cong ewt (∪-left-zero xs)

∪-right-zero : (xs : VarSet n) → xs ∪ full ≡ full
∪-right-zero emp = refl
∪-right-zero (x ∷ xs) = cong₂ _∷_ (B.∨-zeroʳ x) (∪-right-zero xs)

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

  ∪-isMonoid : IsMonoid _∪_ empty
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
TransportVarSet-sub : (τ : Sub l n A) → (σ : Sub n m ⋆) → TransportVarSet (FVSub τ) σ ≡ FVSub (σ ∘ τ)

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

TransportVarSet-sub {A = A} ⟨⟩ σ = TransportVarSet-ty A σ -- TransportVarSet-empty σ
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

idSub-supp : FVSub (idSub {n}) ≡ full
idSub-supp {zero} = refl
idSub-supp {suc n} = trans (cong (_∪ ewt empty) (supp-lift-sub idSub)) (cong ewt (trans (∪-right-unit (FVSub idSub)) idSub-supp))

idSub≃-supp : (p : Γ ≃c Δ) → FVSub (idSub≃ p) ≡ full
idSub≃-supp Emp≃ = refl
idSub≃-supp (Add≃ p x) = trans (cong (_∪ ewt empty) (supp-lift-sub (idSub≃ p))) (cong ewt (trans (∪-right-unit (FVSub (idSub≃ p))) (idSub≃-supp p)))

TransportVarSet-lift : (xs : VarSet n) → (σ : Sub n m ⋆) → TransportVarSet xs (liftSub σ) ≡ ewf (TransportVarSet xs σ)
TransportVarSet-lift emp ⟨⟩ = refl
TransportVarSet-lift (ewf xs) ⟨ σ , t ⟩ = TransportVarSet-lift xs σ
TransportVarSet-lift (ewt xs) ⟨ σ , t ⟩ = cong₂ _∪_ (TransportVarSet-lift xs σ) (supp-lift-tm t)

TransportVarSet-id : (xs : VarSet n) → TransportVarSet xs idSub ≡ xs
TransportVarSet-id emp = refl
TransportVarSet-id (ewf xs) = trans (TransportVarSet-lift xs idSub) (cong ewf (TransportVarSet-id xs))
TransportVarSet-id (ewt xs) = trans (cong (_∪ ewt empty) (TransportVarSet-lift xs idSub)) (cong ewt (trans (∪-right-unit (TransportVarSet xs idSub)) (TransportVarSet-id xs)))

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

⊆-top : (xs : VarSet n) → xs ⊆ full
⊆-top xs = sym (∪-left-zero xs)

⊆-bot : (xs : VarSet n) → empty ⊆ xs
⊆-bot xs = sym (∪-right-unit xs)

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

∪-⊆ : {xs ys zs : VarSet n} → xs ⊆ zs → ys ⊆ zs → xs ∪ ys ⊆ zs
∪-⊆ {xs = xs} {ys} {zs} p q = begin
  zs
    ≡⟨ q ⟩
  zs ∪ ys
    ≡⟨ cong (_∪ ys) p ⟩
  zs ∪ xs ∪ ys
    ≡⟨ ∪-assoc zs xs ys ⟩
  zs ∪ (xs ∪ ys) ∎
  where
    open ≡-Reasoning

-- subbed-ty-⊆ : (B : Ty n) → (σ : Sub n m A) → FVTy (B [ σ ]ty) ⊆ FVSub σ
-- subbed-tm-⊆ : (t : Tm n) → (σ : Sub n m A) → FVTm (t [ σ ]tm) ⊆ FVSub σ

-- subbed-ty-⊆ ⋆ σ = sub-type-⊆ σ
-- subbed-ty-⊆ (s ─⟨ B ⟩⟶ t) σ = ∪-⊆ (∪-⊆ (subbed-ty-⊆ B σ) (subbed-tm-⊆ s σ)) (subbed-tm-⊆ t σ)

-- subbed-tm-⊆ (Var zero) ⟨ σ , t ⟩ = ∪-⊆-2 (FVSub σ) (FVTm t)
-- subbed-tm-⊆ (Var (suc i)) ⟨ σ , t ⟩ = ⊆-trans (subbed-tm-⊆ (Var i) σ) (∪-⊆-1 (FVSub σ) (FVTm t))
-- subbed-tm-⊆ (Coh S A τ) σ = {!!}

DC-⊆ : (Γ : Ctx n) → (xs : VarSet n) → xs ⊆ DC Γ xs
DC-⊆ ∅ emp = ⊆-refl
DC-⊆ (Γ , A) (ewf xs) = cong ewf (DC-⊆ Γ xs)
DC-⊆ (Γ , A) (ewt xs) = cong ewt (begin
  xs
    ≤⟨ ∪-⊆-1 xs (FVTy A) ⟩
  xs ∪ FVTy A
    ≤⟨ DC-⊆ Γ (xs ∪ FVTy A) ⟩
  DC Γ (xs ∪ FVTy A) ∎)
  where
    open PReasoning (⊆-poset _)

module _ where
  open ≡-Reasoning

  DC-cup : (Γ : Ctx n) → (xs ys : VarSet n) → DC Γ (xs ∪ ys) ≡ DC Γ xs ∪ DC Γ ys
  DC-cup ∅ xs ys = refl
  DC-cup (Γ , A) (ewf xs) (ewf ys) = cong ewf (DC-cup Γ xs ys)
  DC-cup (Γ , A) (ewf xs) (ewt ys) = cong ewt (begin
    DC Γ (xs ∪ ys ∪ FVTy A)
      ≡⟨ cong (DC Γ) (∪-assoc xs ys (FVTy A)) ⟩
    DC Γ (xs ∪ (ys ∪ FVTy A))
      ≡⟨ DC-cup Γ xs (ys ∪ FVTy A) ⟩
    (DC Γ xs) ∪ (DC Γ (ys ∪ FVTy A)) ∎)
  DC-cup (Γ , A) (ewt xs) (ewf ys) = cong ewt (begin
    DC Γ (xs ∪ ys ∪ FVTy A)
      ≡⟨ cong (DC Γ) (∪-assoc xs ys (FVTy A)) ⟩
    DC Γ (xs ∪ (ys ∪ FVTy A))
      ≡⟨ cong (λ - → DC Γ (xs ∪ -)) (∪-comm ys (FVTy A)) ⟩
    DC Γ (xs ∪ (FVTy A ∪ ys))
      ≡˘⟨ cong (DC Γ) (∪-assoc xs (FVTy A) ys) ⟩
    DC Γ (xs ∪ FVTy A ∪ ys)
      ≡⟨ DC-cup Γ (xs ∪ FVTy A) ys ⟩
    (DC Γ (xs ∪ FVTy A)) ∪ (DC Γ ys) ∎)
  DC-cup {suc n} (Γ , A) (ewt xs) (ewt ys) = cong ewt (begin
    DC Γ (xs ∪ ys ∪ FVTy A)
      ≡˘⟨ cong (λ - → DC Γ (xs ∪ ys ∪ -)) (∪-idem (FVTy A)) ⟩
    DC Γ (xs ∪ ys ∪ (FVTy A ∪ FVTy A))
      ≡⟨ cong (DC Γ) (solve (∪-monoid {n})) ⟩
    DC Γ (xs ∪ (ys ∪ FVTy A) ∪ FVTy A)
      ≡⟨ cong (λ - → DC Γ (xs ∪ - ∪ FVTy A)) (∪-comm ys (FVTy A)) ⟩
    DC Γ (xs ∪ (FVTy A ∪ ys) ∪ FVTy A)
      ≡⟨ cong (DC Γ) (solve (∪-monoid {n})) ⟩
    DC Γ ((xs ∪ FVTy A) ∪ (ys ∪ FVTy A))
      ≡⟨ DC-cup Γ (xs ∪ FVTy A) (ys ∪ FVTy A) ⟩
    DC Γ (xs ∪ FVTy A) ∪ DC Γ (ys ∪ FVTy A) ∎)

  DC-idem : (Γ : Ctx n) → (xs : VarSet n) → DC Γ (DC Γ xs) ≡ DC Γ xs
  DC-idem ∅ xs = refl
  DC-idem (Γ , A) (ewf xs) = cong ewf (DC-idem Γ xs)
  DC-idem (Γ , A) (ewt xs) = cong ewt (begin
    DC Γ (DC Γ (xs ∪ FVTy A) ∪ FVTy A)
      ≡⟨ cong (λ - → DC Γ (- ∪ FVTy A)) (DC-cup Γ xs (FVTy A)) ⟩
    DC Γ (DC Γ xs ∪ DC Γ (FVTy A) ∪ FVTy A)
      ≡⟨ cong (DC Γ) (∪-assoc (DC Γ xs) (DC Γ (FVTy A)) (FVTy A)) ⟩
    DC Γ (DC Γ xs ∪ (DC Γ (FVTy A) ∪ FVTy A))
      ≡˘⟨ cong (λ - → DC Γ (DC Γ xs ∪ -)) (DC-⊆ Γ (FVTy A)) ⟩
    DC Γ (DC Γ xs ∪ DC Γ (FVTy A))
      ≡˘⟨ cong (DC Γ) (DC-cup Γ xs (FVTy A)) ⟩
    DC Γ (DC Γ (xs ∪ FVTy A))
      ≡⟨ DC-idem Γ (xs ∪ FVTy A) ⟩
    DC Γ (xs ∪ FVTy A) ∎)

  DC-empty : (Γ : Ctx n) → DC Γ empty ≡ empty
  DC-empty ∅ = refl
  DC-empty (Γ , A) = cong ewf (DC-empty Γ)

⊆-cong-∪-1 : {xs ys zs : VarSet n} → ys ⊆ zs → xs ∪ ys ⊆ xs ∪ zs
⊆-cong-∪-1 p = ∪-⊆ (∪-⊆-1 _ _) (⊆-trans p (∪-⊆-2 _ _))

build-⊆-1 : (x : Bool) → {xs ys : VarSet n} → xs ⊆ ys → ewf xs ⊆ (x ∷ ys)
build-⊆-1 x p = cong₂ _∷_ (sym (B.∨-identityʳ x)) p

build-⊆-2 : (x : Bool) → {xs ys : VarSet n} → xs ⊆ ys → (x ∷ xs) ⊆ ewt ys
build-⊆-2 x p = cong ewt p

debuild-⊆-2 : {x y : Bool} → {xs ys : VarSet n} → (x ∷ xs) ⊆ (y ∷ ys) → xs ⊆ ys
debuild-⊆-2 p = cong tail p


FVTy-comp-⊆ : (A : Ty n) → (σ : Sub n m B) → FVTy (A [ σ ]ty) ⊆ FVSub σ
FVTm-comp-⊆ : (t : Tm n) → (σ : Sub n m A) → FVTm (t [ σ ]tm) ⊆ FVSub σ
FVSub-comp-⊆ : (σ : Sub n m A) → (τ : Sub l n ⋆) → FVSub (σ ∘ τ) ⊆ FVSub σ

FVTy-comp-⊆ ⋆ σ = sub-type-⊆ σ
FVTy-comp-⊆ (s ─⟨ A ⟩⟶ t) σ = ∪-⊆ (∪-⊆ (FVTy-comp-⊆ A σ) (FVTm-comp-⊆ s σ)) (FVTm-comp-⊆ t σ)

FVTm-comp-⊆ (Var zero) ⟨ σ , t ⟩ = ∪-⊆-2 (FVSub σ) (FVTm t)
FVTm-comp-⊆ (Var (suc i)) ⟨ σ , t ⟩ = ⊆-trans (FVTm-comp-⊆ (Var i) σ) (∪-⊆-1 (FVSub σ) (FVTm t))
FVTm-comp-⊆ {A = ⋆} (Coh S B τ) σ = FVSub-comp-⊆ σ τ
FVTm-comp-⊆ {A = s ─⟨ A ⟩⟶ t} (Coh S B τ) σ = begin
  FVTm
      (Coh (suspTree S) (suspTy B) (suspSub τ) [ unrestrict σ ]tm)
    ≤⟨ FVTm-comp-⊆ (Coh (suspTree S) (suspTy B) (suspSub τ)) (unrestrict σ) ⟩
  FVSub (unrestrict σ)
    ≡⟨ unrestrict-supp σ ⟩
  FVSub σ ∎
  where
    open PReasoning (⊆-poset _)

FVSub-comp-⊆ σ ⟨⟩ = sub-type-⊆ σ
FVSub-comp-⊆ σ ⟨ τ , t ⟩ = begin
  FVSub (σ ∘ τ) ∪ FVTm (t [ σ ]tm)
    ≤⟨ ⊆-cong-∪-1 (FVTm-comp-⊆ t σ) ⟩
  FVSub (σ ∘ τ) ∪ FVSub σ
    ≤⟨ ∪-⊆ (FVSub-comp-⊆ σ τ) ⊆-refl ⟩
  FVSub σ ∎
  where
    open PReasoning (⊆-poset _)

SuppContainsType : (t : Tm n) → (Γ : Ctx n) → SuppTy Γ (tm-to-ty Γ t) ⊆ SuppTm Γ t
SuppContainsType (Var zero) (Γ , A) = begin
  SuppTy (Γ , A) (liftType A)
    ≡⟨ cong (DC (Γ , A)) (supp-lift-ty A) ⟩
  ewf (SuppTy Γ A)
    ≤⟨ cong ewt (sym (∪-idem (SuppTy Γ A))) ⟩
  ewt (SuppTy Γ A)
    ≡˘⟨ cong (λ - → ewt (DC Γ -)) (∪-left-unit (FVTy A)) ⟩
  ewt (DC Γ (empty ∪ FVTy A))
    ≡⟨⟩
  SuppTm (Γ , A) 0V ∎
  where
    open PReasoning (⊆-poset _)

SuppContainsType (Var (suc i)) (Γ , A) = begin
  SuppTy (Γ , A) (liftType (Γ ‼ i))
    ≡⟨ cong (DC (Γ , A)) (supp-lift-ty (Γ ‼ i)) ⟩
  ewf (SuppTy Γ (Γ ‼ i))
    ≤⟨ cong ewf (SuppContainsType (Var i) Γ) ⟩
  ewf (SuppTm Γ (Var i))
    ≡⟨⟩
  SuppTm (Γ , A) (Var (suc i)) ∎
  where
    open PReasoning (⊆-poset _)

SuppContainsType (Coh S A σ) Γ = trans (cong (DC Γ) (FVTy-comp-⊆ A σ)) (DC-cup Γ (FVTm (Coh S A σ)) (FVTy (A [ σ ]ty)))

full-⊆ : {xs : VarSet n} → full ⊆ xs → xs ≡ full
full-⊆ p = trans p (∪-right-zero _)

subctx-inc-ty : (A : Ty n) → (σ : Sub m n ⋆) → .⦃ varToVar σ ⦄ → .(FVTy A ⊆ FVSub σ) → Ty m
subctx-inc-tm : (t : Tm n) → (σ : Sub m n ⋆) → .⦃ varToVar σ ⦄ → .(FVTm t ⊆ FVSub σ) → Tm m
subctx-inc-sub : (τ : Sub l n ⋆) → (σ : Sub m n ⋆) → .⦃ varToVar σ ⦄ → .(FVSub τ ⊆ FVSub σ) → Sub l m ⋆

subctx-inc-ty ⋆ σ p = ⋆
subctx-inc-ty (s ─⟨ A ⟩⟶ t) σ p = (subctx-inc-tm s σ (⊆-trans (⊆-trans (∪-⊆-2 (FVTy A) (FVTm s)) (∪-⊆-1 (FVTy A ∪ FVTm s) (FVTm t))) p)) ─⟨ (subctx-inc-ty A σ (⊆-trans (⊆-trans (∪-⊆-1 (FVTy A) (FVTm s)) (∪-⊆-1 (FVTy A ∪ FVTm s) (FVTm t))) p)) ⟩⟶ (subctx-inc-tm t σ (⊆-trans (∪-⊆-2 (FVTy A ∪ FVTm s) (FVTm t)) p))

subctx-inc-tm (Var i) ⟨⟩ p = ⊥-elim (lem i p)
  where
    lem : (i : Fin n) → .(trueAt i ⊆ empty) → ⊥
    lem zero ()
    lem (suc i) p = lem i (debuild-⊆-2 p)
subctx-inc-tm (Var i) ⟨ σ , Var j ⟩ ⦃ q ⦄ p with i f≟ j
... | yes x = 0V
... | no x = liftTerm (subctx-inc-tm (Var i) σ ⦃ proj₁ q ⦄ (lem i j x (FVSub σ) p))
  where
    lem : (i j : Fin n) → ¬ i ≡ j → (xs : VarSet n) → trueAt i ⊆ xs ∪ trueAt j → trueAt i ⊆ xs
    lem zero zero p xs q = ⊥-elim (p refl)
    lem zero (suc j) p (ewt xs) q = cong ewt (⊆-bot xs)
    lem (suc i) zero p (x ∷ xs) q = build-⊆-1 x (⊆-trans (debuild-⊆-2 q) (⊆-reflexive (∪-right-unit xs)))
    lem (suc i) (suc j) p (x ∷ xs) q = build-⊆-1 x (lem i j (λ where refl → p refl) xs (debuild-⊆-2 q))

subctx-inc-tm (Coh S A τ) σ p = Coh S A (subctx-inc-sub τ σ p)

subctx-inc-sub ⟨⟩ σ p = ⟨⟩
subctx-inc-sub ⟨ τ , t ⟩ σ p = ⟨ (subctx-inc-sub τ σ (⊆-trans (∪-⊆-1 (FVSub τ) (FVTm t)) p)) , (subctx-inc-tm t σ (⊆-trans (∪-⊆-2 (FVSub τ) (FVTm t)) p)) ⟩

is-DC : (Γ : Ctx n) → (xs : VarSet n) → Set
is-DC ∅ emp = ⊤
is-DC (Γ , A) (ewf xs) = is-DC Γ xs
is-DC (Γ , A) (ewt xs) = is-DC Γ xs × (FVTy A ⊆ xs)

DC-is-DC : (Γ : Ctx n) → (xs : VarSet n) → is-DC Γ (DC Γ xs)
DC-is-DC ∅ emp = tt
DC-is-DC (Γ , A) (ewf xs) = DC-is-DC Γ xs
DC-is-DC (Γ , A) (ewt xs) = (DC-is-DC Γ (xs ∪ FVTy A)) ,, ⊆-trans (∪-⊆-2 xs (FVTy A)) (DC-⊆ Γ (xs ∪ FVTy A))

VarSet-size : VarSet n → ℕ
VarSet-size emp = 0
VarSet-size (ewf xs) = VarSet-size xs
VarSet-size (ewt xs) = suc (VarSet-size xs)

supp-ctx-inc : (xs : VarSet n) → Sub (VarSet-size xs) n ⋆
supp-ctx-inc emp = ⟨⟩
supp-ctx-inc (ewf xs) = liftSub (supp-ctx-inc xs)
supp-ctx-inc (ewt xs) = ⟨ (liftSub (supp-ctx-inc xs)) , 0V ⟩

supp-ctx-inc-v2v : (xs : VarSet n) → varToVar (supp-ctx-inc xs)
supp-ctx-inc-v2v emp = tt
supp-ctx-inc-v2v (ewf xs) = liftSub-preserve-var-to-var (supp-ctx-inc xs) ⦃ supp-ctx-inc-v2v xs ⦄
supp-ctx-inc-v2v (ewt xs) = (liftSub-preserve-var-to-var (supp-ctx-inc xs) ⦃ supp-ctx-inc-v2v xs ⦄) ,, tt

supp-ctx-inc-FV : (xs : VarSet n) → FVSub (supp-ctx-inc xs) ≡ xs
supp-ctx-inc-FV emp = refl
supp-ctx-inc-FV (ewf xs) = trans (supp-lift-sub (supp-ctx-inc xs)) (cong ewf (supp-ctx-inc-FV xs))
supp-ctx-inc-FV (ewt xs) = trans (cong (_∪ ewt empty) (supp-lift-sub (supp-ctx-inc xs))) (cong ewt (trans (∪-right-unit (FVSub (supp-ctx-inc xs))) (supp-ctx-inc-FV xs)))


supp-ctx : (Γ : Ctx n) → (xs : VarSet n) → .(is-DC Γ xs) → Ctx (VarSet-size xs)
supp-ctx ∅ emp dc = ∅
supp-ctx (Γ , A) (ewf xs) dc = supp-ctx Γ xs dc
supp-ctx (Γ , A) (ewt xs) dc = (supp-ctx Γ xs (proj₁ dc)) , subctx-inc-ty A (supp-ctx-inc xs) ⦃ supp-ctx-inc-v2v xs ⦄ (⊆-trans (proj₂ dc) (⊆-reflexive (sym (supp-ctx-inc-FV xs))))

VarSet-NonEmpty : (xs : VarSet n) → Set
VarSet-NonEmpty emp = ⊥
VarSet-NonEmpty (ewf xs) = VarSet-NonEmpty xs
VarSet-NonEmpty (ewt xs) = ⊤

susp-supp-drop : (xs : VarSet n) → .⦃ VarSet-NonEmpty xs ⦄ → suspSupp (drop xs) ≡ drop (suspSupp xs)
susp-supp-drop (ewf xs) = cong ewf (susp-supp-drop xs)
susp-supp-drop (ewt xs) = refl

pdb-bd-supp-non-empty : (n : ℕ) → (Γ : Ctx m) → (pdb : Γ ⊢pdb) → (b : Bool) → VarSet-NonEmpty (pdb-bd-supp n Γ pdb b)
pdb-bd-supp-non-empty n ∅ pdb b = ⊥-elim (pdb-odd-length pdb)
pdb-bd-supp-non-empty n (∅ , A) pdb b = tt
pdb-bd-supp-non-empty n (Γ , B , A) pdb b with <-cmp n (ty-dim B) | b
... | tri< a ¬b ¬c | b = pdb-bd-supp-non-empty n Γ (pdb-prefix pdb) b
... | tri≈ ¬a b₁ ¬c | false = pdb-bd-supp-non-empty n Γ (pdb-prefix pdb) false
... | tri≈ ¬a b₁ ¬c | true = tt
... | tri> ¬a ¬b c | b = tt

VarSet-NonEmpty-Special : (xs : VarSet n) → Set
VarSet-NonEmpty-Special {zero} xs = ⊥
VarSet-NonEmpty-Special {suc zero} xs = ⊥
VarSet-NonEmpty-Special {suc (suc n)} (ewf xs) = VarSet-NonEmpty-Special xs
VarSet-NonEmpty-Special {suc (suc n)} (ewt xs) = ⊤

connect-drop : (xs : VarSet (suc n)) → (ys : VarSet (suc m)) → .⦃ VarSet-NonEmpty-Special ys ⦄ → connect-supp xs (drop ys) ≡ drop (connect-supp xs ys)
connect-drop xs (ewf (y ∷ ys)) = cong ewf (connect-drop xs (y ∷ ys))
connect-drop xs (ewt (y ∷ ys)) = refl

pdb-bd-supp-non-empty-special : (n : ℕ) → (Γ : Ctx (suc m)) → (pdb : Γ ⊢pdb) → (b : Bool) → .⦃ NonZero′ m ⦄ → VarSet-NonEmpty-Special (pdb-bd-supp (suc n) Γ pdb b)
pdb-bd-supp-non-empty-special n (∅ , B , A) pdb b = ⊥-elim (pdb-odd-length pdb)
pdb-bd-supp-non-empty-special n (Γ , C , B , A) pdb b with <-cmp (suc n) (ty-dim B) | b
... | tri< a ¬b ¬c | b = pdb-bd-supp-non-empty-special n (Γ , C) (pdb-prefix pdb) b ⦃ focus-ty-dim-to-non-empty (pdb-prefix pdb) (≤-trans (≤-trans (s≤s z≤n) a) (≤-reflexive (ty-dim-≃ (pdb-proj₁ pdb)))) ⦄
... | tri≈ ¬a b₁ ¬c | false = pdb-bd-supp-non-empty-special n (Γ , C) (pdb-prefix pdb) false ⦃ focus-ty-dim-to-non-empty (pdb-prefix pdb) (≤-trans (≤-trans (s≤s z≤n) (≤-reflexive b₁)) (≤-reflexive (ty-dim-≃ (pdb-proj₁ pdb)))) ⦄
... | tri≈ ¬a b₁ ¬c | true = tt
... | tri> ¬a ¬b c | b = tt

susp-pdb-bd-compat : (n : ℕ)
                   → (Γ : Ctx m)
                   → (pdb : Γ ⊢pdb)
                   → (b : Bool)
                   → suspSupp (pdb-bd-supp n Γ pdb b) ≡ pdb-bd-supp (suc n) (suspCtx Γ) (susp-pdb pdb) b
susp-pdb-bd-compat n ∅ pdb b = ⊥-elim′ (pdb-odd-length pdb)
susp-pdb-bd-compat n (∅ , A) pdb b = refl
susp-pdb-bd-compat n (Γ , B , A) pdb b with <-cmp n (ty-dim B) | <-cmp (suc n) (ty-dim (suspTy B)) | b
... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ | b = cong ewf (cong ewf (susp-pdb-bd-compat n Γ (pdb-prefix pdb) b))
... | tri< a ¬b ¬c | tri≈ ¬a b₁ ¬c₁ | b = ⊥-elim (¬a (<-transʳ a (<-transˡ (n<1+n (ty-dim B)) (≤-reflexive (sym (susp-dim B))))))
... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c | b = ⊥-elim (¬a (<-transʳ a (<-transˡ (n<1+n (ty-dim B)) (≤-reflexive (sym (susp-dim B))))))
... | tri≈ ¬a b₁ ¬c | tri< a ¬b ¬c₁ | b = ⊥-elim (¬b (trans (cong suc b₁) (sym (susp-dim B))))
... | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ | false = cong ewf (cong ewf (susp-pdb-bd-compat n Γ (pdb-prefix pdb) false))
... | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ | true = cong ewf (cong ewt (trans (susp-supp-drop (pdb-bd-supp n Γ (pdb-prefix pdb) true) ⦃ pdb-bd-supp-non-empty n Γ (pdb-prefix pdb) true ⦄) (cong drop (susp-pdb-bd-compat n Γ (pdb-prefix pdb) true))))
... | tri≈ ¬a b₁ ¬c | tri> ¬a₁ ¬b c | b = ⊥-elim (¬b (trans (cong suc b₁) (sym (susp-dim B))))
... | tri> ¬a ¬b c | tri< a ¬b₁ ¬c | b = ⊥-elim (¬c (s≤s (≤-trans (≤-reflexive (susp-dim B)) c)))
... | tri> ¬a ¬b c | tri≈ ¬a₁ b₁ ¬c | b = ⊥-elim (¬c (s≤s (≤-trans (≤-reflexive (susp-dim B)) c)))
... | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ | b = cong ewt (cong ewt (susp-pdb-bd-compat n Γ (pdb-prefix pdb) b))

susp-pd-bd-compat : (n : ℕ)
                  → (Γ : Ctx m)
                  → (pd : Γ ⊢pd)
                  → (b : Bool)
                  → suspSupp (pd-bd-supp n Γ pd b) ≡ pdb-bd-supp (suc n) (suspCtx Γ) (susp-pdb (pd-to-pdb pd)) b
susp-pd-bd-compat n Γ (Finish pdb) b = susp-pdb-bd-compat n Γ pdb b

connect-susp-pdb-bd-compat : (n : ℕ)
                      → (Γ : Ctx (suc m))
                      → (pd : Γ ⊢pd)
                      → (Δ : Ctx (suc l))
                      → (pdb : Δ ⊢pdb)
                      → (b : Bool)
                      → connect-supp (suspSupp (pd-bd-supp n Γ pd b)) (pdb-bd-supp (suc n) Δ pdb b) ≡ pdb-bd-supp (suc n) (connect-susp Γ Δ) (connect-susp-pdb pd pdb) b
connect-susp-pdb-bd-compat n Γ pd (∅ , A) pdb b = susp-pd-bd-compat n Γ pd b
connect-susp-pdb-bd-compat n Γ pd (∅ , B , A) pdb b = ⊥-elim (pdb-odd-length pdb)
connect-susp-pdb-bd-compat n Γ pd (Δ , C , B , A) pdb b with <-cmp (suc n) (ty-dim B) | <-cmp (suc n) (ty-dim (B [ connect-susp-inc-right (pred (ctxLength Γ)) _ ]ty)) | b
... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ | b = cong ewf (cong ewf (connect-susp-pdb-bd-compat n Γ pd (Δ , C) (pdb-prefix pdb) b))
... | tri< a ¬b ¬c | tri≈ ¬a b₁ ¬c₁ | b = ⊥-elim (¬a (<-transˡ a (≤-reflexive (sub-dim (connect-susp-inc-right _ _) B))))
... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c | b = ⊥-elim ((¬a (<-transˡ a (≤-reflexive (sub-dim (connect-susp-inc-right _ _) B)))))
... | tri≈ ¬a b₁ ¬c | tri< a ¬b ¬c₁ | b = ⊥-elim (¬b (trans b₁ (sub-dim (connect-susp-inc-right _ _) B)))
... | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ | false = cong ewf (cong ewf (connect-susp-pdb-bd-compat n Γ pd (Δ , C) (pdb-prefix pdb) false))
... | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ | true = cong ewf (cong ewt (trans (connect-drop (suspSupp (pd-bd-supp n Γ pd true)) (pdb-bd-supp (suc n) (Δ , C) _ true) ⦃ pdb-bd-supp-non-empty-special n (Δ , C) (pdb-prefix pdb) true ⦃ focus-ty-dim-to-non-empty (pdb-prefix pdb) (≤-trans (≤-trans (s≤s z≤n) (≤-reflexive b₁)) (≤-reflexive (ty-dim-≃ (pdb-proj₁ pdb)))) ⦄ ⦄) (cong drop (connect-susp-pdb-bd-compat n Γ pd (Δ , C) (pdb-prefix pdb) true))))
... | tri≈ ¬a b₁ ¬c | tri> ¬a₁ ¬b c | b = ⊥-elim (¬b (trans b₁ (sub-dim (connect-susp-inc-right _ _) B)))
... | tri> ¬a ¬b c | tri< a ¬b₁ ¬c | b = ⊥-elim (¬c (<-transʳ (≤-reflexive (sym (sub-dim (connect-susp-inc-right _ _) B))) c))
... | tri> ¬a ¬b c | tri≈ ¬a₁ b₁ ¬c | b = ⊥-elim (¬c (<-transʳ (≤-reflexive (sym (sub-dim (connect-susp-inc-right _ _) B))) c))
... | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ | b = cong ewt (cong ewt (connect-susp-pdb-bd-compat n Γ pd (Δ , C) (pdb-prefix pdb) b))

connect-susp-pd-bd-compat : (n : ℕ)
                      → (Γ : Ctx (suc m))
                      → (pd : Γ ⊢pd)
                      → (Δ : Ctx (suc l))
                      → (pd2 : Δ ⊢pd)
                      → (b : Bool)
                      → connect-supp (suspSupp (pd-bd-supp n Γ pd b)) (pd-bd-supp (suc n) Δ pd2 b) ≡ pd-bd-supp (suc n) (connect-susp Γ Δ) (connect-susp-pd pd pd2) b
connect-susp-pd-bd-compat n Γ pd Δ (Finish pdb) b = connect-susp-pdb-bd-compat n Γ pd Δ pdb b

drop-var : (t : Tm n) → .⦃ isVar t ⦄ → drop (FVTm t) ≡ empty
drop-var (Var zero) = refl
drop-var (Var (suc i)) = cong ewf (drop-var (Var i))

supp-compat : (n : ℕ) → (T : Tree m) → (b : Bool) → supp-bd n T b ≡ pd-bd-supp n (tree-to-ctx T) (tree-to-pd T) b
supp-compat zero T false = lem (tree-to-ctx T) (pd-to-pdb (tree-to-pd T))
  where
    lem : (Γ : Ctx (suc m)) → (pdb : Γ ⊢pdb) → trueAt (fromℕ m) ≡ pdb-bd-supp zero Γ pdb false
    lem (∅ , A) pdb = refl
    lem (∅ , B , A) pdb = ⊥-elim (pdb-odd-length pdb)
    lem (Γ , C , B , A) pdb with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = cong ewf (cong ewf (lem (Γ , C) (pdb-prefix pdb)))
    ... | tri≈ ¬a b ¬c = cong ewf (cong ewf (lem (Γ , C) (pdb-prefix pdb)))
supp-compat zero T true = begin
  FVTm (tree-last-var T)
    ≡˘⟨ FVTm-≃ (tree-to-pd-focus-tm T) ⟩
  FVTm (pd-focus-tm (tree-to-pd T))
    ≡˘⟨ FVTm-≃ (pd-right-base (tree-to-pd T)) ⟩
  FVTm (pdb-right-base (pd-to-pdb (tree-to-pd T)))
    ≡⟨ lem (tree-to-ctx T) (pd-to-pdb (tree-to-pd T)) ⟩
  pd-bd-supp zero (tree-to-ctx T) (tree-to-pd T) true ∎
  where
    open ≡-Reasoning

    lem : (Γ : Ctx (suc m)) → (pdb : Γ ⊢pdb) → FVTm (pdb-right-base pdb) ≡ pdb-bd-supp zero Γ pdb true
    lem (∅ , .⋆) Base = refl
    lem (∅ , A) (Restr pdb) = ⊥-elim (NonZero′-⊥ (≤-trans (pdb-dim-lem pdb) (≤-reflexive (ty-dim-≃ (pdb-singleton-lem pdb)))))
    lem (∅ , B , A) pdb = ⊥-elim (pdb-odd-length pdb)
    lem (Γ , C , B , A) pdb with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = begin
      FVTm (pdb-right-base pdb)
        ≡⟨ FVTm-≃ (pdb-right-base-prefix pdb a) ⟩
      FVTm (liftTerm (liftTerm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ supp-lift-tm (liftTerm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (FVTm (liftTerm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ cong ewf (supp-lift-tm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (ewf (FVTm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ cong ewf (cong ewf (lem (Γ , C) (pdb-prefix pdb))) ⟩
      ewf (ewf (pdb-bd-supp 0 (Γ , C) _ true)) ∎
        where open ≡-Reasoning
    ... | tri≈ ¬a b ¬c = begin
      FVTm (pdb-right-base pdb)
        ≡⟨ FVTm-≃ (pdb-right-base-0-dim pdb (sym b)) ⟩
      FVTm 1V
        ≡˘⟨ cong ewf (cong ewt (drop-var (pdb-right-base (pdb-prefix pdb)) ⦃ pdb-right-base-isVar (pdb-prefix pdb) ⦄)) ⟩
      ewf (ewt (drop (FVTm (pdb-right-base (pdb-prefix pdb)))))
        ≡⟨ cong ewf (cong ewt (cong drop (lem (Γ , C) (pdb-prefix pdb)))) ⟩
      ewf (ewt (drop (pdb-bd-supp 0 (Γ , C) _ true))) ∎
        where open ≡-Reasoning
supp-compat (suc n) Sing b = refl
supp-compat (suc n) (Join S T) b = begin
  connect-supp (suspSupp (supp-bd n S b)) (supp-bd (suc n) T b)
    ≡⟨ cong₂ (λ a b → connect-supp (suspSupp a) b) (supp-compat n S b) (supp-compat (suc n) T b) ⟩
  connect-supp
    (suspSupp (pd-bd-supp n (tree-to-ctx S) (tree-to-pd S) b))
    (pd-bd-supp (suc n) (tree-to-ctx T) (tree-to-pd T) b)
    ≡⟨ connect-susp-pd-bd-compat n (tree-to-ctx S) (tree-to-pd S) (tree-to-ctx T) (tree-to-pd T) b ⟩
  pd-bd-supp (suc n) (connect-susp (tree-to-ctx S) (tree-to-ctx T))
      (connect-susp-pd (tree-to-pd S) (tree-to-pd T)) b ∎
  where
    open ≡-Reasoning
