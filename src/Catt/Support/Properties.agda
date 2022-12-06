{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Support.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Support
open import Catt.Variables
open import Relation.Binary
open import Tactic.MonoidSolver
open import Algebra.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using (Pointwise)
open import Data.Sum
open import Catt.Globular
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Connection
open import Catt.Connection.Pasting
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Pasting
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

  ∪-isMonoid : IsMonoid _∪_ empty
  ∪-isMonoid = record
    { isSemigroup = ∪-isSemigroup
    ; identity = ∪-left-unit ,, ∪-right-unit
    }

  ∪-isCommutativeMonoid : IsCommutativeMonoid _∪_ empty
  ∪-isCommutativeMonoid = record
    { isMonoid = ∪-isMonoid
    ; comm = ∪-comm
    }

  ∪-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _∪_ empty
  ∪-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ∪-isCommutativeMonoid
    ; idem = ∪-idem
    }

  ∪-monoid : Monoid _ _
  ∪-monoid = record
    { isMonoid = ∪-isMonoid }

  ∪-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  ∪-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = ∪-isIdempotentCommutativeMonoid
    }

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
TransportVarSet-sub : (τ : Sub l n A) → (σ : Sub n m ⋆) → TransportVarSet (FVSub τ) σ ≡ FVSub (σ ● τ)

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

TransportVarSet-comp : (xs : VarSet l) → (σ : Sub n m ⋆) → (τ : Sub l n ⋆) → TransportVarSet xs (σ ● τ) ≡ TransportVarSet (TransportVarSet xs τ) σ
TransportVarSet-comp emp σ ⟨⟩ = sym (TransportVarSet-empty σ)
TransportVarSet-comp (ewf xs) σ ⟨ τ , t ⟩ = TransportVarSet-comp xs σ τ
TransportVarSet-comp (ewt xs) σ ⟨ τ , t ⟩ = begin
  TransportVarSet xs (σ ● τ) ∪ FVTm (t [ σ ]tm)
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

coh-sub-fv : (Γ : Ctx (suc n)) → (A : Ty (suc n)) → (σ : Sub (suc n) m B) → FVTm (Coh Γ A idSub [ σ ]tm) ≡ FVSub σ
coh-sub-fv {B = ⋆} Γ A σ = FVSub-≃ (id-right-unit σ)
coh-sub-fv {B = s ─⟨ B ⟩⟶ t} Γ A σ = begin
  FVTm (Coh (suspCtx Γ) (suspTy A) (suspSub idSub) [ unrestrict σ ]tm)
    ≡⟨ FVTm-≃ (sub-action-≃-tm (Coh≃ (refl≃c {Γ = suspCtx Γ}) refl≃ty susp-functorial-id) (refl≃s {σ = unrestrict σ})) ⟩
  FVTm (Coh (suspCtx Γ) (suspTy A) idSub [ unrestrict σ ]tm)
    ≡⟨ coh-sub-fv (suspCtx Γ) (suspTy A) (unrestrict σ) ⟩
  FVSub (unrestrict σ)
    ≡⟨ unrestrict-supp σ ⟩
  FVSub σ ∎
  where
    open ≡-Reasoning

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
build-⊆-1 x p = cong₂ _∷_ (sym (∨-identityʳ x)) p

build-⊆-2 : (x : Bool) → {xs ys : VarSet n} → xs ⊆ ys → (x ∷ xs) ⊆ ewt ys
build-⊆-2 x p = cong ewt p

debuild-⊆-2 : {x y : Bool} → {xs ys : VarSet n} → (x ∷ xs) ⊆ (y ∷ ys) → xs ⊆ ys
debuild-⊆-2 p = cong tail p


FVTy-comp-⊆ : (A : Ty n) → (σ : Sub n m B) → FVTy (A [ σ ]ty) ⊆ FVSub σ
FVTm-comp-⊆ : (t : Tm n) → (σ : Sub n m A) → FVTm (t [ σ ]tm) ⊆ FVSub σ
FVSub-comp-⊆ : (σ : Sub n m A) → (τ : Sub l n ⋆) → FVSub (σ ● τ) ⊆ FVSub σ

FVTy-comp-⊆ ⋆ σ = sub-type-⊆ σ
FVTy-comp-⊆ (s ─⟨ A ⟩⟶ t) σ = ∪-⊆ (∪-⊆ (FVTy-comp-⊆ A σ) (FVTm-comp-⊆ s σ)) (FVTm-comp-⊆ t σ)

FVTm-comp-⊆ (Var zero) ⟨ σ , t ⟩ = ∪-⊆-2 (FVSub σ) (FVTm t)
FVTm-comp-⊆ (Var (suc i)) ⟨ σ , t ⟩ = ⊆-trans (FVTm-comp-⊆ (Var i) σ) (∪-⊆-1 (FVSub σ) (FVTm t))
FVTm-comp-⊆ {A = ⋆} (Coh S B τ) σ = FVSub-comp-⊆ σ τ
FVTm-comp-⊆ {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) σ = begin
  FVTm
      (Coh (suspCtx Δ) (suspTy B) (suspSub τ) [ unrestrict σ ]tm)
    ≤⟨ FVTm-comp-⊆ (Coh (suspCtx Δ) (suspTy B) (suspSub τ)) (unrestrict σ) ⟩
  FVSub (unrestrict σ)
    ≡⟨ unrestrict-supp σ ⟩
  FVSub σ ∎
  where
    open PReasoning (⊆-poset _)

FVSub-comp-⊆ σ ⟨⟩ = sub-type-⊆ σ
FVSub-comp-⊆ σ ⟨ τ , t ⟩ = begin
  FVSub (σ ● τ) ∪ FVTm (t [ σ ]tm)
    ≤⟨ ⊆-cong-∪-1 (FVTm-comp-⊆ t σ) ⟩
  FVSub (σ ● τ) ∪ FVSub σ
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

DC-is-DC : (Γ : Ctx n) → (xs : VarSet n) → is-DC Γ (DC Γ xs)
DC-is-DC ∅ emp = tt
DC-is-DC (Γ , A) (ewf xs) = DC-is-DC Γ xs
DC-is-DC (Γ , A) (ewt xs) = (DC-is-DC Γ (xs ∪ FVTy A)) ,, ⊆-trans (∪-⊆-2 xs (FVTy A)) (DC-⊆ Γ (xs ∪ FVTy A))

drop-var : (t : Tm n) → .⦃ isVar t ⦄ → drop (FVTm t) ≡ empty
drop-var (Var 0F) = refl
drop-var (Var (suc i)) = cong ewf (drop-var (Var i))

DC-fromℕ : (Γ : Ctx (suc n)) → SuppTm Γ (Var (fromℕ n)) ≡ trueAt (fromℕ n)
DC-fromℕ {n = zero} (∅ , A) = refl
DC-fromℕ {n = suc n} (Γ , A) = cong ewf (DC-fromℕ Γ)

DC-cong-⊆ : (Γ : Ctx n) → {xs ys : VarSet n} → xs ⊆ ys → DC Γ xs ⊆ DC Γ ys
DC-cong-⊆ Γ {xs} {ys} p = begin
  DC Γ ys
    ≡⟨ cong (DC Γ) p ⟩
  DC Γ (ys ∪ xs)
    ≡⟨ DC-cup Γ ys xs ⟩
  DC Γ ys ∪ DC Γ xs ∎
  where
    open ≡-Reasoning
