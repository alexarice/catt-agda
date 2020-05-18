{-# OPTIONS --safe --without-K #-}

module Catt.Syntax.Equality where

open import Catt.Syntax
open import Catt.Fin
open import Level using (Level; 0ℓ)
open import Data.Nat
open import Catt.Vec.Functional
open import Catt.Vec.Functional.Pointwise
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

infix 4 _≡ctx_ _≡ty_ _≡tm_ _≡sub_
_≡ctx_ : ∀ {n} → Rel (Ctx n) 0ℓ
data _≡ty_ : ∀ {n} → Rel (Ty n) 0ℓ
data _≡tm_ : ∀ {n} → Rel (Term n) 0ℓ
_≡sub_ : ∀ {n m} → Rel (Sub n m) 0ℓ

Γ ≡ctx Δ = Pointwise _≡ty_ Γ Δ
data _≡ty_ where
  Star≡ : ∀ {n} → (⋆ {n}) ≡ty ⋆
  Arr≡ : ∀ {n t t′ u u′ A A′} → t ≡tm t′ → _≡ty_ {n} A A′ → u ≡tm u′ → t ─⟨ A ⟩⟶ u ≡ty t′ ─⟨ A′ ⟩⟶ u′

data _≡tm_ where
  Var≡ : ∀ {n i i′} → i ≡ i′ → Var {n} i ≡tm Var i′
  Coh≡ : ∀ {n m Γ Γ′ A A′ σ σ′} → _≡ctx_ {n} Γ Γ′ → A ≡ty A′ → _≡sub_ {m} σ σ′ → Coh Γ A σ ≡tm Coh Γ′ A′ σ′

σ ≡sub τ = Pointwise _≡tm_ σ τ

-- Properties

liftType-cong : ∀ {n} {A A′ : Ty n} → A ≡ty A′ → liftType A ≡ty liftType A′
liftTerm-cong : ∀ {n} {t t′ : Term n} → t ≡tm t′ → liftTerm t ≡tm liftTerm t′
liftSub-cong : ∀ {n} {m} {σ σ′ : Sub m n} → σ ≡sub σ′ → liftSub σ ≡sub liftSub σ′

liftType-cong Star≡ = Star≡
liftType-cong (Arr≡ p q r) = Arr≡ (liftTerm-cong p) (liftType-cong q) (liftTerm-cong r)

liftTerm-cong (Var≡ P.refl) = Var≡ P.refl
liftTerm-cong (Coh≡ p q r) = Coh≡ p q (liftSub-cong r)

liftSub-cong p i = liftTerm-cong (p i)

‼-cong : ∀ {n} {Γ Γ′ : Ctx n} → Γ ≡ctx Γ′ → (i : Fin n) → Γ ‼ i ≡ty Γ′ ‼ i
‼-cong {suc n} p (fromℕ .n) = liftType-cong (p (fromℕ n))
‼-cong {suc n} {Γ} {Γ′} p (inject i) = liftType-cong (‼-cong {n} {front Γ} {front Γ′} (λ m → p (inject m)) i)

ctx-refl : ∀ {n} → Reflexive {A = Ctx n} _≡ctx_
tm-refl : ∀ {n} → Reflexive {A = Term n} _≡tm_
ty-refl : ∀ {n} → Reflexive {A = Ty n} _≡ty_
sub-refl : ∀ {m} {n} → Reflexive {A = Sub m n} _≡sub_

ctx-refl i = ty-refl

tm-refl {n} {Var x} = Var≡ P.refl
tm-refl {n} {Coh Γ A σ} = Coh≡ ctx-refl ty-refl sub-refl


ty-refl {n} {⋆} = Star≡
ty-refl {n} {t ─⟨ A ⟩⟶ u} = Arr≡ tm-refl ty-refl tm-refl

sub-refl i = tm-refl

ctx-sym : ∀ {n} → Symmetric {A = Ctx n} _≡ctx_
tm-sym : ∀ {n} → Symmetric {A = Term n} _≡tm_
ty-sym : ∀ {n} → Symmetric {A = Ty n} _≡ty_
sub-sym : ∀ {m n} → Symmetric {A = Sub m n} _≡sub_

ctx-sym s i = ty-sym (s i)

tm-sym (Var≡ p) = Var≡ (P.sym p)
tm-sym (Coh≡ p q r) = Coh≡ (ctx-sym p) (ty-sym q) (sub-sym r)

ty-sym Star≡ = Star≡
ty-sym (Arr≡ p q r) = Arr≡ (tm-sym p) (ty-sym q) (tm-sym r)

sub-sym s i = tm-sym (s i)

ctx-trans : ∀ {n} → Transitive {A = Ctx n} _≡ctx_
tm-trans : ∀ {n} → Transitive {A = Term n} _≡tm_
ty-trans : ∀ {n} → Transitive {A = Ty n} _≡ty_
sub-trans : ∀ {m n} → Transitive {A = Sub m n} _≡sub_

ctx-trans p q i = ty-trans (p i) (q i)

tm-trans (Var≡ p) (Var≡ p′) = Var≡ (P.trans p p′)
tm-trans (Coh≡ p q r) (Coh≡ p′ q′ r′) = Coh≡ (ctx-trans p p′) (ty-trans q q′) (sub-trans r r′)

ty-trans Star≡ Star≡ = Star≡
ty-trans (Arr≡ p q r) (Arr≡ p′ q′ r′) = Arr≡ (tm-trans p p′) (ty-trans q q′) (tm-trans r r′)

sub-trans p q  i = tm-trans (p i) (q i)

-- Equivalences

ctx-isEquiv : ∀ {n} → IsEquivalence {A = Ctx n} _≡ctx_
ctx-isEquiv = record
  { refl = ctx-refl
  ; sym = ctx-sym
  ; trans = ctx-trans
  }

ty-isEquiv : ∀ {n} → IsEquivalence {A = Ty n} _≡ty_
ty-isEquiv = record
  { refl = ty-refl
  ; sym = ty-sym
  ; trans = ty-trans
  }

tm-isEquiv : ∀ {n} → IsEquivalence {A = Term n} _≡tm_
tm-isEquiv = record
  { refl = tm-refl
  ; sym = tm-sym
  ; trans = tm-trans
  }

sub-isEquiv : ∀ {n m} → IsEquivalence {A = Sub n m} _≡sub_
sub-isEquiv = record
  { refl = sub-refl
  ; sym = sub-sym
  ; trans = sub-trans
  }

-- Setoids

ctx-setoid : ℕ → Setoid 0ℓ 0ℓ
ctx-setoid n = record
  { Carrier = Ctx n
  ; _≈_ = _≡ctx_
  ; isEquivalence = ctx-isEquiv
  }

ty-setoid : ℕ → Setoid 0ℓ 0ℓ
ty-setoid n = record
  { Carrier = Ty n
  ; _≈_ = _≡ty_
  ; isEquivalence = ty-isEquiv
  }

tm-setoid : ℕ → Setoid 0ℓ 0ℓ
tm-setoid n = record
  { Carrier = Term n
  ; _≈_ = _≡tm_
  ; isEquivalence = tm-isEquiv
  }

sub-setoid : ℕ → ℕ → Setoid 0ℓ 0ℓ
sub-setoid n m = record
  { Carrier = Sub n m
  ; _≈_ = _≡sub_
  ; isEquivalence = sub-isEquiv
  }
