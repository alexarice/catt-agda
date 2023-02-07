module Catt.Syntax.Equality where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax

data SETS : Set₁ where
  Base : (X : Set) → SETS
  Arg : (A : Set) → (X : A → SETS) → SETS

ELEM : SETS → Set
ELEM (Base X) = X
ELEM (Arg A X) = Σ[ a ∈ A ] ELEM (X a)

applyₑ : ∀ {ℓ} → (X : SETS) → (ELEM X → Set ℓ) → Set ℓ
applyₑ (Base X) Y = (x : X) → Y x
applyₑ (Arg A X) Y = {a : A} → applyₑ (X a) (Y ∘ (a ,,_))

curryₑ : ∀ {ℓ} → {X : SETS} → {Y : ELEM X → Set ℓ} → (f : (e : ELEM X) → Y e) → applyₑ X Y
curryₑ {X = Base X} f = f
curryₑ {X = Arg A X} f {a} = curryₑ (f ∘ (a ,,_))

Eq : (X : SETS) → (a b : ELEM X) → Set
Eq (Base X) a b = a ≡ b
Eq (Arg A X) (a ,, x) (b ,, y) = Σ (a ≡ b) λ where refl → Eq (X a) x y

TY : SETS
TY = Arg ℕ (Base ∘ Ty)

-- ⌊_⌋<_> :
-- ⌊_⌋<_>

_≃ty_ : Ty n → Ty m → Set
A ≃ty B = Eq TY (_ ,, A) (_ ,, B)

refl≃ : {X : SETS} → {a : ELEM X} → Eq X a a
refl≃ {X = Base X} {a = a} = refl
refl≃ {X = Arg A X} {a = a ,, x} = refl ,, refl≃

refl≃ty : A ≃ty A
refl≃ty = refl≃

{-
SETS : ℕ → Set₁
SETS zero = Set
SETS (suc n) = Σ Set (λ S → ∀ (x : S) → SETS n)

ELEMS′ : SETS n → Set
ELEMS′ {zero} X = X
ELEMS′ {suc n} (X ,, Y) = Σ[ x ∈ X ] ELEMS′ (Y x)



record ELEMS : Set where
  constructor
ELEMS = Wrap (λ X → ELEMS X)

applys : ∀ {ℓ} → (X : SETS n) → (ELEMS n X → Set ℓ) → Set ℓ
applys {zero} X Y = (x : X) → Y x
applys {suc n} (A ,, X) Y = {a : A} → applys (X a) λ x → Y (a ,, x)

currys : ∀ {n} {ℓ} → {X : SETS n} → {Y : ELEMS n X → Set ℓ} → (f : (e : ELEMS n X) → Y e) → applys X Y
currys {zero} f = f
currys {suc n} {X = A ,, X} f {a} = currys (f ∘ (a ,,_))

⌊_⌋ : {X : SETS n} → applys X λ _ → ELEMS n X
⌊_⌋ = currys (λ e → e)

applysi : ∀ {ℓ} → (X : SETS n) → (ELEMS n X → Set ℓ) → Set ℓ
applysi {zero} X Y = {x : X} → Y x
applysi {suc n} (A ,, X) Y = {a : A} → applysi (X a) λ x → Y (a ,, x)

currysi : ∀ {n} {ℓ} → {X : SETS n} → {Y : ELEMS n X → Set ℓ} → (f : (e : ELEMS n X) → Y e) → applysi X Y
currysi {zero} f {x} = f x
currysi {suc n} {X = A ,, X} f {a} = currysi (f ∘ (a ,,_))

Eq : (X : SETS n) → (a b : ELEMS n X) → Set
Eq {zero} X a b = a ≡ b
Eq {suc n} (A ,, X) (a ,, x) (b ,, y) = Σ (a ≡ b) (λ where refl → Eq (X a) x y)

refl≃ : {X : SETS n} → {a : ELEMS n X} → Eq X a a
refl≃ {zero} {a = a} = refl
refl≃ {suc n} {a = a ,, x} = refl ,, refl≃

sym≃ : {X : SETS n} → {a b : ELEMS n X} → Eq X a b → Eq X b a
sym≃ {zero} p = sym p
sym≃ {suc n} (refl ,, p) = refl ,, sym≃ p

trans≃ : {X : SETS n} → {a b c : ELEMS n X} → Eq X a b → Eq X b c → Eq X a c
trans≃ {zero} p q = trans p q
trans≃ {suc n} (refl ,, p) (refl ,, q) = refl ,, (trans≃ p q)

TY : SETS 1
TY = ℕ ,, Ty

_≃ty_ : Ty n → Ty m → Set
A ≃ty B = Eq TY ⌊ A ⌋ ⌊ B ⌋
-}
-- refl≃ty : A ≃ty A
-- refl≃ty = EqRefl

-- sym≃ty : A ≃ty B → B ≃ty A
-- sym≃ty p = EqSym p

-- _≃_ : {X : SETS n} → applys X λ _ → applys X (λ _ → Set)
-- _≃_ {X = X} = currys (λ x → currys (λ y → Eq X x y))

-- refl≃ : {X : SETS n} → applysi X λ x → Eq X x x
-- refl≃ = currysi (λ e → ⌊ EqRefl e ⌋)

-- TY : SETS 1
-- TY = ℕ ,, Ty

-- _≃ty_ : ∀ {n} → Ty n → ∀ {m} → Ty m → Set
-- _≃ty_ = _≃_ {X = TY}

-- refl≃ty : A ≃ty A
-- refl≃ty {A = A} = refl≃ {X = ?}
