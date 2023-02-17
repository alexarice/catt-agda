module Catt.Syntax.Equality where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax

data Sets : Set₁ where
  End : (X : Set) → Sets
  Arg : (A : Set) → (X : A → Sets) → Sets

Base : Sets → Set
Base (End X) = ⊤
Base (Arg A X) = Σ[ a ∈ A ] Base (X a)

Elem : {X : Sets} → (b : Base X) → Set
Elem {End X} b = X
Elem {Arg A X} (x ,, b) = Elem b

Eq : (X : Sets) → {b b′ : Base X} → (a : Elem b) → (a′ : Elem b′) → Set
Eq (End X) a b = a ≡ b
Eq (Arg A X) {b = x ,, b} {b′ = y ,, b′} a a′ = Σ (x ≡ y) λ where refl → Eq (X x) a a′

CTX : Sets
CTX = Arg ℕ (End ∘ Ctx)

TY : Sets
TY = Arg ℕ (End ∘ Ty)

TM : Sets
TM = Arg ℕ (End ∘ Tm)

SUB : Sets
SUB = Arg ℕ λ n → Arg ℕ λ m → Arg (Ty m) (End ∘ Sub n m)

refl≃ : {X : Sets} → {b : Base X} → {x : Elem b} → Eq X x x
refl≃ {End X} = refl
refl≃ {Arg A X} = refl ,, refl≃

sym≃ : {X : Sets} → {b b′ : Base X} → {x : Elem b} → {y : Elem b′} → Eq X x y → Eq X y x
sym≃ {End X} p = sym p
sym≃ {Arg A X} (refl ,, p) = refl ,, sym≃ p

trans≃ : {X : Sets} → {b b′ b″ : Base X} → {x : Elem b} → {y : Elem b′} → {z : Elem b″} → Eq X x y → Eq X y z → Eq X x z
trans≃ {End X} p q = trans p q
trans≃ {Arg A X} (refl ,, p) (refl ,, q) = refl ,, (trans≃ p q)

setoid≃ : (X : Sets) → Setoid _ _
setoid≃ X = record { Carrier = Σ[ b ∈ Base X ] Elem b
                   ; _≈_ = λ x y → Eq X (proj₂ x) (proj₂ y)
                   ; isEquivalence = record { refl = refl≃
                                            ; sym = sym≃
                                            ; trans = trans≃
                                            }
                   }

_≃ty_ : Ty n → Ty m → Set
_≃ty_ = Eq TY

_≃tm_ : Tm n → Tm m → Set
_≃tm_ = Eq TM

_≃c_ : Ctx n → Ctx m → Set
_≃c_ = Eq CTX

_≃s_ : Sub n m A → Sub n′ m′ B → Set
_≃s_ = Eq SUB

<_> : {X : Sets} → {b : Base X} → (e : Elem b) → Σ[ b ∈ Base X ] Elem b
<_> {X} {b} e = b ,, e

J≃ : {X : Sets}
   → {b : Base X}
   → {e : Elem b}
   → (P : {b′ : Base X} → (e′ : Elem b′) → Eq X e e′ → Set)
   → (r : P e refl≃)
   → {b′ : Base X}
   → {e′ : Elem b′}
   → (p : Eq X e e′)
   → P e′ p
J≃ {End X} P r refl = r
J≃ {Arg A X} {b ,, _} P r (refl ,, p) = J≃ {X b} (λ e x → P e (refl ,, x)) r p

cong≃ : {X Y : Sets} → {f : Base X → Base Y} → (g : {b : Base X} → Elem b → Elem (f b)) → {b b′ : Base X} → {e : Elem b} → {e′ : Elem b′} → Eq X e e′ → Eq Y (g e) (g e′)
cong≃ {X} {Y} g {e = e} p = J≃ (λ e′ x → Eq Y (g e) (g e′)) refl≃ p
