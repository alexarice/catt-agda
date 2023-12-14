module Catt.Syntax.Complexity where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular

open import Data.List
open import Relation.Binary
open import Induction.WellFounded
import Data.Nat.Induction as I
open import Algebra.Bundles

Ordinal : Set
Ordinal = List ℕ

infix 4 _<ᵒ_
data _<ᵒ_ : (x y : Ordinal) → Set where
  EmpO : {y : ℕ} → {ys : Ordinal} → [] <ᵒ y ∷ ys
  HigherO : {x y : ℕ} → {xs ys : Ordinal} → xs <ᵒ ys → x ∷ xs <ᵒ y ∷ ys
  HereO : {x y : ℕ} → {xs ys : Ordinal} → x < y → xs ≡ ys → x ∷ xs <ᵒ y ∷ ys

<ᵒ-irrefl : Irreflexive _≡_ _<ᵒ_
<ᵒ-irrefl refl (HigherO p) = <ᵒ-irrefl refl p
<ᵒ-irrefl refl (HereO p q) = <-irrefl refl p

<ᵒ-trans : Transitive _<ᵒ_
<ᵒ-trans EmpO (HigherO q) = EmpO
<ᵒ-trans EmpO (HereO p q) = EmpO
<ᵒ-trans (HigherO p) (HigherO q) = HigherO (<ᵒ-trans p q)
<ᵒ-trans (HigherO p) (HereO q refl) = HigherO p
<ᵒ-trans (HereO p refl) (HigherO r) = HigherO r
<ᵒ-trans (HereO p refl) (HereO q r) = HereO (<-trans p q) r

<ᵒ-resp : _<ᵒ_ Respects₂ _≡_
<ᵒ-resp = subst (_ <ᵒ_) ,, subst (_<ᵒ _)

Ord-is-order : IsStrictPartialOrder _≡_ _<ᵒ_
IsStrictPartialOrder.isEquivalence Ord-is-order = isEquivalence
IsStrictPartialOrder.irrefl Ord-is-order = <ᵒ-irrefl
IsStrictPartialOrder.trans Ord-is-order = <ᵒ-trans
IsStrictPartialOrder.<-resp-≈ Ord-is-order = <ᵒ-resp

Ord-Order : StrictPartialOrder _ _ _
StrictPartialOrder.Carrier Ord-Order = Ordinal
StrictPartialOrder._≈_ Ord-Order = _≡_
StrictPartialOrder._<_ Ord-Order = _<ᵒ_
StrictPartialOrder.isStrictPartialOrder Ord-Order = Ord-is-order

Ord-wf : WellFounded _<ᵒ_
Ord-wf [] = acc λ where ()
Ord-wf (x ∷ xs) = Some.wfRec (λ ys → (y : ℕ) → Acc _<ᵒ_ (y ∷ ys))
                             (λ ys rec → I.<-rec (λ z → Acc _<ᵒ_ (z ∷ ys)) λ x rec₂ → acc (f ys rec x rec₂))
                             xs
                             (Ord-wf xs)
                             x
  where
    f : (ys : Ordinal)
      → ({zs : Ordinal} → zs <ᵒ ys → (z : ℕ) → Acc _<ᵒ_ (z ∷ zs))
      → (y : ℕ)
      → ({z : ℕ} → (z < y) → Acc _<ᵒ_ (z ∷ ys))
      → {zs : Ordinal} → zs <ᵒ y ∷ ys → Acc _<ᵒ_ zs
    f ys rec y rec₂ EmpO = Ord-wf []
    f ys rec y rec₂ (HigherO p) = rec p _
    f ys rec y rec₂ (HereO x refl) = rec₂ x


infixl 6 _♯_
_♯_ : Ordinal → Ordinal → Ordinal
[] ♯ ys = ys
(x ∷ xs) ♯ [] = x ∷ xs
(x ∷ []) ♯ (y ∷ ys) = suc x + y ∷ ys
(x ∷ x′ ∷ xs) ♯ (y ∷ []) = suc x + y ∷ x′ ∷ xs
(x ∷ x′ ∷ xs) ♯ (y ∷ y′ ∷ ys) = x + y ∷ ((x′ ∷ xs) ♯ (y′ ∷ ys))


module _ where
  open import Algebra.Definitions {A = Ordinal} _≡_
  open import Algebra.Structures {A = Ordinal} _≡_

  ♯-lem : (x : ℕ) → (xs : Ordinal) → (y : ℕ) → (x ∷ xs) ♯ (y ∷ []) ≡ suc (x + y) ∷ xs
  ♯-lem x [] y = refl
  ♯-lem x (x′ ∷ xs) y = refl

  NE : Ordinal → Set
  NE [] = ⊥
  NE (x ∷ xs) = ⊤

  ♯-lem-2 : (x : ℕ) → (xs : Ordinal) → .⦃ NE xs ⦄ → (y : ℕ) → (ys : Ordinal) → .⦃ NE ys ⦄ → (x ∷ xs) ♯ (y ∷ ys) ≡ x + y ∷ (xs ♯ ys)
  ♯-lem-2 x (x′ ∷ xs) y (y′ ∷ ys) = refl

  ♯-preserve-non-null : (xs ys : Ordinal) → .⦃ NE xs ⦄ → .⦃ NE ys ⦄ → NE (xs ♯ ys)
  ♯-preserve-non-null (x ∷ []) (y ∷ ys) = tt
  ♯-preserve-non-null (x ∷ x′ ∷ xs) (y ∷ []) = tt
  ♯-preserve-non-null (x ∷ x′ ∷ xs) (y ∷ y′ ∷ ys) = tt

  ♯-assoc : Associative _♯_
  ♯-assoc [] ys zs = refl
  ♯-assoc (x ∷ xs) [] zs = refl
  ♯-assoc (x ∷ []) (y ∷ []) [] = refl
  ♯-assoc (x ∷ []) (y ∷ []) (z ∷ zs) = cong (_∷ zs) (cong suc (trans (cong suc (+-assoc x y z)) (sym (+-suc x (y + z)))))
  ♯-assoc (x ∷ []) (y ∷ y′ ∷ ys) [] = refl
  ♯-assoc (x ∷ []) (y ∷ y′ ∷ ys) (z ∷ []) = cong (_∷ y′ ∷ ys) (cong suc (trans (cong suc (+-assoc x y z)) (sym (+-suc x (y + z)))))
  ♯-assoc (x ∷ []) (y ∷ y′ ∷ ys) (z ∷ z′ ∷ zs) = cong (λ - → suc - ∷ (y′ ∷ ys) ♯ (z′ ∷ zs)) (+-assoc x y z)
  ♯-assoc (x ∷ x′ ∷ xs) (y ∷ []) [] = refl
  ♯-assoc (x ∷ x′ ∷ xs) (y ∷ []) (z ∷ []) = cong (_∷ x′ ∷ xs) (cong suc (trans (cong suc (+-assoc x y z)) (sym (+-suc x (y + z)))))
  ♯-assoc (x ∷ x′ ∷ xs) (y ∷ []) (z ∷ z′ ∷ zs) = cong (_∷ (x′ ∷ xs) ♯ (z′ ∷ zs)) (trans (cong suc (+-assoc x y z)) (sym (+-suc x (y + z))))
  ♯-assoc (x ∷ x′ ∷ xs) (y ∷ y′ ∷ ys) [] = refl
  ♯-assoc (x ∷ x′ ∷ xs) (y ∷ y′ ∷ ys) (z ∷ []) = trans (♯-lem (x + y) ((x′ ∷ xs) ♯ (y′ ∷ ys)) z)
                                                       (cong (_∷ (x′ ∷ xs) ♯ (y′ ∷ ys)) (trans (cong suc (+-assoc x y z)) (sym (+-suc x (y + z)))))
  ♯-assoc (x ∷ x′ ∷ xs) (y ∷ y′ ∷ ys) (z ∷ z′ ∷ zs) = begin
    (x + y ∷ (x′ ∷ xs) ♯ (y′ ∷ ys)) ♯ (z ∷ z′ ∷ zs)
      ≡⟨ ♯-lem-2 (x + y) ((x′ ∷ xs) ♯ (y′ ∷ ys)) ⦃ ♯-preserve-non-null (x′ ∷ xs) (y′ ∷ ys) ⦄ z (z′ ∷ zs)  ⟩
    x + y + z ∷ (x′ ∷ xs) ♯ (y′ ∷ ys) ♯ (z′ ∷ zs)
      ≡⟨ cong₂ _∷_ (+-assoc x y z) (♯-assoc (x′ ∷ xs) (y′ ∷ ys) (z′ ∷ zs)) ⟩
    x + (y + z) ∷ (x′ ∷ xs) ♯ ((y′ ∷ ys) ♯ (z′ ∷ zs))
      ≡˘⟨ ♯-lem-2 x (x′ ∷ xs) (y + z) ((y′ ∷ ys) ♯ (z′ ∷ zs)) ⦃ ♯-preserve-non-null (y′ ∷ ys) (z′ ∷ zs) ⦄ ⟩
    (x ∷ x′ ∷ xs) ♯ (y + z ∷ (y′ ∷ ys) ♯ (z′ ∷ zs)) ∎
    where
      open ≡-Reasoning

  ♯-left-unit : LeftIdentity [] _♯_
  ♯-left-unit xs = refl

  ♯-right-unit : RightIdentity [] _♯_
  ♯-right-unit [] = refl
  ♯-right-unit (x ∷ xs) = refl

  ♯-comm : Commutative _♯_
  ♯-comm [] ys = sym (♯-right-unit ys)
  ♯-comm (x ∷ []) [] = refl
  ♯-comm (x ∷ []) (y ∷ ys) = trans (cong (λ - → suc - ∷ ys) (+-comm x y)) (sym (♯-lem y ys x))
  ♯-comm (x ∷ x′ ∷ xs) [] = refl
  ♯-comm (x ∷ x′ ∷ xs) (y ∷ []) = cong (λ - → suc - ∷ x′ ∷ xs) (+-comm x y)
  ♯-comm (x ∷ x′ ∷ xs) (y ∷ y′ ∷ ys) = cong₂ _∷_ (+-comm x y) (♯-comm (x′ ∷ xs) (y′ ∷ ys))

  ♯-is-magma : IsMagma _♯_
  IsMagma.isEquivalence ♯-is-magma = isEquivalence
  IsMagma.∙-cong ♯-is-magma = cong₂ _♯_

  ♯-is-semigroup : IsSemigroup _♯_
  IsSemigroup.isMagma ♯-is-semigroup = ♯-is-magma
  IsSemigroup.assoc ♯-is-semigroup = ♯-assoc

  ♯-is-monoid : IsMonoid _♯_ []
  IsMonoid.isSemigroup ♯-is-monoid = ♯-is-semigroup
  IsMonoid.identity ♯-is-monoid = ♯-left-unit ,, ♯-right-unit

  ♯-is-comm-monoid : IsCommutativeMonoid _♯_ []
  IsCommutativeMonoid.isMonoid ♯-is-comm-monoid = ♯-is-monoid
  IsCommutativeMonoid.comm ♯-is-comm-monoid = ♯-comm

  ♯-comm-monoid : CommutativeMonoid _ _
  CommutativeMonoid.Carrier ♯-comm-monoid = Ordinal
  CommutativeMonoid._≈_ ♯-comm-monoid = _≡_
  CommutativeMonoid._∙_ ♯-comm-monoid = _♯_
  CommutativeMonoid.ε ♯-comm-monoid = []
  CommutativeMonoid.isCommutativeMonoid ♯-comm-monoid = ♯-is-comm-monoid

  add-<ᵒ : (xs ys : Ordinal) → .⦃ NE ys ⦄ → xs <ᵒ ys ♯ xs
  add-<ᵒ [] (y ∷ ys) = EmpO
  add-<ᵒ (x ∷ []) (y ∷ []) = HereO (s≤s (m≤n+m x y)) refl
  add-<ᵒ (x ∷ []) (y ∷ y′ ∷ ys) = HigherO EmpO
  add-<ᵒ (x ∷ x′ ∷ xs) (y ∷ []) = HereO (s≤s (m≤n+m x y)) refl
  add-<ᵒ (x ∷ x′ ∷ xs) (y ∷ y′ ∷ ys) = HigherO (add-<ᵒ (x′ ∷ xs) (y′ ∷ ys))

  ♯-monoˡ-<ᵒ : (xs : Ordinal) → {ys zs : Ordinal} → ys <ᵒ zs → ys ♯ xs <ᵒ zs ♯ xs
  ♯-monoˡ-<ᵒ [] {ys} {zs} p = begin-strict
    ys ♯ [] ≡⟨ ♯-right-unit ys ⟩
    ys      <⟨ p ⟩
    zs      ≡˘⟨ ♯-right-unit zs ⟩
    zs ♯ [] ∎
    where
      open SPReasoning Ord-Order
  ♯-monoˡ-<ᵒ (x ∷ []) EmpO = add-<ᵒ (x ∷ []) (_ ∷ _)
  ♯-monoˡ-<ᵒ (x ∷ []) {y ∷ ys} {z ∷ zs} (HigherO p) = begin-strict
    (y ∷ ys) ♯ (x ∷ []) ≡⟨ ♯-lem y ys x ⟩
    suc (y + x) ∷ ys <⟨ HigherO p ⟩
    suc (z + x) ∷ zs ≡˘⟨ ♯-lem z zs x ⟩
    (z ∷ zs) ♯ (x ∷ []) ∎
    where
      open SPReasoning Ord-Order
  ♯-monoˡ-<ᵒ (x ∷ []) {y ∷ ys} {z ∷ zs} (HereO p q) = begin-strict
    (y ∷ ys) ♯ (x ∷ []) ≡⟨ ♯-lem y ys x ⟩
    suc (y + x) ∷ ys <⟨ HereO (s≤s (+-monoˡ-< x p)) q ⟩
    suc (z + x) ∷ zs ≡˘⟨ ♯-lem z zs x ⟩
    (z ∷ zs) ♯ (x ∷ []) ∎
    where
      open SPReasoning Ord-Order
  ♯-monoˡ-<ᵒ (x ∷ x′ ∷ xs) EmpO = add-<ᵒ (x ∷ x′ ∷ xs) (_ ∷ _)
  ♯-monoˡ-<ᵒ (x ∷ x′ ∷ xs) (HigherO {xs = []} {ys = z ∷ zs} p) = HigherO (add-<ᵒ (x′ ∷ xs) (_ ∷ _))
  ♯-monoˡ-<ᵒ (x ∷ x′ ∷ xs) (HigherO {xs = y ∷ ys} {ys = z ∷ zs} p) = HigherO (♯-monoˡ-<ᵒ (x′ ∷ xs) p)
  ♯-monoˡ-<ᵒ (x ∷ x′ ∷ xs) (HereO {xs = []} p refl) = HereO (s≤s (+-monoˡ-< x p)) refl
  ♯-monoˡ-<ᵒ (x ∷ x′ ∷ xs) (HereO {xs = y ∷ ys} p refl) = HereO (+-monoˡ-< x p) refl

  ♯-monoʳ-<ᵒ : (xs : Ordinal) → {ys zs : Ordinal} → ys <ᵒ zs → xs ♯ ys <ᵒ xs ♯ zs
  ♯-monoʳ-<ᵒ [] p = p
  ♯-monoʳ-<ᵒ (x ∷ []) (EmpO {ys = []}) = HereO (m≤m+n (suc x) _) refl
  ♯-monoʳ-<ᵒ (x ∷ []) (EmpO {ys = y′ ∷ ys}) = HigherO EmpO
  ♯-monoʳ-<ᵒ (x ∷ []) (HigherO p) = HigherO p
  ♯-monoʳ-<ᵒ (x ∷ []) (HereO p q) = HereO (s≤s (+-monoʳ-< x p)) q
  ♯-monoʳ-<ᵒ (x ∷ x′ ∷ xs) (EmpO {ys = []}) = HereO (m≤m+n (suc x) _) refl
  ♯-monoʳ-<ᵒ (x ∷ x′ ∷ xs) (EmpO {ys = y′ ∷ ys}) = HigherO (♯-monoʳ-<ᵒ (x′ ∷ xs) EmpO)
  ♯-monoʳ-<ᵒ (x ∷ x′ ∷ xs) (HigherO {xs = []} {ys = z ∷ zs} p) = HigherO (♯-monoʳ-<ᵒ (x′ ∷ xs) EmpO)
  ♯-monoʳ-<ᵒ (x ∷ x′ ∷ xs) (HigherO {xs = y ∷ ys} {ys = z ∷ zs} p) = HigherO (♯-monoʳ-<ᵒ (x′ ∷ xs) p)
  ♯-monoʳ-<ᵒ (x ∷ x′ ∷ xs) (HereO {xs = []} p refl) = HereO (s≤s (+-monoʳ-< x p)) refl
  ♯-monoʳ-<ᵒ (x ∷ x′ ∷ xs) (HereO {xs = y ∷ ys} p refl) = HereO (+-monoʳ-< x p) refl

omega : ℕ → Ordinal
omega zero = 0 ∷ []
omega (suc n) = 0 ∷ omega n

SCTm : Tm n → Ordinal
SCTy : Ty n → Ordinal
SCSub : Sub n m ⋆ → Ordinal

SCTm (Var i) = []
SCTm (Coh S A σ) = omega (ty-dim A) ♯ SCTy A ♯ SCSub σ

SCTy ⋆ = []
SCTy (s ─⟨ A ⟩⟶ t) = SCTm s ♯ SCTy A ♯ SCTm t

SCSub ⟨⟩ = []
SCSub ⟨ σ , t ⟩ = SCSub σ ♯ SCTm t
