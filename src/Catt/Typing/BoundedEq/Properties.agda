{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.BoundedEq.Properties (index : ℕ) (rule : Fin index → Rule)
                                                    (bound-rule : ∀ i a → P.BoundRule index rule {i} a)
                                                    where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Catt.Typing.Properties.Base index rule
open import Catt.Typing.BoundedEq index rule
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)
open import Data.Nat.Properties
open import Catt.Suspension
open import Catt.Tree
open import Catt.Globular
open import Catt.Globular.Properties
open import Data.Fin.Properties using (toℕ-injective)
open import Function.Bundles
open import Function.Construct.Identity
open import Function.Construct.Symmetry
open import Function.Construct.Composition

private
  Index : Set
  Index = Fin index

refl≈tyb : A ≈⟨ d ⟩[ Γ ]ty A
refl≈tmb : t ≈⟨ d ⟩[ Γ ]tm t
refl≈sb : σ ≈⟨ d ⟩[ Γ ]s σ

refl≈tyb {A = ⋆} = StarB≈
refl≈tyb {A = s ─⟨ A ⟩⟶ t} = ArrB≈ refl≈tmb refl≈tyb refl≈tmb

refl≈tmb {t = Var i} = VarB≈ refl
refl≈tmb {t = Coh Δ A σ} = CohB≈ refl≈tyb refl≈sb

refl≈sb {σ = ⟨⟩} = NullB≈ refl≈tyb
refl≈sb {σ = ⟨ σ , t ⟩} = ExtB≈ refl≈sb refl≈tmb

reflexive≈tyb : A ≃ty B → A ≈⟨ d ⟩[ Γ ]ty B
reflexive≈tmb : s ≃tm t → s ≈⟨ d ⟩[ Γ ]tm t
reflexive≈sb : σ ≃s τ → σ ≈⟨ d ⟩[ Γ ]s τ

reflexive≈tyb (Star≃ x) = StarB≈
reflexive≈tyb (Arr≃ p q r) = ArrB≈ (reflexive≈tmb p) (reflexive≈tyb q) (reflexive≈tmb r)

reflexive≈tmb (Var≃ x y) = VarB≈ y
reflexive≈tmb (Coh≃ p q r) with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = CohB≈ (reflexive≈tyb q) (reflexive≈sb r)

reflexive≈sb (Null≃ x) = NullB≈ (reflexive≈tyb x)
reflexive≈sb (Ext≃ eq x) = ExtB≈ (reflexive≈sb eq) (reflexive≈tmb x)

sym≈tyb : A ≈⟨ d ⟩[ Γ ]ty B → B ≈⟨ d ⟩[ Γ ]ty A
sym≈tmb : s ≈⟨ d ⟩[ Γ ]tm t → t ≈⟨ d ⟩[ Γ ]tm s
sym≈sb : σ ≈⟨ d ⟩[ Γ ]s τ → τ ≈⟨ d ⟩[ Γ ]s σ

sym≈tyb StarB≈ = StarB≈
sym≈tyb (ArrB≈ p q r) = ArrB≈ (sym≈tmb p) (sym≈tyb q) (sym≈tmb r)

sym≈tmb eq = SymB≈ eq

sym≈sb (NullB≈ x) = NullB≈ (sym≈tyb x)
sym≈sb (ExtB≈ eq x) = ExtB≈ (sym≈sb eq) (sym≈tmb x)

trans≈tyb : A ≈⟨ d ⟩[ Γ ]ty B → B ≈⟨ d ⟩[ Γ ]ty C → A ≈⟨ d ⟩[ Γ ]ty C
trans≈tmb : s ≈⟨ d ⟩[ Γ ]tm t → t ≈⟨ d ⟩[ Γ ]tm u → s ≈⟨ d ⟩[ Γ ]tm u
trans≈sb : σ ≈⟨ d ⟩[ Γ ]s τ → τ ≈⟨ d ⟩[ Γ ]s μ → σ ≈⟨ d ⟩[ Γ ]s μ

trans≈tyb StarB≈ StarB≈ = StarB≈
trans≈tyb (ArrB≈ p q r) (ArrB≈ p′ q′ r′) = ArrB≈ (trans≈tmb p p′) (trans≈tyb q q′) (trans≈tmb r r′)

trans≈tmb eq eq′ = TransB≈ eq eq′

trans≈sb (NullB≈ x) (NullB≈ y) = NullB≈ (trans≈tyb x y)
trans≈sb (ExtB≈ eq x) (ExtB≈ eq′ y) = ExtB≈ (trans≈sb eq eq′) (trans≈tmb x y)

ty-setoid-≈b : (d : ℕ) → Ctx n → Setoid _ _
ty-setoid-≈b {n} d Γ = record { Carrier = Ty n
                    ; _≈_ = λ x y → x ≈⟨ d ⟩[ Γ ]ty y
                    ; isEquivalence = record { refl = refl≈tyb
                                             ; sym = sym≈tyb
                                             ; trans = trans≈tyb
                                             }
                    }

tm-setoid-≈b : (d : ℕ) → Ctx n → Setoid _ _
tm-setoid-≈b {n} d Γ = record { Carrier = Tm n
                    ; _≈_ = λ x y → x ≈⟨ d ⟩[ Γ ]tm y
                    ; isEquivalence = record { refl = refl≈tmb
                                             ; sym = sym≈tmb
                                             ; trans = trans≈tmb
                                             }
                    }

sub-setoid-≈b : (d : ℕ) → ℕ → Ctx m → Setoid _ _
sub-setoid-≈b {m} d n Δ = record { Carrier = SUB′ n m
                    ; _≈_ = λ x y → sub′ x ≈⟨ d ⟩[ Δ ]s sub′ y
                    ; isEquivalence = record { refl = refl≈sb
                                             ; sym = sym≈sb
                                             ; trans = trans≈sb
                                             }
                    }

≈tyb-preserve-height : A ≈⟨ d ⟩[ Γ ]ty B → ty-dim A ≡ ty-dim B
≈tyb-preserve-height StarB≈ = refl
≈tyb-preserve-height (ArrB≈ x p x₁) = cong suc (≈tyb-preserve-height p)

bd-eq-to-eq-tm : s ≈⟨ d ⟩[ Γ ]tm t → s ≈[ Γ ]tm t
bd-eq-to-eq-ty : A ≈⟨ d ⟩[ Γ ]ty B → A ≈[ Γ ]ty B
bd-eq-to-eq-sub : σ ≈⟨ d ⟩[ Γ ]s τ → σ ≈[ Γ ]s τ

bd-eq-to-eq-tm (VarB≈ x) = Var≈ x
bd-eq-to-eq-tm (SymB≈ eq) = Sym≈ (bd-eq-to-eq-tm eq)
bd-eq-to-eq-tm (TransB≈ eq eq₁) = Trans≈ (bd-eq-to-eq-tm eq) (bd-eq-to-eq-tm eq₁)
bd-eq-to-eq-tm (CohB≈ x y) = Coh≈ (bd-eq-to-eq-ty x) (bd-eq-to-eq-sub y)
bd-eq-to-eq-tm (RuleB≈ i a tty p) = Rule≈ i a tty

bd-eq-to-eq-ty StarB≈ = Star≈
bd-eq-to-eq-ty (ArrB≈ p q r) = Arr≈ (bd-eq-to-eq-tm p) (bd-eq-to-eq-ty q) (bd-eq-to-eq-tm r)

bd-eq-to-eq-sub (NullB≈ x) = Null≈ (bd-eq-to-eq-ty x)
bd-eq-to-eq-sub (ExtB≈ eq x) = Ext≈ (bd-eq-to-eq-sub eq) (bd-eq-to-eq-tm x)

≈ty-preserve-bound : A ≈[ Γ ]ty B → BoundedTy d Γ A ⇔ BoundedTy d Γ B
≈tm-preserve-bound : s ≈[ Γ ]tm t → BoundedTm d Γ s ⇔ BoundedTm d Γ t
≈s-preserve-bound : σ ≈[ Γ ]s τ → BoundedSub d Γ σ ⇔ BoundedSub d Γ τ

≈ty-preserve-bound Star≈ = id-⇔ (BoundedTy _ _ ⋆)
≈ty-preserve-bound (Arr≈ p q r) = mk⇔
  (λ where (ArrBound a b c) → ArrBound (≈tm-preserve-bound p .Equivalence.f a) (≈ty-preserve-bound q .Equivalence.f b) (≈tm-preserve-bound r .Equivalence.f c))
  λ where (ArrBound a b c) → ArrBound (≈tm-preserve-bound p .Equivalence.g a) (≈ty-preserve-bound q .Equivalence.g b) (≈tm-preserve-bound r .Equivalence.g c)

≈tm-preserve-bound (Var≈ x) with toℕ-injective x
... | refl = id-⇔ (BoundedTm _ _ (Var _))
≈tm-preserve-bound (Sym≈ eq) = sym-⇔ (≈tm-preserve-bound eq)
≈tm-preserve-bound (Trans≈ p q) = ≈tm-preserve-bound p ∘-⇔ ≈tm-preserve-bound q
≈tm-preserve-bound (Coh≈ p q) = mk⇔
  (λ where (CohBound S b c) → CohBound S (≈ty-preserve-bound p .Equivalence.f b) (≈s-preserve-bound q .Equivalence.f c))
  λ where (CohBound S b c) → CohBound S (≈ty-preserve-bound p .Equivalence.g b) (≈s-preserve-bound q .Equivalence.g c)
≈tm-preserve-bound (Rule≈ i a x) = bound-rule i a

≈s-preserve-bound (Null≈ x) = id-⇔ (BoundedSub _ _ ⟨⟩)
≈s-preserve-bound (Ext≈ p x) = mk⇔
  (λ where (ExtBound a b) → ExtBound (≈s-preserve-bound p .Equivalence.f a) (≈tm-preserve-bound x .Equivalence.f b))
  (λ where (ExtBound a b) → ExtBound (≈s-preserve-bound p .Equivalence.g a) (≈tm-preserve-bound x .Equivalence.g b))

eq-to-bd-eq-tm : s ≈[ Γ ]tm t → BoundedTm d Γ s → s ≈⟨ d ⟩[ Γ ]tm t
eq-to-bd-eq-ty : A ≈[ Γ ]ty B → BoundedTy d Γ A → A ≈⟨ d ⟩[ Γ ]ty B
eq-to-bd-eq-sub : σ ≈[ Γ ]s τ → BoundedSub d Γ σ → σ ≈⟨ d ⟩[ Γ ]s τ

eq-to-bd-eq-tm (Var≈ x) p = VarB≈ x
eq-to-bd-eq-tm (Sym≈ eq) p = SymB≈ (eq-to-bd-eq-tm eq (≈tm-preserve-bound eq .Equivalence.g p))
eq-to-bd-eq-tm (Trans≈ eq eq₁) p = TransB≈ (eq-to-bd-eq-tm eq p) (eq-to-bd-eq-tm eq₁ (≈tm-preserve-bound eq .Equivalence.f p))
eq-to-bd-eq-tm (Coh≈ x y) (CohBound _ a b) = CohB≈ (eq-to-bd-eq-ty x a) (eq-to-bd-eq-sub y b)
eq-to-bd-eq-tm (Rule≈ i a tty) p = RuleB≈ i a tty p

eq-to-bd-eq-ty Star≈ p = StarB≈
eq-to-bd-eq-ty (Arr≈ p q r) (ArrBound a b c) = ArrB≈ (eq-to-bd-eq-tm p (BoundedSucTm a)) (eq-to-bd-eq-ty q (BoundedSucTy b)) (eq-to-bd-eq-tm r (BoundedSucTm c))

eq-to-bd-eq-sub (Null≈ Star≈) b = NullB≈ StarB≈
eq-to-bd-eq-sub (Ext≈ eq x) b = ExtB≈ ? ?
