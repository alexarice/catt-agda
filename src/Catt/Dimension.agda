{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Dimension where

open import Catt.Syntax
open import Data.Nat
open import Data.Nat.Properties
open import Induction.WellFounded
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.Construct.Closure.Transitive using () renaming ([_] to [_]p; _∷_ to _∷p_) public

data Syntax : Set where
  Context : (Γ : Ctx n d) → Syntax
  Type : (A : Ty Γ n) → Syntax
  Term : (t : Tm Γ n) → Syntax
  Substitution : (σ : Sub Γ Δ) → Syntax

syntax-dim : Syntax → ℕ
syntax-dim (Context Γ) = ctx-dim Γ
syntax-dim (Type A) = ty-dim A
syntax-dim (Term t) = suc (tm-dim t)
syntax-dim (Substitution σ) = suc (sub-dim σ)

syntax-ctx-length : Syntax → ℕ
syntax-ctx-length (Context {n} Γ) = n
syntax-ctx-length (Type {n} A) = n
syntax-ctx-length (Term {n} t) = n
syntax-ctx-length (Substitution {Δ = Δ} σ) = ctxLength Δ

syntax-ctx-dim : Syntax → ℕ
syntax-ctx-dim (Context Γ) = ctx-dim Γ
syntax-ctx-dim (Type {Γ = Γ} A) = ctx-dim Γ
syntax-ctx-dim (Term {Γ = Γ} t) = ctx-dim Γ
syntax-ctx-dim (Substitution {Δ = Δ} σ) = ctx-dim Δ

syntax-ctx : (x : Syntax) → Ctx (syntax-ctx-length x) (syntax-ctx-dim x)
syntax-ctx (Context Γ) = Γ
syntax-ctx (Type {Γ = Γ} A) = Γ
syntax-ctx (Term {Γ = Γ} t) = Γ
syntax-ctx (Substitution {Δ = Δ} σ) = Δ

data _≺_ : Syntax → Syntax → Set where
  dim : {x : Syntax} → {y : Syntax} → (p : syntax-dim x < syntax-dim y) → x ≺ y
  ctx1 : Context Γ ≺ Context (Γ , A)
  ctx2 : Type A ≺ Context (Γ , A)
  ty1 : Term s ≺ Type (s ─⟨ A ⟩⟶ t)
  ty2 : Type A ≺ Type (s ─⟨ A ⟩⟶ t)
  ty3 : Term t ≺ Type (s ─⟨ A ⟩⟶ t)
  tm1 : Context Δ ≺ Term (Coh Δ A σ)
  tm2 : Type A ≺ Term (Coh Δ A σ)
  tm3 : Substitution σ ≺ Term (Coh Δ A σ)
  sub1 : Substitution σ ≺ Substitution (⟨_,_⟩ σ {A} t)
  sub2 : Term t ≺ Substitution (⟨_,_⟩ σ {A} t)

not-possible : (A : Set) → (x : ℕ) → x < 0 → A
not-possible A x ()

wf : WellFounded _≺_
wf x = acc (access (syntax-dim x) x ≤-refl)
  where
    access-ctx : (n : ℕ) → (Γ : Ctx m d) → (d ≤ n) → (y : Syntax) → y ≺ (Context Γ) → Acc _≺_ y
    access-ty : (n : ℕ) → (A : Ty Γ m) → (m ≤ n) → (y : Syntax) → y ≺ (Type A) → Acc _≺_ y
    access-tm : (n : ℕ) → (t : Tm Γ m) → (suc m ≤ n) → (y : Syntax) → y ≺ (Term t) → Acc _≺_ y
    access-sub : (n : ℕ) → (σ : Sub Γ Δ) → (suc (sub-dim σ) ≤ n) → (y : Syntax) → y ≺ (Substitution σ) → Acc _≺_ y
    access : (n : ℕ) → (x : Syntax) → (syntax-dim x ≤ n) → (y : Syntax) → y ≺ x → Acc _≺_ y

    access-ctx zero ∅ le y (dim ())
    access-ctx zero (Γ , A) le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
    access-ctx zero (Γ , A) le .(Context Γ) ctx1 = acc (access-ctx zero Γ (m⊔n≤o⇒m≤o _ _ le))
    access-ctx zero (Γ , A) le .(Type A) ctx2 = acc (access-ty zero A (m⊔n≤o⇒n≤o _ _ le))
    access-ctx (suc n) ∅ le y (dim ())
    access-ctx (suc n) (Γ , A) le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-ctx (suc n) (Γ , A) le .(Context Γ) ctx1 = acc (access-ctx (suc n) Γ (m⊔n≤o⇒m≤o _ _ le))
    access-ctx (suc n) (Γ , A) le .(Type A) ctx2 = acc (access-ty (suc n) A (m⊔n≤o⇒n≤o _ _ le))

    access-tm zero t () y p
    access-tm (suc n) (Var i) le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-tm (suc n) (Coh Δ A σ) le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-tm (suc n) (Coh Δ A σ) le .(Context Δ) tm1 = acc (access-ctx n Δ (≤-trans (m≤m⊔n _ _) (≤-pred le)))
    access-tm (suc n) (Coh Δ A σ) le .(Type A) tm2 = acc (access-ty n A (≤-trans (m≤n⊔m _ _) (≤-pred le)))
    access-tm (suc n) (Coh Δ A σ) le .(Substitution σ) tm3 = acc (access-sub (suc n) σ (≤-trans (s≤s (m≤m⊔n _ _)) le))

    access-sub zero σ () y p
    access-sub (suc n) ⟨⟩ le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-sub (suc n) ⟨ σ , t ⟩ le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-sub (suc n) ⟨ σ , t ⟩ le .(Substitution σ) sub1 = acc (access-sub (suc n) σ (≤-trans (s≤s (m≤m⊔n _ _)) le))
    access-sub (suc n) ⟨ σ , t ⟩ le .(Term t) sub2 = acc (access-tm (suc n) t (≤-trans (s≤s (m≤n⊔m _ _)) le))

    access-ty zero ⋆ le y (dim ())
    access-ty (suc n) ⋆ le y (dim ())
    access-ty (suc n) (s ─⟨ A ⟩⟶ t) le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-ty (suc n) (s ─⟨ A ⟩⟶ t) le .(Term s) ty1 = acc (access-tm (suc n) s le)
    access-ty (suc n) (s ─⟨ A ⟩⟶ t) le .(Type A) ty2 = acc (access-ty n A (≤-pred le))
    access-ty (suc n) (s ─⟨ A ⟩⟶ t) le .(Term t) ty3 = acc (access-tm (suc n) t le)

    access n (Context Γ) le = access-ctx n Γ le
    access n (Type A) le = access-ty n A le
    access n (Term t) le = access-tm n t le
    access n (Substitution σ) le = access-sub n σ le

_≺⁺_ = TransClosure _≺_

wf⁺ : WellFounded _≺⁺_
wf⁺ = wellFounded _≺_ wf

open All wf⁺ public
