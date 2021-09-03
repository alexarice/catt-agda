{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Dimension where

open import Catt.Syntax
open import Data.Nat
open import Data.Nat.Properties
open import Induction.WellFounded
open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.Construct.Closure.Transitive using () renaming ([_] to [_]p; _∷_ to _∷p_) public

data CtxDim : Ctx → ℕ → Set
data TyDim : .⦃ CtxDim Γ d ⦄ → Ty Γ d′ → ℕ → Set
data TmDim : .⦃ CtxDim Γ d ⦄ → Tm Γ → ℕ → Set
data SubDim : .⦃ CtxDim Γ d ⦄ → .⦃ CtxDim Δ d′ ⦄ → Sub Γ Δ → ℕ → Set

data CtxDim where
  instance CtxDimB : CtxDim ∅ 0
  instance CtxDimS : ⦃ _ : CtxDim Γ n ⦄ → ⦃ TyDim A m ⦄ → CtxDim (Γ , A) (n ⊔ m)

lookupDim : (Γ : Ctx) → ⦃ CtxDim Γ n ⦄ → (i : Fin (ctxLength Γ)) → ℕ
lookupDim (Γ , A) ⦃ CtxDimS {m = m} ⦄ zero = m
lookupDim (Γ , A) ⦃ CtxDimS ⦄ (suc i) = lookupDim Γ i

data TyDim where
  instance TyDimB : .⦃ _ : CtxDim Γ d ⦄ → TyDim (⋆ {Γ = Γ}) 1
  instance TyDimS : .⦃ _ : CtxDim Γ d ⦄ → {s : Tm Γ} → ⦃ TmDim s (suc n) ⦄ → ⦃ TyDim A n ⦄ → ⦃ TmDim t (suc n) ⦄ → TyDim (s ─⟨ A ⟩⟶ t) (suc n)

data TmDim where
  instance TmDimV : ⦃ _ : CtxDim Γ n ⦄ → {i : Fin (ctxLength Γ)} → TmDim (Var {Γ = Γ} i) (suc (lookupDim Γ i))
  instance TmDimC : .⦃ _ : CtxDim Γ d ⦄ → ⦃ _ : CtxDim Δ m ⦄ → ⦃ TyDim A n ⦄ → {σ : Sub Δ Γ} → ⦃ SubDim σ l ⦄ → .⦃ m ≤ n ⦄ → .⦃ l ≤ suc n ⦄ → TmDim (Coh Δ A σ) (suc n)

data SubDim where
  instance SubDimB : .⦃ _ : CtxDim Γ d ⦄ → .⦃ _ : CtxDim Δ d′ ⦄ → SubDim (⟨⟩ {Δ = Δ}) 0
  instance SubDimS : .⦃ _ : CtxDim Γ d ⦄ → .⦃ _ : CtxDim Δ d′ ⦄ → { σ : Sub Γ Δ} → ⦃ SubDim σ n ⦄ → ⦃ _ : TyDim A m ⦄ → ⦃ TmDim t (suc m) ⦄ → SubDim (⟨_,_⟩ σ {A} t) (n ⊔ suc m)

data Syntax : Set where
  Context : (Γ : Ctx) → ⦃ c : CtxDim Γ n ⦄ → Syntax
  Type : (A : Ty Γ d′) → .⦃ _ : CtxDim Γ d ⦄ → ⦃ c : TyDim A n ⦄ → Syntax
  Term : (t : Tm Γ) → .⦃ _ : CtxDim Γ d ⦄ → ⦃ c : TmDim t n ⦄ → Syntax
  Substitution : (σ : Sub Γ Δ) → .⦃ _ : CtxDim Γ d ⦄ → .⦃ _ : CtxDim Δ d′ ⦄ → ⦃ c : SubDim σ n ⦄ → Syntax

syntax-dim : Syntax → ℕ
syntax-dim (Context {n = n} Γ) = n
syntax-dim (Type {n = n} A) = n
syntax-dim (Term {n = n} t) = n
syntax-dim (Substitution {n = n} σ) = n

syntax-ctx : Syntax → Ctx
syntax-ctx (Context Γ) = Γ
syntax-ctx (Type {Γ = Γ} A) = Γ
syntax-ctx (Term {Γ = Γ} t) = Γ
syntax-ctx (Substitution {Δ = Δ} σ) = Δ

data _≺_ : Syntax → Syntax → Set where
  dim : {x : Syntax} → {y : Syntax} → .(p : syntax-dim x < syntax-dim y) → x ≺ y
  ctx1 : ⦃ _ : CtxDim Γ n ⦄ → ⦃ _ : TyDim A n ⦄ → Context Γ ≺ Context (Γ , A)
  ctx2 : ⦃ _ : CtxDim Γ n ⦄ → ⦃ _ : TyDim A n ⦄ → Type A ≺ Context (Γ , A)
  ty1 : .⦃ _ : CtxDim Γ m ⦄ → ⦃ _ : TmDim {Γ = Γ} s (suc n) ⦄ → ⦃ _ : TyDim A n ⦄ → ⦃ _ : TmDim t (suc n) ⦄ → Term s ≺ Type (s ─⟨ A ⟩⟶ t)
  ty2 : .⦃ _ : CtxDim Γ m ⦄ → ⦃ _ : TmDim {Γ = Γ} s (suc n) ⦄ → ⦃ _ : TyDim A n ⦄ → ⦃ _ : TmDim t (suc n) ⦄ → Type A ≺ Type (s ─⟨ A ⟩⟶ t)
  ty3 : .⦃ _ : CtxDim Γ m ⦄ → ⦃ _ : TmDim {Γ = Γ} s (suc n) ⦄ → ⦃ _ : TyDim A n ⦄ → ⦃ _ : TmDim t (suc n) ⦄ → Term t ≺ Type (s ─⟨ A ⟩⟶ t)
  tm1 : .⦃ _ : CtxDim Γ n′ ⦄ → ⦃ _ : CtxDim Δ m ⦄ → ⦃ _ : TyDim A n ⦄ → ⦃ _ : SubDim {Δ = Γ} σ l ⦄ → .⦃ _ : m ≤ n ⦄ → .⦃ _ : l ≤ suc n ⦄ → Context Δ ≺ Term (Coh Δ A σ)
  tm2 : .⦃ _ : CtxDim Γ n′ ⦄ → ⦃ _ : CtxDim Δ m ⦄ → ⦃ _ : TyDim A n ⦄ → ⦃ _ : SubDim {Δ = Γ} σ l ⦄ → .⦃ _ : m ≤ n ⦄ → .⦃ _ : l ≤ suc n ⦄ → Type A ≺ Term (Coh Δ A σ)
  tm3 : .⦃ _ : CtxDim Γ n′ ⦄ → ⦃ _ : CtxDim Δ m ⦄ → ⦃ _ : TyDim A n ⦄ → ⦃ _ : SubDim {Δ = Γ} σ l ⦄ → .⦃ _ : m ≤ n ⦄ → .⦃ _ : l ≤ suc n ⦄ → Substitution σ ≺ Term (Coh Δ A σ)
  sub1 : .⦃ _ : CtxDim Γ n′ ⦄ → .⦃ _ : CtxDim Δ m′ ⦄ → ⦃ _ : SubDim {Γ = Γ} {Δ = Δ} σ n ⦄ → ⦃ _ : TyDim A m ⦄ → ⦃ _ : TmDim t (suc m) ⦄ → Substitution σ ≺ Substitution (⟨_,_⟩ σ {A} t)
  sub2 : .⦃ _ : CtxDim Γ n′ ⦄ → .⦃ _ : CtxDim Δ m′ ⦄ → ⦃ _ : SubDim {Γ = Γ} {Δ = Δ} σ n ⦄ → ⦃ _ : TyDim A m ⦄ → ⦃ _ : TmDim t (suc m) ⦄ → Term t ≺ Substitution (⟨_,_⟩ σ {A} t)

not-possible : (A : Set) → (x : ℕ) → .(x < 0) → A
not-possible A x ()

wf : WellFounded _≺_
wf x = acc (access (syntax-dim x) x ≤-refl)
  where
    access-ctx : (n : ℕ) → (Γ : Ctx) → {d : ℕ} → ⦃ _ : CtxDim Γ d ⦄ → .(d ≤ n) → (y : Syntax) → y ≺ (Context Γ) → Acc _≺_ y
    access-ty : (n : ℕ) → (A : Ty Γ m) → .⦃ _ : CtxDim Γ d′ ⦄ → {d : ℕ} → ⦃ _ : TyDim A d ⦄ → .(d ≤ n) → (y : Syntax) → y ≺ (Type A) → Acc _≺_ y
    access-tm : (n : ℕ) → (t : Tm Γ) → .⦃ _ : CtxDim Γ d′ ⦄ → {d : ℕ} → ⦃ _ : TmDim t d ⦄ → .(d ≤ n) → (y : Syntax) → y ≺ (Term t) → Acc _≺_ y
    access-sub : (n : ℕ) → (σ : Sub Γ Δ) → .⦃ _ : CtxDim Γ d′ ⦄ → .⦃ _ : CtxDim Δ m ⦄ → {d : ℕ} → ⦃ _ : SubDim σ d ⦄ → .(d ≤ n) → (y : Syntax) → y ≺ (Substitution σ) → Acc _≺_ y
    access : (n : ℕ) → (x : Syntax) → .(syntax-dim x ≤ n) → (y : Syntax) → y ≺ x → Acc _≺_ y

    access-ctx zero ∅ le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
    access-ctx zero (Γ , A) le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
    access-ctx zero (Γ , A) le .(Context Γ) ctx1 = acc (access-ctx zero Γ (m⊔n≤o⇒m≤o _ _ le))
    access-ctx zero (Γ , A) le .(Type A) ctx2 = acc (access-ty zero A (m⊔n≤o⇒n≤o _ _ le))
    access-ctx (suc n) ∅ {zero} ⦃ x ⦄ le y (dim ())
    access-ctx (suc n) ∅ {suc d} ⦃ () ⦄ le y (dim p)
    access-ctx (suc n) (Γ , A) le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-ctx (suc n) (Γ , A) le .(Context Γ) ctx1 = acc (access-ctx (suc n) Γ (m⊔n≤o⇒m≤o _ _ le))
    access-ctx (suc n) (Γ , A) le .(Type A) ctx2 = acc (access-ty (suc n) A (m⊔n≤o⇒n≤o _ _ le))

    access-ty zero ⋆ {zero} ⦃ () ⦄ le y p
    access-ty zero ⋆ {suc d} ⦃ x ⦄ () y p
    access-ty zero (s ─⟨ A ⟩⟶ t) {zero} ⦃ () ⦄ le y p
    access-ty zero (s ─⟨ A ⟩⟶ t) {suc d} () y p
    access-ty (suc n) ⋆ le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-ty (suc n) (s ─⟨ A ⟩⟶ t) le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-ty (suc n) (s ─⟨ A ⟩⟶ t) le .(Term s) ty1 = acc (access-tm (suc n) s le)
    access-ty (suc n) (s ─⟨ A ⟩⟶ t) le .(Type A) ty2 = acc (access-ty n A (≤-pred le))
    access-ty (suc n) (s ─⟨ A ⟩⟶ t) le .(Term t) ty3 = acc (access-tm (suc n) t le)

    access-tm zero (Var i) {zero} ⦃ () ⦄ le y p
    access-tm zero (Var i) {suc d} ⦃ x ⦄ () y p
    access-tm zero (Coh Δ A σ) le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
    access-tm (suc n) (Var i) le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-tm (suc n) (Coh Δ A σ) le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-tm (suc n) (Coh Δ A σ) le .(Context Δ) tm1 = acc (access-ctx n Δ (≤-trans it (≤-pred le)))
    access-tm (suc n) (Coh Δ A σ) le .(Type A) tm2 = acc (access-ty n A (≤-pred le))
    access-tm (suc n) (Coh Δ A σ) le .(Substitution σ) tm3 = acc (access-sub (suc n) σ (≤-trans it le))

    access-sub zero ⟨⟩ {zero} ⦃ x ⦄ le y (dim ())
    access-sub zero ⟨⟩ {suc d} ⦃ () ⦄ le y (dim p)
    access-sub zero ⟨ σ , t ⟩ le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
    access-sub zero ⟨ σ , t ⟩ le .(Substitution σ) sub1 = acc (access-sub zero σ (m⊔n≤o⇒m≤o _ _ le))
    access-sub zero ⟨ σ , t ⟩ le .(Term t) sub2 = acc (access-tm zero t (m⊔n≤o⇒n≤o _ (suc _) le))
    access-sub (suc n) ⟨⟩ le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-sub (suc n) ⟨ σ , t ⟩ le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
    access-sub (suc n) ⟨ σ , t ⟩ le .(Substitution σ) sub1 = acc (access-sub (suc n) σ (m⊔n≤o⇒m≤o _ _ le))
    access-sub (suc n) ⟨ σ , t ⟩ le .(Term t) sub2 = acc (access-tm (suc n) t (m⊔n≤o⇒n≤o _ _ le))

    access n (Context Γ) le = access-ctx n Γ le
    access n (Type A) le = access-ty n A le
    access n (Term t) le = access-tm n t le
    access n (Substitution σ) le = access-sub n σ le

_≺⁺_ = TransClosure _≺_

wf⁺ : WellFounded _≺⁺_
wf⁺ = wellFounded _≺_ wf

open All wf⁺ public

-- no-term-of-dim-1 : ⦃ TmDim t 1 ⦄ → ⊥
-- no-term-of-dim-1 {Γ , A} {t = Var {Γ = .(Γ , A)} zero} ⦃ x ⦄ = {!!}
-- no-term-of-dim-1 {Γ , A} {t = Var {Γ = .(Γ , A)} (suc i)} ⦃ x ⦄ = {!!}
-- no-term-of-dim-1 {∅} {t = Coh Δ A σ} ⦃ TmDimC ⦄ = {!!}
-- no-term-of-dim-1 {Γ , A₁} {t = Coh Δ A σ} ⦃ x ⦄ = {!!}
