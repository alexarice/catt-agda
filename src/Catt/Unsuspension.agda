{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Unsuspension where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc;toℕ;inject₁;fromℕ<)
open import Data.Fin.Properties using (toℕ-inject₁;toℕ<n;toℕ-fromℕ<)
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

is-unsuspendable-ctx : (Γ : Ctx n) → Set
unsuspend-ctx : (Γ : Ctx (suc (suc n))) → .⦃ us : is-unsuspendable-ctx Γ ⦄ → Ctx n

unsuspend-ctx-compat : (Γ : Ctx (suc (suc n))) → .⦃ us : is-unsuspendable-ctx Γ ⦄ → suspCtx (unsuspend-ctx Γ) ≃c Γ
is-unsuspendable-ty : (A : Ty (suc (suc n)) d) → Set
unsuspend-ty : (A : Ty (suc (suc n)) d)
             → .⦃ is-unsuspendable-ty A ⦄
             → Ty n (pred d)
unsuspend-ty-compat : (A : Ty (suc (suc n)) d)
                    → .⦃ _ : is-unsuspendable-ty A ⦄
                    → suspTy (unsuspend-ty A) ≃ty A
is-unsuspendable-tm : (t : Tm (suc (suc n))) → Set
unsuspend-tm : (t : Tm (suc (suc n)))
             → .⦃ is-unsuspendable-tm t ⦄
             → Tm n
unsuspend-tm-compat : (t : Tm (suc (suc n)))
                    → .⦃ _ : is-unsuspendable-tm t ⦄
                    → suspTm (unsuspend-tm t) ≃tm t
is-unsuspendable-sub : Sub (suc (suc n)) (suc (suc m)) → Set
unsuspend-sub : (σ : Sub (suc (suc n)) (suc (suc m)))
              → .⦃ is-unsuspendable-sub σ ⦄
              → Sub n m
unsuspend-sub-compat : (σ : Sub (suc (suc n)) (suc (suc m)))
                     → .⦃ _ : is-unsuspendable-sub σ ⦄
                     → suspSub (unsuspend-sub σ) ≃s σ

is-unsuspendable-ctx ∅ = ⊥
is-unsuspendable-ctx (∅ , A) = ⊥
is-unsuspendable-ctx (∅ , ⋆ , ⋆) = ⊤
is-unsuspendable-ctx (∅ , ⋆ , _ ─⟨ _ ⟩⟶ _) = ⊥
is-unsuspendable-ctx (∅ , _ ─⟨ _ ⟩⟶ _ , _) = ⊥
is-unsuspendable-ctx (Γ , A , B , C) = is-unsuspendable-ctx (Γ , A , B) × is-unsuspendable-ty C

unsuspend-ctx (∅ , ⋆ , ⋆) = ∅
unsuspend-ctx (Γ , A , B , C) ⦃ usc ⦄ = (unsuspend-ctx (Γ , A , B) ⦃ proj₁ usc ⦄) , unsuspend-ty C ⦃ proj₂ usc ⦄

unsuspend-ctx-compat (∅ , ⋆ , ⋆) = refl≃c
unsuspend-ctx-compat (Γ , A , B , C) ⦃ us ⦄ = Add≃ (unsuspend-ctx-compat (Γ , A , B) ⦃ proj₁ us ⦄) (unsuspend-ty-compat C ⦃ proj₂ us ⦄)

is-unsuspendable-ty ⋆ = ⊥
is-unsuspendable-ty {n = n} (s ─⟨ ⋆ ⟩⟶ t) = getFst {n} ≃tm s × getSnd {n} ≃tm t
is-unsuspendable-ty (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) = is-unsuspendable-ty A × is-unsuspendable-tm s × is-unsuspendable-tm t

unsuspend-ty (s ─⟨ ⋆ ⟩⟶ t) = ⋆
unsuspend-ty (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) ⦃ x ⦄ = (unsuspend-tm s ⦃ proj₁ (proj₂ x) ⦄) ─⟨ unsuspend-ty A ⦃ proj₁ x ⦄ ⟩⟶ unsuspend-tm t ⦃ proj₂ (proj₂ x) ⦄

unsuspend-ty-compat {n = n} (s ─⟨ ⋆ ⟩⟶ t) ⦃ x ⦄ = Arr≃ (recompute (≃tm-dec (getFst {n}) s) (proj₁ x)) (Star≃ refl) (recompute (≃tm-dec (getSnd {n}) t) (proj₂ x))
unsuspend-ty-compat (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) ⦃ x ⦄ = Arr≃ (unsuspend-tm-compat s ⦃ proj₁ (proj₂ x) ⦄) (unsuspend-ty-compat A ⦃ proj₁ x ⦄) (unsuspend-tm-compat t ⦃ proj₂ (proj₂ x) ⦄)

is-unsuspendable-tm {n = n} (Var i) = toℕ i < n
is-unsuspendable-tm (Coh {n = zero} Δ A σ) = ⊥
is-unsuspendable-tm (Coh {n = suc zero} Δ A σ) = ⊥
is-unsuspendable-tm (Coh {n = suc (suc n)} Δ A σ) = is-unsuspendable-ctx Δ × is-unsuspendable-ty A × is-unsuspendable-sub σ

fromℕ<Irrel : ∀ {m n} → .(m < n) → Fin n
fromℕ<Irrel {zero}  {suc n} m≤n = zero
fromℕ<Irrel {suc m} {suc n} m≤n = suc (fromℕ<Irrel (≤-pred m≤n))

toℕ-fromℕ<Irrel : ∀ {m n} .(m<n : m < n) → toℕ (fromℕ<Irrel m<n) ≡ m
toℕ-fromℕ<Irrel {zero} {suc n} m≤n = refl
toℕ-fromℕ<Irrel {suc m} {suc n} m≤n = cong suc (toℕ-fromℕ<Irrel (≤-pred m≤n))

unsuspend-tm {n = n} (Var i) = Var (fromℕ<Irrel it)
unsuspend-tm (Coh {n = suc (suc n)} Δ A σ) ⦃ x ⦄ = Coh (unsuspend-ctx Δ ⦃ proj₁ x ⦄) (unsuspend-ty A ⦃ proj₁ (proj₂ x) ⦄) (unsuspend-sub σ ⦃ proj₂ (proj₂ x) ⦄)

unsuspend-tm-compat {n = n} (Var i) = Var≃ refl (begin
  toℕ (inject₁ (inject₁ (fromℕ<Irrel _))) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ (fromℕ<Irrel _)) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ (fromℕ<Irrel _) ≡⟨ toℕ-fromℕ<Irrel _ ⟩
  toℕ i ∎)
  where
    open ≡-Reasoning
unsuspend-tm-compat (Coh {n = suc (suc n)} Δ A σ) ⦃ x ⦄ = Coh≃ (unsuspend-ctx-compat Δ ⦃ proj₁ x ⦄) (unsuspend-ty-compat A ⦃ proj₁ (proj₂ x) ⦄) (unsuspend-sub-compat σ ⦃ proj₂ (proj₂ x) ⦄)

is-unsuspendable-sub {m = m} ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ = getFst {m} ≃tm s × getSnd {m} ≃tm t
is-unsuspendable-sub ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = is-unsuspendable-sub ⟨ ⟨ σ , u ⟩ , s ⟩ × is-unsuspendable-tm t

unsuspend-sub ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ = ⟨⟩
unsuspend-sub ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ ⦃ x ⦄ = ⟨ unsuspend-sub ⟨ ⟨ σ , u ⟩ , s ⟩ ⦃ proj₁ x ⦄ , unsuspend-tm t ⦃ proj₂ x ⦄ ⟩

unsuspend-sub-compat ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ ⦃ x ⦄ = Ext≃ (Ext≃ (Null≃ refl) (recompute (≃tm-dec getFst s) (proj₁ x))) (recompute (≃tm-dec getSnd t) (proj₂ x))
unsuspend-sub-compat ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ ⦃ x ⦄ = Ext≃ (unsuspend-sub-compat ⟨ ⟨ σ , u ⟩ , s ⟩ ⦃ proj₁ x ⦄) (unsuspend-tm-compat t ⦃ proj₂ x ⦄)

suspension-is-unsuspendable-ctx :  (Γ : Ctx n) → is-unsuspendable-ctx (suspCtx Γ)
suspension-is-unsuspendable-ty : (A : Ty n d) → is-unsuspendable-ty (suspTy A)
suspension-is-unsuspendable-tm : (t : Tm n) → is-unsuspendable-tm (suspTm t)
suspension-is-unsuspendable-sub : (σ : Sub n m) → is-unsuspendable-sub (suspSub σ)

suspension-is-unsuspendable-ctx ∅ = tt
suspension-is-unsuspendable-ctx (∅ , A) = tt ,, (suspension-is-unsuspendable-ty A)
suspension-is-unsuspendable-ctx (∅ , A , B)
  = (tt ,, suspension-is-unsuspendable-ty A) ,,  suspension-is-unsuspendable-ty B
suspension-is-unsuspendable-ctx (Γ , A , B , C)
  = suspension-is-unsuspendable-ctx (Γ , A , B) ,, suspension-is-unsuspendable-ty C

suspension-is-unsuspendable-ty ⋆ = refl≃tm ,, refl≃tm
suspension-is-unsuspendable-ty (s ─⟨ ⋆ ⟩⟶ t) = (refl≃tm ,, refl≃tm) ,, (suspension-is-unsuspendable-tm s) ,, (suspension-is-unsuspendable-tm t)
suspension-is-unsuspendable-ty (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) = (suspension-is-unsuspendable-ty A) ,, ((suspension-is-unsuspendable-tm s) ,, (suspension-is-unsuspendable-tm t))

suspension-is-unsuspendable-tm (Var i) = ≤-trans (≤-reflexive (cong suc (trans (toℕ-inject₁ _) (toℕ-inject₁ _)))) (toℕ<n i)
suspension-is-unsuspendable-tm (Coh Δ A σ)
  = (suspension-is-unsuspendable-ctx Δ) ,, (suspension-is-unsuspendable-ty A ,, suspension-is-unsuspendable-sub σ)

suspension-is-unsuspendable-sub ⟨⟩ = refl≃tm ,, refl≃tm
suspension-is-unsuspendable-sub ⟨ ⟨⟩ , t ⟩ = (refl≃tm ,, refl≃tm) ,, (suspension-is-unsuspendable-tm t)
suspension-is-unsuspendable-sub ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ = ((refl≃tm ,, refl≃tm) ,, (suspension-is-unsuspendable-tm s)) ,, (suspension-is-unsuspendable-tm t)
suspension-is-unsuspendable-sub ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = (suspension-is-unsuspendable-sub ⟨ ⟨ σ , u ⟩ , s ⟩) ,, (suspension-is-unsuspendable-tm t)

susp-inj-ctx : suspCtx Γ ≃c suspCtx Δ → Γ ≃c Δ
susp-inj-ty : suspTy A ≃ty suspTy B → A ≃ty B
susp-inj-tm : suspTm s ≃tm suspTm t → s ≃tm t
susp-inj-sub : suspSub σ ≃s suspSub τ → σ ≃s τ


susp-inj-ctx {Γ = ∅} {Δ = ∅} p = Emp≃
susp-inj-ctx {Γ = ∅} {Δ = Δ , A} (Add≃ p x) with ≃c-preserve-length p
... | ()
susp-inj-ctx {Γ = Γ , A} {Δ = ∅} (Add≃ p x) with ≃c-preserve-length p
... | ()
susp-inj-ctx {Γ = Γ , A} {Δ = Δ , B} (Add≃ p x) = Add≃ (susp-inj-ctx p) (susp-inj-ty x)

susp-inj-ty {A = ⋆} {B = ⋆} (Arr≃ x (Star≃ p) x₁) = Star≃ (cong pred (cong pred p))
susp-inj-ty {A = ⋆} {B = s ─⟨ ⋆ ⟩⟶ t} (Arr≃ x p x₁) with ≃ty-preserve-height p
... | ()
susp-inj-ty {A = ⋆} {B = s ─⟨ s₁ ─⟨ B ⟩⟶ t₁ ⟩⟶ t} (Arr≃ x p x₁) with ≃ty-preserve-height p
... | ()
susp-inj-ty {A = s ─⟨ ⋆ ⟩⟶ t} {B = ⋆} p with ≃ty-preserve-height p
... | ()
susp-inj-ty {A = s ─⟨ s₁ ─⟨ A ⟩⟶ t₁ ⟩⟶ t} {B = ⋆} p with ≃ty-preserve-height p
... | ()
susp-inj-ty {A = s ─⟨ ⋆ ⟩⟶ t} {B = s₁ ─⟨ B ⟩⟶ t₁} (Arr≃ x p y) = Arr≃ (susp-inj-tm x) (susp-inj-ty p) (susp-inj-tm y)
susp-inj-ty {A = s ─⟨ s₂ ─⟨ A ⟩⟶ t₂ ⟩⟶ t} {B = s₁ ─⟨ B ⟩⟶ t₁} (Arr≃ x p y) = Arr≃ (susp-inj-tm x) (susp-inj-ty p) (susp-inj-tm y)

susp-inj-tm {s = Var i} {t = Var j} (Var≃ x y) = Var≃ (cong pred (cong pred x)) (begin
  toℕ i ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ i) ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ (inject₁ i)) ≡⟨ y ⟩
  toℕ (inject₁ (inject₁ j)) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ j) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ j ∎)
  where
    open ≡-Reasoning
susp-inj-tm {s = Var i} {t = Coh Δ A σ} ()
susp-inj-tm {s = Coh Δ A σ} {t = Var i} ()
susp-inj-tm {s = Coh Δ A σ} {t = Coh Δ₁ A₁ σ₁} (Coh≃ p q r) = Coh≃ (susp-inj-ctx p) (susp-inj-ty q) (susp-inj-sub r)

susp-inj-sub {σ = ⟨⟩} {τ = ⟨⟩} p = Null≃ (cong pred (cong pred (≃s-to-codomain-≡ p)))
susp-inj-sub {σ = ⟨⟩} {τ = ⟨ ⟨⟩ , t ⟩} (Ext≃ (Ext≃ () x₁) x)
susp-inj-sub {σ = ⟨⟩} {τ = ⟨ ⟨ τ , t₁ ⟩ , t ⟩} (Ext≃ (Ext≃ () x₁) x)
susp-inj-sub {σ = ⟨ ⟨⟩ , t ⟩} {τ = ⟨⟩} (Ext≃ (Ext≃ () x₁) x)
susp-inj-sub {σ = ⟨ ⟨ σ , t₁ ⟩ , t ⟩} {τ = ⟨⟩} (Ext≃ (Ext≃ () x₁) x)
susp-inj-sub {σ = ⟨ ⟨⟩ , t ⟩} {τ = ⟨ τ , t₁ ⟩} (Ext≃ p x) = Ext≃ (susp-inj-sub p) (susp-inj-tm x)
susp-inj-sub {σ = ⟨ ⟨ σ , t₂ ⟩ , t ⟩} {τ = ⟨ τ , t₁ ⟩} (Ext≃ p x) = Ext≃ (susp-inj-sub p) (susp-inj-tm x)

unsusp-susp-compat-ctx : (Γ : Ctx n) → unsuspend-ctx (suspCtx Γ) ⦃ suspension-is-unsuspendable-ctx Γ ⦄ ≃c Γ
unsusp-susp-compat-ty : (A : Ty n d) → unsuspend-ty (suspTy A) ⦃ suspension-is-unsuspendable-ty A ⦄ ≃ty A
unsusp-susp-compat-tm : (t : Tm n) → unsuspend-tm (suspTm t) ⦃ suspension-is-unsuspendable-tm t ⦄ ≃tm t
unsusp-susp-compat-sub : (σ : Sub n m) → (unsuspend-sub (suspSub σ) ⦃ suspension-is-unsuspendable-sub σ ⦄) ≃s σ

unsusp-susp-compat-ctx Γ = susp-inj-ctx (unsuspend-ctx-compat (suspCtx Γ) ⦃ suspension-is-unsuspendable-ctx Γ ⦄)

unsusp-susp-compat-ty A = susp-inj-ty (unsuspend-ty-compat (suspTy A) ⦃ suspension-is-unsuspendable-ty A ⦄)

unsusp-susp-compat-tm t = susp-inj-tm (unsuspend-tm-compat (suspTm t) ⦃ suspension-is-unsuspendable-tm t ⦄)

unsusp-susp-compat-sub σ = susp-inj-sub (unsuspend-sub-compat (suspSub σ) ⦃ suspension-is-unsuspendable-sub σ ⦄)
