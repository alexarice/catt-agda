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
-- dim-of-unsuspend : (Γ : Ctx (suc (suc n))) → (us : is-unsuspendable-ctx Γ) → suc (ctx-dim (unsuspend-ctx Γ us)) ≡ ctx-dim Γ
is-unsuspendable-ty : (Γ : Ctx n) → (A : Ty Δ d) → suspCtx Γ ≃c Δ → Set
unsuspend-ty : (A : Ty Δ d)
             → (Γ : Ctx n)
             → (p : suspCtx Γ ≃c Δ)
             → .⦃ is-unsuspendable-ty Γ A p ⦄
             → Ty Γ (pred d)
unsuspend-ty-compat : (A : Ty Δ d)
                    → (Γ : Ctx n)
                    → (p : suspCtx Γ ≃c Δ)
                    → .⦃ _ : is-unsuspendable-ty Γ A p ⦄
                    → suspTy (unsuspend-ty A Γ p) ≃ty A
is-unsuspendable-tm : (Γ : Ctx n) → (t : Tm Δ) → suspCtx Γ ≃c Δ → Set
unsuspend-tm : (t : Tm Δ)
             → (Γ : Ctx n)
             → (p : suspCtx Γ ≃c Δ)
             → .⦃ is-unsuspendable-tm Γ t p ⦄
             → Tm Γ
unsuspend-tm-compat : (t : Tm Δ)
                    → (Γ : Ctx n)
                    → (p : suspCtx Γ ≃c Δ)
                    → .⦃ _ : is-unsuspendable-tm Γ t p ⦄
                    → suspTm (unsuspend-tm t Γ p) ≃tm t
is-unsuspendable-sub : (Γ : Ctx n) → (Δ : Ctx m) → Sub Γ′ Δ′ → suspCtx Γ ≃c Γ′ → suspCtx Δ ≃c Δ′ → Set
unsuspend-sub : (σ : Sub Γ′ Δ′)
              → (Γ : Ctx n)
              → (Δ : Ctx m)
              → (p : suspCtx Γ ≃c Γ′)
              → (q : suspCtx Δ ≃c Δ′)
              → .⦃ is-unsuspendable-sub Γ Δ σ p q ⦄
              → Sub Γ Δ
unsuspend-sub-compat : (σ : Sub Γ′ Δ′)
                     → (Γ : Ctx n)
                     → (Δ : Ctx m)
                     → (p : suspCtx Γ ≃c Γ′)
                     → (q : suspCtx Δ ≃c Δ′)
                     → .⦃ _ : is-unsuspendable-sub Γ Δ σ p q ⦄
                     → suspSub (unsuspend-sub σ Γ Δ p q) ≃s σ

is-unsuspendable-ctx ∅ = ⊥
is-unsuspendable-ctx (∅ , A) = ⊥
is-unsuspendable-ctx (∅ , ⋆ , ⋆) = ⊤
is-unsuspendable-ctx (∅ , ⋆ , _ ─⟨ _ ⟩⟶ _) = ⊥
is-unsuspendable-ctx (∅ , _ ─⟨ _ ⟩⟶ _ , _) = ⊥
is-unsuspendable-ctx (Γ , A , B , C) = Σ[ p ∈ is-unsuspendable-ctx (Γ , A , B) ] is-unsuspendable-ty (unsuspend-ctx (Γ , A , B) ⦃ p ⦄) C (unsuspend-ctx-compat (Γ , A , B) ⦃ p ⦄)

unsuspend-ctx (∅ , ⋆ , ⋆) = ∅
unsuspend-ctx (Γ , A , B , C) ⦃ usc ⦄ = (unsuspend-ctx (Γ , A , B) ⦃ proj₁ usc ⦄) , unsuspend-ty C (unsuspend-ctx (Γ , A , B) ⦃ proj₁ usc ⦄) (unsuspend-ctx-compat (Γ , A , B) ⦃ proj₁ usc ⦄) ⦃ proj₂ usc ⦄

unsuspend-ctx-compat (∅ , ⋆ , ⋆) = refl≃c
unsuspend-ctx-compat (Γ , A , B , C) ⦃ us ⦄ = Add≃ (unsuspend-ctx-compat (Γ , A , B) ⦃ proj₁ us ⦄) (unsuspend-ty-compat C (unsuspend-ctx (Γ , A , B) ⦃ proj₁ us ⦄) (unsuspend-ctx-compat (Γ , A , B) ⦃ proj₁ us ⦄) ⦃ proj₂ us ⦄)

-- dim-of-unsuspend (∅ , ⋆ , ⋆) us = refl
-- dim-of-unsuspend (Γ , A , B , C) us = cong₂ _⊔_ {u = suc (pred (ty-dim C))} (dim-of-unsuspend (Γ , A , B) (proj₁ us)) (suc[pred[n]]≡n (lem C))
--   where
--     lem : (A : Ty Γ′ n′) → n′ ≢ 0
--     lem ⋆ ()
--     lem (s ─⟨ A ⟩⟶ t) ()

is-unsuspendable-ty Γ ⋆ p = ⊥
is-unsuspendable-ty Γ (s ─⟨ ⋆ ⟩⟶ t) p = getFst Γ ≃tm s × getSnd Γ ≃tm t
is-unsuspendable-ty Γ (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) p = is-unsuspendable-ty Γ A p × is-unsuspendable-tm Γ s p × is-unsuspendable-tm Γ t p

unsuspend-ty (s ─⟨ ⋆ ⟩⟶ t) Γ p = ⋆
unsuspend-ty (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) Γ p ⦃ x ⦄ = (unsuspend-tm s Γ p ⦃ proj₁ (proj₂ x) ⦄) ─⟨ unsuspend-ty A Γ p ⦃ proj₁ x ⦄ ⟩⟶ unsuspend-tm t Γ p ⦃ proj₂ (proj₂ x) ⦄

unsuspend-ty-compat (s ─⟨ ⋆ ⟩⟶ t) Γ p ⦃ x ⦄ = Arr≃ (recompute (≃tm-dec (getFst Γ) s) (proj₁ x)) (Star≃ p) (recompute (≃tm-dec (getSnd Γ) t) (proj₂ x))
unsuspend-ty-compat (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) Γ p ⦃ x ⦄ = Arr≃ (unsuspend-tm-compat s Γ p ⦃ proj₁ (proj₂ x) ⦄) (unsuspend-ty-compat A Γ p ⦃ proj₁ x ⦄) (unsuspend-tm-compat t Γ p ⦃ proj₂ (proj₂ x) ⦄)

is-unsuspendable-tm Γ (Var i) p = toℕ i < ctxLength Γ
is-unsuspendable-tm Γ (Coh {n = zero} Δ A σ) p = ⊥
is-unsuspendable-tm Γ (Coh {n = suc zero} Δ A σ) p = ⊥
is-unsuspendable-tm Γ (Coh {n = suc (suc n)} Δ A σ) p = Σ[ q ∈ is-unsuspendable-ctx Δ ] is-unsuspendable-ty (unsuspend-ctx Δ ⦃ q ⦄) A (unsuspend-ctx-compat Δ ⦃ q ⦄) × is-unsuspendable-sub (unsuspend-ctx Δ ⦃ q ⦄) Γ σ (unsuspend-ctx-compat Δ ⦃ q ⦄) p

unsuspend-tm (Var i) Γ p = Var (fromℕ< (recompute (toℕ i <? ctxLength Γ) it))
unsuspend-tm (Coh {n = suc (suc n)} Δ A σ) Γ p ⦃ x ⦄ = Coh (unsuspend-ctx Δ ⦃ proj₁ x ⦄) (unsuspend-ty A (unsuspend-ctx Δ ⦃ proj₁ x ⦄) (unsuspend-ctx-compat Δ ⦃ proj₁ x ⦄) ⦃ proj₁ (proj₂ x) ⦄) (unsuspend-sub σ (unsuspend-ctx Δ ⦃ proj₁ x ⦄) Γ (unsuspend-ctx-compat Δ ⦃ proj₁ x ⦄) p ⦃ proj₂ (proj₂ x) ⦄)

unsuspend-tm-compat (Var i) Γ p = Var≃ p (begin
  toℕ (inject₁ (inject₁ (fromℕ< (recompute (toℕ i <? ctxLength Γ) _)))) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ (fromℕ< (recompute (toℕ i <? ctxLength Γ) _))) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ (fromℕ< (recompute (toℕ i <? ctxLength Γ) _)) ≡⟨ toℕ-fromℕ< _ ⟩
  toℕ i ∎)
  where
    open ≡-Reasoning
unsuspend-tm-compat (Coh {n = suc (suc n)} Δ A σ) Γ p ⦃ x ⦄ = Coh≃ (unsuspend-ctx-compat Δ ⦃ proj₁ x ⦄) (unsuspend-ty-compat A (unsuspend-ctx Δ ⦃ proj₁ x ⦄) (unsuspend-ctx-compat Δ ⦃ proj₁ x ⦄) ⦃ proj₁ (proj₂ x) ⦄) (unsuspend-sub-compat σ (unsuspend-ctx Δ ⦃ proj₁ x ⦄) Γ (unsuspend-ctx-compat Δ ⦃ proj₁ x ⦄) p ⦃ proj₂ (proj₂ x) ⦄)

is-unsuspendable-sub Γ Δ ⟨ ⟨⟩ , t ⟩ p q = ⊥
is-unsuspendable-sub Γ Δ ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ p q = getFst Δ ≃tm s × getSnd Δ ≃tm t
is-unsuspendable-sub ∅ Δ ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ (Add≃ (Add≃ () x₁) x) q
is-unsuspendable-sub (Γ , A) Δ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ (Add≃ p _) q = is-unsuspendable-sub Γ Δ ⟨ ⟨ σ , u ⟩ , s ⟩ p q × is-unsuspendable-tm Δ t q

unsuspend-sub ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ ∅ Δ p q = ⟨⟩
unsuspend-sub ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ (Γ , A) Δ p q with cong (λ - → pred (pred -)) (≃c-preserve-length p)
... | ()
unsuspend-sub ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ ∅ Δ (Add≃ (Add≃ () x₂) x₁) q
unsuspend-sub ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ (Γ , A) Δ (Add≃ p y) q ⦃ x ⦄ = ⟨ unsuspend-sub ⟨ ⟨ σ , u ⟩ , s ⟩ Γ Δ p q ⦃ proj₁ x ⦄ , unsuspend-tm t Δ q ⦃ proj₂ x ⦄ ⟩

unsuspend-sub-compat ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ ∅ Δ p q ⦃ x ⦄ = Ext≃ (Ext≃ (Null≃ q) (recompute (≃tm-dec (getFst Δ) s) (proj₁ x))) (recompute (≃tm-dec (getSnd Δ) t) (proj₂ x))
-- Ext≃ (Ext≃ Null≃ (proj₁ x)) (proj₂ x)
unsuspend-sub-compat ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ (Γ , A) Δ p q with cong (λ - → pred (pred -)) (≃c-preserve-length p)
... | ()
unsuspend-sub-compat ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ ∅ Δ (Add≃ (Add≃ () x₂) x₁) q
unsuspend-sub-compat ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ (Γ , A) Δ (Add≃ p x₁) q ⦃ x ⦄ = Ext≃ (unsuspend-sub-compat ⟨ ⟨ σ , u ⟩ , s ⟩ Γ Δ p q ⦃ proj₁ x ⦄) (unsuspend-tm-compat t Δ q ⦃ proj₂ x ⦄)


suspension-is-unsuspendable-ctx :  (Γ : Ctx n) → is-unsuspendable-ctx (suspCtx Γ)
suspension-is-unsuspendable-ty : (Γ : Ctx n) → (A : Ty Δ d) → (p : suspCtx Γ ≃c suspCtx Δ) → is-unsuspendable-ty Γ (suspTy A) p
suspension-is-unsuspendable-tm : (Γ : Ctx n) → (t : Tm Δ) → (p : suspCtx Γ ≃c suspCtx Δ) → is-unsuspendable-tm Γ (suspTm t) p
suspension-is-unsuspendable-sub : (Γ : Ctx n) → (Δ : Ctx m) → (σ : Sub Γ′ Δ′) → (p : suspCtx Γ ≃c suspCtx Γ′) → (q : suspCtx Δ ≃c suspCtx Δ′) → is-unsuspendable-sub Γ Δ (suspSub σ) p q

suspension-is-unsuspendable-ctx ∅ = tt
suspension-is-unsuspendable-ctx (∅ , A) = tt ,, (suspension-is-unsuspendable-ty ∅ A refl≃c)
suspension-is-unsuspendable-ctx (∅ , A , B) = let
  instance _ = suspension-is-unsuspendable-ty ∅ A refl≃c
  in (tt ,, it) ,,  suspension-is-unsuspendable-ty (unsuspend-ctx (∅ , ⋆ , ⋆ , suspTy A) ⦃ tt ,, it ⦄) B (Add≃ refl≃c (unsuspend-ty-compat (suspTy A) ∅ refl≃c ))
suspension-is-unsuspendable-ctx (Γ , A , B , C) = let
  instance _ = suspension-is-unsuspendable-ctx (Γ , A , B)
  in it ,, suspension-is-unsuspendable-ty (unsuspend-ctx (suspCtx Γ , suspTy A , suspTy B)) C (unsuspend-ctx-compat (suspCtx Γ , suspTy A , suspTy B))

suspension-is-unsuspendable-ty Γ ⋆ p = getFst-Lem p ,, getSnd-Lem p
suspension-is-unsuspendable-ty Γ (s ─⟨ ⋆ ⟩⟶ t) p = (getFst-Lem p ,, getSnd-Lem p) ,, (suspension-is-unsuspendable-tm Γ s p) ,, (suspension-is-unsuspendable-tm Γ t p)
suspension-is-unsuspendable-ty Γ (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) p = (suspension-is-unsuspendable-ty Γ A p) ,, ((suspension-is-unsuspendable-tm Γ s p) ,, (suspension-is-unsuspendable-tm Γ t p))

suspension-is-unsuspendable-tm {Δ = Δ} Γ (Var i) p = ≤-trans (≤-reflexive (cong suc (trans (toℕ-inject₁ _) (toℕ-inject₁ _)))) (≤-trans (toℕ<n i) (≤-reflexive (sym (cong (λ - → pred (pred -)) (≃c-preserve-length p)))))
suspension-is-unsuspendable-tm Γ (Coh Δ A σ) p = let
  instance _ = suspension-is-unsuspendable-ctx Δ
  in (suspension-is-unsuspendable-ctx Δ) ,, (suspension-is-unsuspendable-ty (unsuspend-ctx (suspCtx Δ)) A (unsuspend-ctx-compat (suspCtx Δ)) ,, suspension-is-unsuspendable-sub (unsuspend-ctx (suspCtx Δ)) Γ σ (unsuspend-ctx-compat (suspCtx Δ)) p)

suspension-is-unsuspendable-sub Γ Δ ⟨⟩ p q = getFst-Lem q ,, getSnd-Lem q
suspension-is-unsuspendable-sub ∅ Δ ⟨ ⟨⟩ , t ⟩ (Add≃ (Add≃ () x₁) x) q
suspension-is-unsuspendable-sub (Γ , A) Δ ⟨ ⟨⟩ , t ⟩ (Add≃ p x) q = (getFst-Lem q ,, getSnd-Lem q) ,, (suspension-is-unsuspendable-tm Δ t q)
suspension-is-unsuspendable-sub ∅ Δ ⟨ ⟨ σ , t₁ ⟩ , t ⟩ (Add≃ (Add≃ () x₁) x) q
suspension-is-unsuspendable-sub (∅ , A) Δ ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ (Add≃ (Add≃ (Add≃ () x₂) x₁) x) q
suspension-is-unsuspendable-sub (Γ , A₁ , A) Δ ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ (Add≃ (Add≃ p x₁) x) q = ((getFst-Lem q ,, getSnd-Lem q) ,, suspension-is-unsuspendable-tm Δ t₁ q) ,, suspension-is-unsuspendable-tm Δ t q
suspension-is-unsuspendable-sub (∅ , A) Δ ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ (Add≃ (Add≃ (Add≃ () x₂) x₁) x) q
suspension-is-unsuspendable-sub (Γ , A₁ , A) Δ ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ (Add≃ (Add≃ p x₁) x) q = (suspension-is-unsuspendable-sub (Γ , A₁) Δ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ (Add≃ p x₁) q) ,, (suspension-is-unsuspendable-tm Δ t q)

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

susp-inj-ty {A = ⋆} {B = ⋆} (Arr≃ x (Star≃ p) x₁) = Star≃ (susp-inj-ctx p)
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

susp-inj-tm {s = Var i} {t = Var j} (Var≃ x y) = Var≃ (susp-inj-ctx x) (begin
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

susp-inj-sub {σ = ⟨⟩} {τ = ⟨⟩} p = Null≃ (susp-inj-ctx (≃s-to-codomain-≃c p))
susp-inj-sub {σ = ⟨⟩} {τ = ⟨ ⟨⟩ , t ⟩} (Ext≃ (Ext≃ () x₁) x)
susp-inj-sub {σ = ⟨⟩} {τ = ⟨ ⟨ τ , t₁ ⟩ , t ⟩} (Ext≃ (Ext≃ () x₁) x)
susp-inj-sub {σ = ⟨ ⟨⟩ , t ⟩} {τ = ⟨⟩} (Ext≃ (Ext≃ () x₁) x)
susp-inj-sub {σ = ⟨ ⟨ σ , t₁ ⟩ , t ⟩} {τ = ⟨⟩} (Ext≃ (Ext≃ () x₁) x)
susp-inj-sub {σ = ⟨ ⟨⟩ , t ⟩} {τ = ⟨ τ , t₁ ⟩} (Ext≃ p x) = Ext≃ (susp-inj-sub p) (susp-inj-tm x)
susp-inj-sub {σ = ⟨ ⟨ σ , t₂ ⟩ , t ⟩} {τ = ⟨ τ , t₁ ⟩} (Ext≃ p x) = Ext≃ (susp-inj-sub p) (susp-inj-tm x)

unsusp-susp-compat-ctx : (Γ : Ctx n) → unsuspend-ctx (suspCtx Γ) ⦃ suspension-is-unsuspendable-ctx Γ ⦄ ≃c Γ
unsusp-susp-compat-ty : (Γ : Ctx n) → (A : Ty Δ d) → (p : suspCtx Γ ≃c suspCtx Δ) → unsuspend-ty (suspTy A) Γ p ⦃ suspension-is-unsuspendable-ty Γ A p ⦄ ≃ty A
unsusp-susp-compat-tm : (Γ : Ctx n) → (t : Tm Δ) → (p : suspCtx Γ ≃c suspCtx Δ) → unsuspend-tm (suspTm t) Γ p ⦃ suspension-is-unsuspendable-tm Γ t p ⦄ ≃tm t
unsusp-susp-compat-sub : (Γ : Ctx n) → (Δ : Ctx m) → (σ : Sub Γ′ Δ′) → (p : suspCtx Γ ≃c suspCtx Γ′) → (q : suspCtx Δ ≃c suspCtx Δ′) → (unsuspend-sub (suspSub σ) Γ Δ p q ⦃ suspension-is-unsuspendable-sub Γ Δ σ p q ⦄) ≃s σ

unsusp-susp-compat-ctx Γ = susp-inj-ctx (unsuspend-ctx-compat (suspCtx Γ) ⦃ suspension-is-unsuspendable-ctx Γ ⦄)

unsusp-susp-compat-ty Γ A p = susp-inj-ty (unsuspend-ty-compat (suspTy A) Γ p ⦃ suspension-is-unsuspendable-ty Γ A p ⦄)

unsusp-susp-compat-tm Γ t p = susp-inj-tm (unsuspend-tm-compat (suspTm t) Γ p ⦃ suspension-is-unsuspendable-tm Γ t p ⦄)

unsusp-susp-compat-sub Γ Δ σ p q = susp-inj-sub (unsuspend-sub-compat (suspSub σ) Γ Δ p q ⦃ suspension-is-unsuspendable-sub Γ Δ σ p q ⦄)
