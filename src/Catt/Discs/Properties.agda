{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Discs.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Globular.Properties
open import Relation.Nullary
open import Catt.Tree

disc-≡ : .(d ≡ d′) → Disc d ≃c Disc d′
disc-≡ p with recompute (_ ≟ _) p
... | refl = refl≃c

disc-susp : (n : ℕ) → suspCtx (Disc n) ≃c Disc (suc n)
sphere-susp : (n : ℕ) → suspCtx (Sphere n) ≃c Sphere (suc n)
sphere-type-susp : (n : ℕ) → suspTy (sphere-type n) ≃ty sphere-type (suc n)

disc-susp zero = refl≃c
disc-susp (suc n) = Add≃ (sphere-susp (suc n)) (sphere-type-susp (suc n))

sphere-susp zero = refl≃c
sphere-susp (suc n) = Add≃ (disc-susp n) (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n)))

sphere-type-susp zero = refl≃ty
sphere-type-susp (suc n) = Arr≃ (refl≃tm) (trans≃ty (susp-ty-lift (liftType (sphere-type n))) (lift-ty-≃ (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n))))) (refl≃tm)

linear-tree-compat : (T : Tree n) → .⦃ _ : is-linear T ⦄ → tree-to-ctx T ≃c Disc (tree-dim T)
linear-tree-compat Sing = Add≃ Emp≃ (Star≃ refl)
linear-tree-compat (Join S Sing) = trans≃c (susp-ctx-≃ (linear-tree-compat S)) (trans≃c (disc-susp (tree-dim S)) (disc-≡ (sym (max-lem (suc (tree-dim S))))))

sub-from-sphere-prop : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → sphere-type d [ sub-from-sphere d A p ]ty ≃ty A
sub-from-sphere-prop zero ⋆ p = refl≃ty
sub-from-sphere-prop (suc d) (s ─⟨ A ⟩⟶ t) p = Arr≃ refl≃tm (trans≃ty (lift-sub-comp-lem-ty ⟨ sub-from-sphere d A (cong pred p) , s ⟩ (liftType (sphere-type _))) (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere d A (cong pred p)) (sphere-type _)) (sub-from-sphere-prop d A (cong pred p)))) refl≃tm

sub-from-disc-tm-≃ : (d₁ d₂ : ℕ) → A ≃ty B → .(p : ty-dim A ≡ d₁) → .(q : ty-dim B ≡ d₂) → s ≃tm t → sub-from-disc d₁ A p s ≃s sub-from-disc d₂ B q t
sub-from-sphere-ty-≃ : (d₁ d₂ : ℕ) → A ≃ty B → .(p : ty-dim A ≡ d₁) → .(q : ty-dim B ≡ d₂) → sub-from-sphere d₁ A p ≃s sub-from-sphere d₂ B q

sub-from-disc-tm-≃ d₁ d₂ a b c d = Ext≃ (sub-from-sphere-ty-≃ d₁ d₂ a b c) d

sub-from-sphere-ty-≃ zero zero (Star≃ x) p q = Null≃ (Star≃ x)
sub-from-sphere-ty-≃ (suc d₁) (suc d₂) (Arr≃ a b c) p q = Ext≃ (Ext≃ (sub-from-sphere-ty-≃ d₁ d₂ b (cong pred p) (cong pred q)) a) c

-- disc-to-subbed-tm : sub-from-disc (t [ σ ]tm) ≃s σ ∘ sub-from-disc t
-- disc-to-subbed-tm = Ext≃ {!!} refl≃tm

sphere-to-subbed-ty : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (σ : Sub n m ⋆) → sub-from-sphere d (A [ σ ]ty) (trans (sym (sub-dim σ A)) p) ≃s σ ∘ sub-from-sphere d A p
sphere-to-subbed-ty zero ⋆ p σ = refl≃s
sphere-to-subbed-ty (suc d) (s ─⟨ A ⟩⟶ t) p σ = Ext≃ (Ext≃ (sphere-to-subbed-ty d A (cong pred p) σ) refl≃tm) refl≃tm

-- right-base-sphere : (n : ℕ) → get-right-base-tm (sphere-type (suc n)) ≃tm Var {n = sphere-size (suc n)} (inject₁ (fromℕ _))
-- right-base-sphere zero = refl≃tm
-- right-base-sphere (suc n) = begin
--   < get-right-base-tm (liftType (liftType (sphere-type (suc n)))) >tm
--     ≈⟨ get-right-base-tm-lift (liftType (sphere-type (suc n))) ⟩
--   < liftTerm (get-right-base-tm (liftType (sphere-type (suc n)))) >tm
--     ≈⟨ lift-tm-≃ (get-right-base-tm-lift (sphere-type (suc n))) ⟩
--   < liftTerm (liftTerm (get-right-base-tm (sphere-type (suc n)))) >tm
--     ≈⟨ lift-tm-≃ (lift-tm-≃ (right-base-sphere n)) ⟩
--   < (Var (suc (suc (inject₁ (fromℕ (sphere-size n)))))) >tm ∎
--   where
--     open Reasoning tm-setoid

-- pd-focus-disc-is-snd : (n : ℕ) → pd-focus-tm (Disc-pd (suc n)) ≃tm Var {n = disc-size (suc n)} (inject₁ (fromℕ _))
-- pd-focus-disc-is-snd n = trans≃tm (restr-to-pd-foc-tm (Disc-pdb (suc n))) (trans≃tm (get-right-base-tm-lift (sphere-type (suc n))) (lift-tm-≃ (right-base-sphere n)))

-- sub-from-sphere-snd : (A : Ty n (suc d)) → Var (inject₁ (fromℕ _)) [ sub-from-sphere A ]tm ≃tm get-right-base-tm A
-- sub-from-sphere-snd {d = zero} (s ─⟨ A ⟩⟶ t) = refl≃tm
-- sub-from-sphere-snd {d = suc d} (s ─⟨ A ⟩⟶ t) = sub-from-sphere-snd A
