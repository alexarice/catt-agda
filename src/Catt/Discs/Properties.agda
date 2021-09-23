{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Discs.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Tree
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Data.Fin using (Fin; suc; zero; inject₁; fromℕ)
open import Catt.Globular
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Catt.Globular
open import Catt.Globular.Properties

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
linear-tree-compat (Join S Sing) = trans≃c (susp-ctx-≃ (linear-tree-compat S)) (disc-susp (tree-dim S))

sub-from-sphere-prop : (A : Ty n) → sphere-type (ty-dim A) [ sub-from-sphere A ]ty ≃ty A
sub-from-sphere-prop ⋆ = refl≃ty
sub-from-sphere-prop (s ─⟨ A ⟩⟶ t) = Arr≃ refl≃tm (trans≃ty (lift-sub-comp-lem-ty ⟨ sub-from-sphere A , s ⟩ (liftType (sphere-type _))) (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere A) (sphere-type _)) (sub-from-sphere-prop A))) refl≃tm

sub-from-disc-tm-≃ : A ≃ty B → s ≃tm t → sub-from-disc A s ≃s sub-from-disc B t
sub-from-sphere-ty-≃ : A ≃ty B → sub-from-sphere A ≃s sub-from-sphere B

sub-from-disc-tm-≃ p q = Ext≃ (sub-from-sphere-ty-≃ p) q

sub-from-sphere-ty-≃ (Star≃ x) = Null≃ (Star≃ x)
sub-from-sphere-ty-≃ (Arr≃ p q r) = Ext≃ (Ext≃ (sub-from-sphere-ty-≃ q) p) r

-- disc-to-subbed-tm : sub-from-disc (t [ σ ]tm) ≃s σ ∘ sub-from-disc t
-- disc-to-subbed-tm = Ext≃ {!!} refl≃tm

sphere-to-subbed-ty : (A : Ty n) → (σ : Sub n m ⋆) → sub-from-sphere (A [ σ ]ty) ≃s σ ∘ sub-from-sphere A
sphere-to-subbed-ty ⋆ σ = refl≃s
sphere-to-subbed-ty (s ─⟨ A ⟩⟶ t) σ = Ext≃ (Ext≃ (sphere-to-subbed-ty A σ) refl≃tm) refl≃tm

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
