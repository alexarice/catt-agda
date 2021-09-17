{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Discs.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Data.Fin using (Fin; suc; zero; inject₁; fromℕ)
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
import Relation.Binary.Reasoning.Setoid as Reasoning

sub-from-sphere-prop : (A : Ty n d) → sphere-type d [ sub-from-sphere A ]ty ≃ty A
sub-from-sphere-prop ⋆ = refl≃ty
sub-from-sphere-prop (s ─⟨ A ⟩⟶ t) = Arr≃ refl≃tm (trans≃ty (lift-sub-comp-lem-ty ⟨ sub-from-sphere A , s ⟩ (liftType (sphere-type _))) (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere A) (sphere-type _)) (sub-from-sphere-prop A))) refl≃tm

-- sub-from-disc-tm-≃ : {s : Tm Γ (suc (suc d))} → {t : Tm Δ (suc (suc d′))} → Γ ≃c Δ → s ≃tm t → sub-from-disc s ≃s sub-from-disc t
-- sub-from-sphere-ty-≃ : {A : Ty Γ (suc d)} {B : Ty Δ (suc d′)} → Γ ≃c Δ → A ≃ty B → sub-from-sphere A ≃s sub-from-sphere B

-- sub-from-disc-tm-≃ p q = Ext≃ (sub-from-sphere-ty-≃ p (tm-to-ty-≃ p q)) q

-- sub-from-sphere-ty-≃ p Star≃ = Null≃
-- sub-from-sphere-ty-≃ {d = suc d} {d′ = suc d′} p (Arr≃ q r s) = Ext≃ (sub-from-disc-tm-≃ p q) s

-- disc-to-subbed-tm : sub-from-disc (t [ σ ]tm) ≃s σ ∘ sub-from-disc t
-- disc-to-subbed-tm = Ext≃ {!!} refl≃tm

sphere-to-subbed-ty : (A : Ty n d) → (σ : Sub n m) → sub-from-sphere (A [ σ ]ty) ≃s σ ∘ sub-from-sphere A
sphere-to-subbed-ty ⋆ σ = refl≃s
sphere-to-subbed-ty (s ─⟨ A ⟩⟶ t) σ = Ext≃ (Ext≃ (sphere-to-subbed-ty A σ) refl≃tm) refl≃tm

Disc-pdb : (n : ℕ) → Disc n ⊢pd[ 0 ][ n ]
Disc-pdb-foc-ty : (n : ℕ) → liftType (sphere-type n) ≃ty getFocusType (Disc-pdb n)
Disc-pdb-foc-tm : (n : ℕ) → 0V {disc-size n} ≃tm getFocusTerm (Disc-pdb n)



Disc-pdb zero = Base
Disc-pdb (suc n) = Extend (Disc-pdb n) (Disc-pdb-foc-ty n) (Arr≃ (lift-tm-≃ (Disc-pdb-foc-tm n)) (lift-ty-≃ (Disc-pdb-foc-ty n)) refl≃tm)

Disc-pdb-foc-ty zero = refl≃ty
Disc-pdb-foc-ty (suc n) = refl≃ty

Disc-pdb-foc-tm zero = refl≃tm
Disc-pdb-foc-tm (suc n) = refl≃tm

Disc-pd : (n : ℕ) → Disc n ⊢pd₀ n
Disc-pd n = restr-to-pd (Disc-pdb n)

right-base-sphere : (n : ℕ) → get-right-base-tm (sphere-type (suc n)) ≃tm Var {n = sphere-size (suc n)} (inject₁ (fromℕ _))
right-base-sphere zero = refl≃tm
right-base-sphere (suc n) = begin
  < get-right-base-tm (liftType (liftType (sphere-type (suc n)))) >tm
    ≈⟨ get-right-base-tm-lift (liftType (sphere-type (suc n))) ⟩
  < liftTerm (get-right-base-tm (liftType (sphere-type (suc n)))) >tm
    ≈⟨ lift-tm-≃ (get-right-base-tm-lift (sphere-type (suc n))) ⟩
  < liftTerm (liftTerm (get-right-base-tm (sphere-type (suc n)))) >tm
    ≈⟨ lift-tm-≃ (lift-tm-≃ (right-base-sphere n)) ⟩
  < (Var (suc (suc (inject₁ (fromℕ (sphere-size n)))))) >tm ∎
  where
    open Reasoning tm-setoid

pd-focus-disc-is-snd : (n : ℕ) → pd-focus-tm (Disc-pd (suc n)) ≃tm Var {n = disc-size (suc n)} (inject₁ (fromℕ _))
pd-focus-disc-is-snd n = trans≃tm (restr-to-pd-foc-tm (Disc-pdb (suc n))) (trans≃tm (get-right-base-tm-lift (sphere-type (suc n))) (lift-tm-≃ (right-base-sphere n)))

sub-from-sphere-snd : (A : Ty n (suc d)) → Var (inject₁ (fromℕ _)) [ sub-from-sphere A ]tm ≃tm get-right-base-tm A
sub-from-sphere-snd {d = zero} (s ─⟨ A ⟩⟶ t) = refl≃tm
sub-from-sphere-snd {d = suc d} (s ─⟨ A ⟩⟶ t) = sub-from-sphere-snd A
