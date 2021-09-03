{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Suspension.Base where

open import Catt.Syntax.Base
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

suspCtx : Ctx → Ctx
suspTy : Ty Γ → Ty (suspCtx Γ)
getFst : Tm (suspCtx Γ)
getSnd : Tm (suspCtx Γ)
suspTm : Tm Γ → Tm (suspCtx Γ)
suspSub : Sub Γ Δ ⋆ → Sub (suspCtx Γ) (suspCtx Δ) ⋆
convertIndex : (i : Fin (ctxLength Γ)) → Fin (ctxLength (suspCtx Γ))

suspCtx ∅ = ∅ , ⋆ , ⋆
suspCtx (Γ , A) = (suspCtx Γ) , (suspTy A)

suspTy ⋆ = getFst ─⟨ ⋆ ⟩⟶ getSnd
suspTy (s ─⟨ A ⟩⟶ t) = suspTm s ─⟨ suspTy A ⟩⟶ suspTm t

getFst {Γ = ∅} = 1V
getFst {Γ = Γ , A} = liftTerm getFst

getSnd {Γ = ∅} = 0V
getSnd {Γ = Γ , A} = liftTerm getSnd

suspTm (Var i) = Var (convertIndex i)
suspTm (Coh Δ A σ) = Coh (suspCtx Δ) (suspTy A) (suspSub σ)

suspSub ⟨⟩ = ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩
suspSub ⟨ σ , t ⟩ = ⟨ suspSub σ , suspTm t ⟩

convertIndex {Γ , A} zero = zero
convertIndex {Γ , A} (suc i) = suc (convertIndex i)

susp-ctx-n : (n : ℕ) → Ctx → Ctx
susp-ctx-n zero Γ = Γ
susp-ctx-n (suc n) Γ = susp-ctx-n n (suspCtx Γ)

susp-ty-n : (n : ℕ) → Ty Γ → Ty (susp-ctx-n n Γ)
susp-ty-n zero A = A
susp-ty-n (suc n) A = susp-ty-n n (suspTy A)

susp-sub-n : (n : ℕ) → Sub Γ Δ ⋆ → Sub (susp-ctx-n n Γ) (susp-ctx-n n Δ) ⋆
susp-sub-n zero σ = σ
susp-sub-n (suc n) σ = susp-sub-n n (suspSub σ)

susp-adjoint : Sub Γ Δ (s ─⟨ A ⟩⟶ t) → Sub (suspCtx Γ) Δ A
susp-adjoint {s = s} {t = t} ⟨⟩ = ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩
susp-adjoint ⟨ σ , t ⟩ = ⟨ (susp-adjoint σ) , t ⟩

ty-base-dim′ : ⦃ TyHeight (s ─⟨ A ⟩⟶ t) (suc d) ⦄ → TyHeight A d
ty-base-dim′ {d = _} ⦃ TyHeightS ⦃ x ⦄ ⦄ = x

sub-level : Sub Γ Δ A → ℕ
sub-level {A = A} σ = ty-dim A

sub-ty-height : (σ : Sub Γ Δ A) → TyHeight A (sub-level σ)
sub-ty-height {A = A} σ = get-ty-height A

susp-adjoint-full : (σ : Sub Γ Δ A) → Sub (susp-ctx-n (sub-level σ) Γ) Δ ⋆
susp-adjoint-full {A = ⋆} σ = σ
susp-adjoint-full {A = s ─⟨ A ⟩⟶ t} σ = susp-adjoint-full {A = A} (susp-adjoint σ)
