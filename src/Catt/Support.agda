{-# OPTIONS --without-K --safe --postfix-projections #-}

module Catt.Support where

open import Data.Nat hiding (_<_)
open import Data.Fin hiding (pred)
open import Data.Fin.Properties
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Syntax
open import Catt.Pasting
open import Catt.Vars
open import Data.Empty
open import Data.Unit
open import Data.Fin.Patterns
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions

open Tri

private
  variable
    Γ Δ : Ctx
    submax dim : ℕ

getLast : (σ : Sub Γ Δ) → VSub σ → Maybe (Fin (length Γ))
getLast ⟨⟩ vσ = nothing
getLast ⟨ σ , Var i ⟩ vσ = just i

Monotone : (σ : Sub Γ Δ) → VSub σ → Set
Monotone ⟨⟩ vsub = ⊤
Monotone ⟨ σ , Var i ⟩ (vσ ,, vx) = Monotone σ vσ × maybe′ (λ j → j < i) ⊤ (getLast σ vσ)

record SubCtx (Γ : Ctx) : Set where
  constructor ⟪_+_+_+_⟫
  field
    SrcCtx : Ctx
    Inc : Sub Γ SrcCtx
    VInc : VSub Inc
    Mon : Monotone Inc VInc

open SubCtx

subCtxUnionCtx : (a b : SubCtx Γ) → Ctx
subCtxUnionCtx ⟪ ∅ + σ + vσ + mσ ⟫ ⟪ Δ + τ + vτ + mτ ⟫ = Δ
subCtxUnionCtx ⟪ Υ , A + σ + vσ + mσ ⟫ ⟪ Δ + τ + vτ + mτ ⟫ = {!!}

subCtxUnion : (a b : SubCtx Γ) → SubCtx Γ
subCtxUnion ⟪ ∅ + σ + vσ + mσ ⟫ ⟪ Δ + τ + vτ + mτ ⟫ = ⟪ Δ + τ + vτ + mτ ⟫
subCtxUnion ⟪ Υ , A + σ + vσ + mσ ⟫ ⟪ ∅ + τ + vτ + mτ ⟫ = ⟪ Υ , A + σ + vσ + mσ ⟫
subCtxUnion ⟪ Υ , A + ⟨ σ , Var i ⟩ + vσ ,, vx + mσ ,, mi ⟫ ⟪ Δ , B + ⟨ τ , Var j ⟩ + vτ ,, vy + mτ ,, mj ⟫ with <-cmp i j
... | tri< a ¬b ¬c = {!!} --  with subCtxUnion ⟪ Υ , A + ⟨ σ , Var i ⟩ + vσ ,, vx + mσ ,, mi ⟫ ⟪ Δ + τ + vτ + mτ ⟫
-- ...   | p  = {!!}

... | tri≈ ¬a b ¬c = {!!}
... | tri> ¬a ¬b c = {!!}

disk-ctx : ℕ → Ctx
disk-pdb : (n : ℕ) → (disk-ctx n ⊢pd[ 0 ][ n ])

disk-ctx zero = ∅ , ⋆
disk-ctx (suc n) = extend (disk-pdb n)

disk-pdb zero = Base
disk-pdb (suc n) = ExtendM (disk-pdb n)

disk-pd : (n : ℕ) → (disk-ctx n ⊢pd₀ n)
disk-pd n = restrict-to-pd (disk-pdb n)

disk-sub : VCtx Γ → (t : Term Γ dim) → VTerm t → Sub Γ (disk-ctx dim)
disk-sub {Γ} vctx x@(Var i) vtm with retrieveDim Γ i | Var i | Γ ‼ i | vLookup vctx i
... | zero | v | A | vA = ⟨ ⟨⟩ , v ⟩
... | suc dim | v | s ─⟨ A ⟩⟶ t | vs ,, vt ,, vA = ⟨ ⟨ (disk-sub vctx s vs) , t ⟩ , v ⟩

sub-support-ctx : Δ ⊢pd[ submax ][ dim ] → Sub Γ Δ → Ctx
support-ctx : Term Γ dim → Ctx

sub-support-ctx Base ⟨ ⟨⟩ , x ⟩ = support-ctx x
sub-support-ctx (ExtendM pdb) ⟨ ⟨ σ , tgt ⟩ , fill ⟩ = {!!}
sub-support-ctx (Extend pdb) σ = {!!}
sub-support-ctx (Restr pdb) σ = {!!}

support-ctx {dim = dim} (Var i) = disk-ctx dim
support-ctx (Coh Δ A σ) = {!!}

SourceFree : ∀ Γ → VCtx Γ → Fin (length Γ) → Set
SourceFree (Γ , A) vΓ 0F = ⊤
SourceFree (Γ , ⋆) (vΓ ,, tt) (suc i) = SourceFree Γ vΓ i
SourceFree (Γ , Var j ─⟨ A ⟩⟶ t) (vΓ ,, vs ,, vt ,, vA) (suc i) = SourceFree Γ vΓ i × j ≢ i
