{-# OPTIONS --without-K --safe #-}

module Catt.Support where

open import Data.Nat
open import Data.Fin hiding (pred)
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Syntax
open import Catt.Pasting
open import Data.Empty
open import Data.Unit
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality

private
  variable
    Γ Δ : Ctx
    submax dim : ℕ

disk-ctx : ℕ → Ctx
disk-pdb : (n : ℕ) → (disk-ctx n ⊢pd[ 0 ][ n ])

disk-ctx zero = ∅ , ⋆
disk-ctx (suc n) = extend (disk-pdb n)

disk-pdb zero = Base
disk-pdb (suc n) = ExtendM (disk-pdb n)

disk-pd : (n : ℕ) → (disk-ctx n ⊢pd₀ n)
disk-pd n = restrict-to-pd (disk-pdb n)

disk-sub : (i : Fin (length Γ)) → Sub Γ (disk-ctx (retrieveDim Γ i))
disk-sub {Γ} i with retrieveDim Γ i | Var i | Γ ‼ i
... | zero | v | A = ⟨ ⟨⟩ , v ⟩
... | suc dim | v | s ─⟨ A ⟩⟶ t = ⟨ ⟨ {!!} , {!!} ⟩ , {!!} ⟩

support-ctx : Term Γ dim → Ctx

support-ctx {dim = dim} (Var i) = disk-ctx dim
support-ctx (Coh Δ A σ) = {!!}
