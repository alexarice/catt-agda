{-# OPTIONS --without-K --safe #-}

module Catt.Vars where

open import Data.Nat
open import Data.Fin hiding (pred)
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Syntax
open import Data.Bool
open import Catt.Pasting
open import Data.Empty
open import Data.Unit
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality

private
  variable
    submax dim dim′ : ℕ
    Γ Δ : Ctx

VCtx : Ctx → Set
VTy : Ty Γ dim → Set
VTerm : Term Γ dim → Set
VSub : Sub Γ Δ → Set

VCtx ∅ = ⊤
VCtx (Γ , A) = VCtx Γ × VTy A

VTy ⋆ = ⊤
VTy (s ─⟨ A ⟩⟶ t) = VTerm s × VTerm t × VTy A

VTerm (Var i) = ⊤
VTerm (Coh Δ A σ) = ⊥

VSub ⟨⟩ = ⊤
VSub ⟨ σ , x ⟩ = VSub σ × VTerm x

vliftTy : {B : Ty Γ dim′} {A : Ty Γ dim} → VTy A → VTy (liftType A {B})
vliftTerm : {B : Ty Γ dim′} {t : Term Γ dim} → VTerm t → VTerm (liftTerm t {B})

vliftTy {A = ⋆} vty = tt
vliftTy {A = s ─⟨ A ⟩⟶ t} (vs ,, vt ,, vA) = vliftTerm vs ,, vliftTerm vt ,, vliftTy vA

vliftTerm {t = Var i} vtm = tt

vFocusType : (pdb : Γ ⊢pd[ submax ][ dim ]) → VTy (getFocusType pdb)
vFocusTerm : (pdb : Γ ⊢pd[ submax ][ dim ]) → VTerm (getFocusTerm pdb)

vFocusType Base = tt
vFocusType (ExtendM pdb) = vliftTerm (vliftTerm (vFocusTerm pdb)) ,, tt ,, vliftTy (vliftTy (vFocusType pdb))
vFocusType (Extend pdb) = vliftTerm (vliftTerm (vFocusTerm pdb)) ,, tt ,, vliftTy (vliftTy (vFocusType pdb))
vFocusType (Restr pdb) with getFocusType pdb | vFocusType pdb
... | s ─⟨ A ⟩⟶ t | vs ,, vt ,, vA = vA

vFocusTerm Base = tt
vFocusTerm (ExtendM pdb) = tt
vFocusTerm (Extend pdb) = tt
vFocusTerm (Restr pdb) with getFocusType pdb | vFocusType pdb
... | s ─⟨ A ⟩⟶ t | vs ,, vt ,, vA = vt

PastingVarsB : Γ ⊢pd[ submax ][ dim ] → VCtx Γ
PastingVarsB Base = tt ,, tt
PastingVarsB (ExtendM pdb) = (PastingVarsB pdb ,, vFocusType pdb) ,, vliftTerm (vFocusTerm pdb) ,, tt ,, vliftTy (vFocusType pdb)
PastingVarsB (Extend pdb) = (PastingVarsB pdb ,, vFocusType pdb) ,, vliftTerm (vFocusTerm pdb) ,, tt ,, vliftTy (vFocusType pdb)
PastingVarsB (Restr pdb) = PastingVarsB pdb

PastingVars : Γ ⊢pd₀ dim → VCtx Γ
PastingVars (Finish pdb) = PastingVarsB pdb

vLookup : VCtx Γ → (i : Fin (length Γ)) → VTy (Γ ‼ i)
vLookup {Γ , A} (vctx ,, vA) 0F = vliftTy vA
vLookup {Γ , A} (vctx ,, vA) (suc i) = vliftTy (vLookup vctx i)
