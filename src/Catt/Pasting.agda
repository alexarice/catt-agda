{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Pasting where

open import Data.Nat
open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Data.Empty
open import Data.Unit
open import Catt.Support
open import Catt.Dimension

variable
  submax : ℕ

data _⊢pd₀_ : Ctx (suc n) → ℕ → Set

data _⊢pd[_][_] : (Γ : Ctx (suc n)) → ℕ → ℕ → Set

getFocusType : Γ ⊢pd[ submax ][ d ] → Ty Γ (suc d)
getFocusTerm : Γ ⊢pd[ submax ][ d ] → Tm Γ (suc (suc d))

-- Uniquely extend a pasting context
extend : {Γ : Ctx (suc n)} → Γ ⊢pd[ submax ][ d ] → Ctx (suc (suc (suc n)))
extend {Γ = Γ} pdb = Γ , getFocusType pdb , liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V

data _⊢pd[_][_] where
  Base : ∅ , ⋆ ⊢pd[ 0 ][ 0 ]
  Extend : (pdb : Γ ⊢pd[ submax ][ d ]) →
            extend pdb ⊢pd[ pred submax ][ suc d ]
  Restr : Γ ⊢pd[ submax ][ suc d ] →
          Γ ⊢pd[ suc submax ][ d ]

getFocusType Base = ⋆
getFocusType {Γ = Γ , A} (Extend pdb) = liftType A
getFocusType (Restr pdb) = ty-base (getFocusType pdb)

getFocusTerm Base = 0V
getFocusTerm (Extend pdb) = 0V
getFocusTerm (Restr pdb) = ty-tgt (getFocusType pdb)

data _⊢pd₀_ where
  Finish : (pdb : Γ ⊢pd[ submax ][ 0 ]) → Γ ⊢pd₀ submax

nonZero : ℕ → ℕ → Set
nonZero zero zero = ⊥
nonZero zero (suc m) = ⊤
nonZero (suc n) m = ⊤

nonZeroTT : nonZero submax (suc d)
nonZeroTT {zero} = tt
nonZeroTT {suc submax} = tt

newDim : ℕ → ℕ → ℕ
newDim zero d = pred d
newDim (suc submax) d = d

pdb-bd-len-1 : Γ ⊢pd[ submax ][ d ] → .(nonZero submax d) → ℕ
pdb-bd-ctx : (pdb : Γ ⊢pd[ submax ][ d ]) → .(nz : nonZero submax d) → Ctx (suc (pdb-bd-len-1 pdb nz))
pdb-bd-pd : (pdb : Γ ⊢pd[ submax ][ d ]) → .(nz : nonZero submax d) → (pdb-bd-ctx pdb nz ⊢pd[ pred submax ][ newDim submax d ])

pdb-bd-len-1 (Extend {n} {submax = zero} pdb) nz = n
pdb-bd-len-1 (Extend {submax = suc zero} pdb) nz = pdb-bd-len-1 pdb nz
pdb-bd-len-1 (Extend {submax = suc (suc submax)} pdb) nz = suc (suc (pdb-bd-len-1 pdb nz))
pdb-bd-len-1 (Restr pdb) nz = pdb-bd-len-1 pdb nonZeroTT

pdb-bd-ctx (Extend {Γ = Γ} {submax = zero} pdb) nz = Γ
pdb-bd-ctx (Extend {submax = suc zero} pdb) nz = pdb-bd-ctx pdb nz
pdb-bd-ctx (Extend {submax = suc (suc submax)} pdb) nz = extend (pdb-bd-pd pdb nz)
pdb-bd-ctx (Restr pdb) nz = pdb-bd-ctx pdb nonZeroTT

pdb-bd-pd (Extend {submax = zero} pdb) nz = pdb
pdb-bd-pd (Extend {submax = suc zero} pdb) nz = pdb-bd-pd pdb nz
pdb-bd-pd (Extend {submax = suc (suc submax)} pdb) nz = Extend (pdb-bd-pd pdb nz)
pdb-bd-pd (Restr {submax = zero} pdb) nz = pdb-bd-pd pdb nz
pdb-bd-pd (Restr {submax = suc submax} pdb) nz = Restr (pdb-bd-pd pdb nz)

pd-bd-len-1 : Γ ⊢pd₀ suc d → ℕ
pd-bd-len-1 (Finish pdb) = pdb-bd-len-1 pdb tt

pd-bd-ctx : (pd : Γ ⊢pd₀ suc d) → Ctx (suc (pd-bd-len-1 pd))
pd-bd-ctx (Finish pdb) = pdb-bd-ctx pdb tt

pd-bd-pd : (pd : Γ ⊢pd₀ suc d) → pd-bd-ctx pd ⊢pd₀ d
pd-bd-pd (Finish pdb) = Finish (pdb-bd-pd pdb tt)

-- Source and Target
pdb-src : (pdb : Γ ⊢pd[ submax ][ d ]) → .(nz : nonZero submax d) → Sub (pdb-bd-ctx pdb nz) Γ
pdb-src (Extend {submax = zero} pdb) nz = liftSub (liftSub (idSub _))
pdb-src (Extend {submax = suc zero} pdb) nz = liftSub (liftSub (pdb-src pdb nz))
pdb-src (Extend {submax = suc (suc submax)} pdb) nz = ⟨ ⟨ liftSub (liftSub (pdb-src pdb nz)) , 1V ⟩ , 0V ⟩
pdb-src (Restr pdb) nz = pdb-src pdb nonZeroTT

is-zero : ℕ → Set
is-zero zero = ⊤
is-zero (suc n) = ⊥

replacePdSub : Δ ⊢pd[ submax ][ d ] → (σ : Sub Δ Γ) → Tm Γ (suc (suc d)) → .(is-zero submax) → Sub Δ Γ
replacePdSub Base ⟨ σ , x ⟩ t iz = ⟨ σ , t ⟩
replacePdSub (Extend pdb) ⟨ σ , x ⟩ t iz = ⟨ σ , t ⟩

pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → .(nz : nonZero submax d) → Sub (pdb-bd-ctx pdb nz) Γ
pdb-tgt (Extend {submax = zero} pdb) nz = replacePdSub (pdb-bd-pd (Extend pdb) nz) (liftSub (liftSub (idSub _))) 1V tt
pdb-tgt (Extend {submax = suc zero} pdb) nz = replacePdSub (pdb-bd-pd (Extend pdb) nz) (liftSub (liftSub (pdb-tgt pdb nz))) 1V tt
pdb-tgt (Extend {submax = suc (suc submax)} pdb) nz = ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb nz)) , 1V ⟩ , 0V ⟩
pdb-tgt (Restr pdb) nz = pdb-tgt pdb nonZeroTT

pd-src : (pd : Γ ⊢pd₀ (suc d)) → Sub (pd-bd-ctx pd) Γ
pd-src (Finish pdb) = pdb-src pdb tt

pd-tgt : (pd : Γ ⊢pd₀ (suc d)) → Sub (pd-bd-ctx pd) Γ
pd-tgt (Finish pdb) = pdb-tgt pdb tt

-- Source and target variables
supp-pdb-src : (pdb : Γ ⊢pd[ submax ][ d ]) → .(nz : nonZero submax d) → VarSet Γ
supp-pdb-src (Extend {submax = zero} pdb) nz = ewf (ewf full)
supp-pdb-src (Extend {submax = suc zero} pdb) nz = ewf (ewf (supp-pdb-src pdb nz))
supp-pdb-src (Extend {submax = suc (suc submax)} pdb) nz = ewt (ewt (supp-pdb-src pdb nz))
supp-pdb-src (Restr pdb) nz = supp-pdb-src pdb nonZeroTT

supp-pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → .(nz : nonZero submax d) → VarSet Γ
supp-pdb-tgt (Extend {submax = zero} pdb) nz = ewf (ewt (drop full))
supp-pdb-tgt (Extend {submax = suc zero} pdb) nz = ewf (ewt (drop (supp-pdb-tgt pdb nz)))
supp-pdb-tgt (Extend {submax = suc (suc submax)} pdb) nz = ewt (ewt (supp-pdb-tgt pdb nz))
supp-pdb-tgt (Restr pdb) nz = supp-pdb-tgt pdb nonZeroTT

supp-src : (pd : Γ ⊢pd₀ suc d) → VarSet Γ
supp-src (Finish pdb) = supp-pdb-src pdb tt

supp-tgt : (pd : Γ ⊢pd₀ suc d) → VarSet Γ
supp-tgt (Finish pdb) = supp-pdb-tgt pdb tt

-- Focus of pd
pd-focus-tm : (pd : Γ ⊢pd₀ d) → Tm Γ 2
pd-focus-tm (Finish pdb) = getFocusTerm pdb

pd-focus-ty : (pd : Γ ⊢pd₀ d) → Ty Γ 1
pd-focus-ty (Finish pdb) = getFocusType pdb
