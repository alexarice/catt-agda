{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Pasting where

open import Data.Nat
open import Catt.Syntax
open import Data.Empty
open import Data.Unit
open import Data.Fin.Patterns
open import Catt.Support
open import Catt.Dimension

variable
  submax : ℕ

data _⊢pd₀_ : Ctx n d → ℕ → Set

data _⊢pd[_][_] : (Γ : Ctx n d) → ℕ → ℕ → Set

getFocusType : Γ ⊢pd[ submax ][ d ] → Ty Γ (suc d)
getFocusTerm : Γ ⊢pd[ submax ][ d ] → Tm Γ (suc (suc d))

-- Uniquely extend a pasting context
extend : {Γ : Ctx n m} → Γ ⊢pd[ submax ][ d ] → Ctx (suc (suc n)) (m ⊔ suc d ⊔ suc (suc d))
extend {Γ = Γ} pdb = Γ , getFocusType pdb , liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F

data _⊢pd[_][_] where
  Base : ∅ , ⋆ ⊢pd[ 0 ][ 0 ]
  ExtendM : (pdb : Γ ⊢pd[ 0 ][ d ]) →
            extend pdb ⊢pd[ 0 ][ suc d ]
  Extend : (pdb : Γ ⊢pd[ suc submax ][ d ]) →
            extend pdb ⊢pd[ submax ][ suc d ]
  Restr : Γ ⊢pd[ submax ][ suc d ] →
          Γ ⊢pd[ suc submax ][ d ]

getFocusType Base = ⋆
getFocusType {Γ = Γ , A} (ExtendM pdb) = liftType A
getFocusType {Γ = Γ , A} (Extend pdb) = liftType A
getFocusType (Restr pdb) = ty-base (getFocusType pdb)

getFocusTerm Base = Var 0F
getFocusTerm (ExtendM pdb) = Var 0F
getFocusTerm (Extend pdb) = Var 0F
getFocusTerm (Restr pdb) = ty-tgt (getFocusType pdb)



data _⊢pd₀_ where
  Finish : (pdb : Γ ⊢pd[ submax ][ 0 ]) → Γ ⊢pd₀ submax

extend-pd : (pdb : Γ ⊢pd[ submax ][ d ]) →
            extend pdb ⊢pd[ pred submax ][ suc d ]
extend-pd {submax = zero} pdb = ExtendM pdb
extend-pd {submax = suc submax} pdb = Extend pdb

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

pdb-bd-len : Γ ⊢pd[ submax ][ d ] → nonZero submax d → ℕ
pdb-bd-dim : Γ ⊢pd[ submax ][ d ] → nonZero submax d → ℕ
pdb-bd-ctx : (pdb : Γ ⊢pd[ submax ][ d ]) → (nz : nonZero submax d) → Ctx (pdb-bd-len pdb nz) (pdb-bd-dim pdb nz)
pdb-bd-pd : (pdb : Γ ⊢pd[ submax ][ d ]) → (nz : nonZero submax d) → (pdb-bd-ctx pdb nz ⊢pd[ pred submax ][ newDim submax d ])

pdb-bd-len (ExtendM {n} pdb) nz = n
pdb-bd-len {submax = zero} (Extend pdb) nz = pdb-bd-len pdb nz
pdb-bd-len {submax = suc submax} (Extend pdb) nz = suc (suc (pdb-bd-len pdb nz))
pdb-bd-len (Restr pdb) nz = pdb-bd-len pdb nonZeroTT

pdb-bd-dim (ExtendM {Γ = Γ} pdb) nz = ctx-dim Γ
pdb-bd-dim {submax = zero} (Extend pdb) nz = pdb-bd-dim pdb nz
pdb-bd-dim {submax = suc submax} {d = suc d} (Extend pdb) nz =
  pdb-bd-dim pdb nz ⊔ suc (newDim (suc (suc submax)) d) ⊔ suc (suc (newDim (suc (suc submax)) d))
pdb-bd-dim (Restr pdb) nz = pdb-bd-dim pdb nonZeroTT

pdb-bd-ctx (ExtendM {Γ = Γ} pdb) nz = Γ
pdb-bd-ctx {submax = zero} (Extend pdb) nz = pdb-bd-ctx pdb nz
pdb-bd-ctx {submax = suc submax} (Extend pdb) nz = extend (pdb-bd-pd pdb nz)
pdb-bd-ctx (Restr pdb) nz = pdb-bd-ctx pdb nonZeroTT

pdb-bd-pd (ExtendM pdb) nz = pdb
pdb-bd-pd {submax = zero} (Extend pdb) nz = pdb-bd-pd pdb nz
pdb-bd-pd {submax = suc submax} (Extend pdb) nz = extend-pd (pdb-bd-pd pdb nz)
pdb-bd-pd (Restr {submax = zero} pdb) nz = pdb-bd-pd pdb nz
pdb-bd-pd (Restr {submax = suc submax} pdb) nz = Restr (pdb-bd-pd pdb nz)

pd-bd-len : Γ ⊢pd₀ suc d → ℕ
pd-bd-len (Finish pdb) = pdb-bd-len pdb tt

pd-bd-d : Γ ⊢pd₀ suc d → ℕ
pd-bd-d (Finish pdb) = pdb-bd-dim pdb tt

pd-bd-ctx : (pd : Γ ⊢pd₀ suc d) → Ctx (pd-bd-len pd) (pd-bd-d pd)
pd-bd-ctx (Finish pdb) = pdb-bd-ctx pdb tt

pd-bd-pd : (pd : Γ ⊢pd₀ suc d) → pd-bd-ctx pd ⊢pd₀ d
pd-bd-pd (Finish pdb) = Finish (pdb-bd-pd pdb tt)

-- Source and Target
pdb-src : (pdb : Γ ⊢pd[ submax ][ d ]) → (nz : nonZero submax d) → Sub (pdb-bd-ctx pdb nz) Γ
pdb-src (ExtendM pdb) nz = liftSub (liftSub (idSub _))
pdb-src {submax = zero} (Extend pdb) nz = liftSub (liftSub (pdb-src pdb nz))
pdb-src {submax = suc submax} (Extend pdb) nz = ⟨ ⟨ liftSub (liftSub (pdb-src pdb nz)) , Var 1F ⟩ , Var 0F ⟩
pdb-src (Restr pdb) nz = pdb-src pdb nonZeroTT

replacePdSub : Δ ⊢pd[ 0 ][ d ] → (σ : Sub Δ Γ) → Tm Γ (suc (suc d)) → Sub Δ Γ
replacePdSub Base ⟨ σ , x ⟩ t = ⟨ σ , t ⟩
replacePdSub (ExtendM pdb) ⟨ σ , x ⟩ t = ⟨ σ , t ⟩
replacePdSub (Extend pdb) ⟨ σ , x ⟩ t = ⟨ σ , t ⟩

pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → (nz : nonZero submax d) → Sub (pdb-bd-ctx pdb nz) Γ
pdb-tgt (ExtendM pdb) nz = replacePdSub (pdb-bd-pd (ExtendM pdb) nz) (liftSub (liftSub (idSub _))) (Var 1F)
pdb-tgt {submax = zero} (Extend pdb) nz = replacePdSub (pdb-bd-pd (Extend pdb) nz) (liftSub (liftSub (pdb-tgt pdb nz))) (Var 1F)
pdb-tgt {submax = suc submax} (Extend pdb) nz = ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb nz)) , Var 1F ⟩ , Var 0F ⟩
pdb-tgt (Restr pdb) nz = pdb-tgt pdb nonZeroTT

pd-src : (pd : Γ ⊢pd₀ (suc d)) → Sub (pd-bd-ctx pd) Γ
pd-src (Finish pdb) = pdb-src pdb tt

pd-tgt : (pd : Γ ⊢pd₀ (suc d)) → Sub (pd-bd-ctx pd) Γ
pd-tgt (Finish pdb) = pdb-tgt pdb tt

-- Source and target variables
supp-pdb-src : (pdb : Γ ⊢pd[ submax ][ d ]) → (nz : nonZero submax d) → VarSet Γ
supp-pdb-src (ExtendM pdb) nz = ewf (ewf full)
supp-pdb-src {submax = zero} (Extend pdb) nz = ewf (ewf (supp-pdb-src pdb nz))
supp-pdb-src {submax = suc submax} (Extend pdb) nz = ewt (ewt (supp-pdb-src pdb nz))
supp-pdb-src (Restr pdb) nz = supp-pdb-src pdb nonZeroTT

supp-pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → (nz : nonZero submax d) → VarSet Γ
supp-pdb-tgt (ExtendM pdb) nz = ewf (ewt (drop full))
supp-pdb-tgt {submax = zero} (Extend pdb) nz = ewf (ewt (drop (supp-pdb-tgt pdb nz)))
supp-pdb-tgt {submax = suc submax} (Extend pdb) nz = ewt (ewt (supp-pdb-tgt pdb nz))
supp-pdb-tgt (Restr pdb) nz = supp-pdb-tgt pdb nonZeroTT

supp-src : (pd : Γ ⊢pd₀ suc d) → VarSet Γ
supp-src (Finish pdb) = supp-pdb-src pdb tt

supp-tgt : (pd : Γ ⊢pd₀ suc d) → VarSet Γ
supp-tgt (Finish pdb) = supp-pdb-tgt pdb tt
