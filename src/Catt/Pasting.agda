{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Pasting where

open import Data.Nat
open import Catt.Syntax
open import Data.Empty
open import Data.Unit
open import Data.Fin.Patterns
open import Catt.Support

private
  variable
    submax dim dim′ : ℕ

data _⊢pd₀_ : Ctx n d → ℕ → Set

data _⊢pd[_][_] : (Γ : Ctx n d) → ℕ → ℕ → Set

combine : ℕ → ℕ → ℕ
combine zero b = b
combine (suc a) b = combine a (suc b)

extend-dim : ℕ → ℕ → ℕ
extend-dim zero dim = ?
extend-dim (suc submax) dim = ?
-- Uniquely extend a pasting context
extend : {Γ : Ctx n (combine submax dim)} → Γ ⊢pd[ submax ][ dim ] → Ctx (suc (suc (ctxLength Γ))) (extend-dim submax dim)

data _⊢pd[_][_] where
  Base : ∅ , ⋆ ⊢pd[ 0 ][ 0 ]
  ExtendM : (pdb : Γ ⊢pd[ 0 ][ dim ]) →
            extend pdb ⊢pd[ 0 ][ suc dim ]
  Extend : (pdb : Γ ⊢pd[ suc submax ][ dim ]) →
           extend pdb ⊢pd[ submax ][ suc dim ]
  Restr : Γ ⊢pd[ submax ][ suc dim ] →
          Γ ⊢pd[ suc submax ][ dim ]

getFocusTerm : Γ ⊢pd[ submax ][ dim ] → Tm Γ dim
getFocusType : Γ ⊢pd[ submax ][ dim ] → Ty Γ dim

extend {Γ = Γ} pdb = Γ , getFocusType pdb , liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F

getFocusTerm Base = Var 0F
getFocusTerm (ExtendM pdb) = Var 0F
getFocusTerm (Extend pdb) = Var 0F
getFocusTerm (Restr pdb) with getFocusType pdb
... | s ─⟨ A ⟩⟶ t = t

getFocusType Base = ⋆
getFocusType {Γ = Γ , A} (ExtendM pdb) = liftType A
getFocusType {Γ = Γ , A} (Extend pdb) = liftType A
getFocusType (Restr pdb) with getFocusType pdb
... | s ─⟨ A ⟩⟶ t = A

data _⊢pd₀_ where
  Finish : {Γ : Ctx n submax} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → Γ ⊢pd₀ submax

extend-pd : (pdb : Γ ⊢pd[ submax ][ dim ]) →
            extend pdb ⊢pd[ pred submax ][ suc dim ]
extend-pd {submax = zero} pdb = ExtendM pdb
extend-pd {submax = suc submax} pdb = Extend pdb

nonZero : ℕ → ℕ → Set
nonZero zero zero = ⊥
nonZero zero (suc m) = ⊤
nonZero (suc n) m = ⊤

nonZeroTT : nonZero submax (suc dim)
nonZeroTT {zero} = tt
nonZeroTT {suc submax} = tt

newDim : ℕ → ℕ → ℕ
newDim zero dim = pred dim
newDim (suc submax) dim = dim

pd-bd-dim : (submax dim : ℕ) → nonZero submax dim → ℕ
pd-bd-dim zero (suc dim) nz = dim
pd-bd-dim (suc submax) dim nz = {!!}

pdb-bd-len : Γ ⊢pd[ submax ][ dim ] → nonZero submax dim → ℕ
pdb-bd-ctx : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → Ctx (pdb-bd-len pdb nz) {!!}
pdb-bd-pd : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → (pdb-bd-ctx pdb nz ⊢pd[ pred submax ][ newDim submax dim ])

pdb-bd-len (ExtendM {n} pdb) nz = n
pdb-bd-len {submax = zero} (Extend pdb) nz = pdb-bd-len pdb nz
pdb-bd-len {submax = suc submax} (Extend pdb) nz = suc (suc (pdb-bd-len pdb nz))
pdb-bd-len (Restr pdb) nz = pdb-bd-len pdb nonZeroTT

pdb-bd-ctx (ExtendM {Γ = Γ} pdb) nz = Γ
pdb-bd-ctx {submax = zero} (Extend pdb) nz = pdb-bd-ctx pdb nz
pdb-bd-ctx {submax = suc submax} (Extend pdb) nz = extend (pdb-bd-pd pdb nz)
pdb-bd-ctx (Restr pdb) nz = pdb-bd-ctx pdb nonZeroTT

pdb-bd-pd (ExtendM pdb) nz = pdb
pdb-bd-pd {submax = zero} (Extend pdb) nz = pdb-bd-pd pdb nz
pdb-bd-pd {submax = suc submax} (Extend pdb) nz = extend-pd (pdb-bd-pd pdb nz)
pdb-bd-pd (Restr {submax = zero} pdb) nz = pdb-bd-pd pdb nz
pdb-bd-pd (Restr {submax = suc submax} pdb) nz = Restr (pdb-bd-pd pdb nz)

pd-bd-len : Γ ⊢pd₀ suc dim → ℕ
pd-bd-len (Finish pdb) = pdb-bd-len pdb tt

pd-bd-ctx : (pd : Γ ⊢pd₀ suc dim) → Ctx (pd-bd-len pd) {!!}
pd-bd-ctx (Finish pdb) = pdb-bd-ctx pdb tt

pd-bd-pd : (pd : Γ ⊢pd₀ suc dim) → pd-bd-ctx pd ⊢pd₀ dim
pd-bd-pd (Finish pdb) = Finish (pdb-bd-pd pdb tt)

-- Source and Target
pdb-src : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → Sub (pdb-bd-ctx pdb nz) Γ
pdb-src (ExtendM pdb) nz = liftSub (liftSub (idSub _))
pdb-src {submax = zero} (Extend pdb) nz = liftSub (liftSub (pdb-src pdb nz))
pdb-src {submax = suc submax} (Extend pdb) nz = ⟨ ⟨ liftSub (liftSub (pdb-src pdb nz)) , Var 1F ⟩ , Var 0F ⟩
pdb-src (Restr pdb) nz = pdb-src pdb nonZeroTT

replacePdSub : Δ ⊢pd[ 0 ][ dim ] → (σ : Sub Δ Γ) → Tm Γ dim → Sub Δ Γ
replacePdSub Base ⟨ σ , x ⟩ t = ⟨ σ , t ⟩
replacePdSub (ExtendM pdb) ⟨ σ , x ⟩ t = ⟨ σ , t ⟩
replacePdSub (Extend pdb) ⟨ σ , x ⟩ t = ⟨ σ , t ⟩

pdb-tgt : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → Sub (pdb-bd-ctx pdb nz) Γ
pdb-tgt (ExtendM pdb) nz = replacePdSub (pdb-bd-pd (ExtendM pdb) nz) (liftSub (liftSub (idSub _))) (Var 1F)
pdb-tgt {submax = zero} (Extend pdb) nz = replacePdSub (pdb-bd-pd (Extend pdb) nz) (liftSub (liftSub (pdb-tgt pdb nz))) (Var 1F)
pdb-tgt {submax = suc submax} (Extend pdb) nz = ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb nz)) , Var 1F ⟩ , Var 0F ⟩
pdb-tgt (Restr pdb) nz = pdb-tgt pdb nonZeroTT

pd-src : (pd : Γ ⊢pd₀ (suc dim)) → Sub (pd-bd-ctx pd) Γ
pd-src (Finish pdb) = pdb-src pdb tt

pd-tgt : (pd : Γ ⊢pd₀ (suc dim)) → Sub (pd-bd-ctx pd) Γ
pd-tgt (Finish pdb) = pdb-tgt pdb tt

-- Source and target variables
supp-pdb-src : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → VarSet Γ
supp-pdb-src (ExtendM pdb) nz = ewf (ewf full)
supp-pdb-src {submax = zero} (Extend pdb) nz = ewf (ewf (supp-pdb-src pdb nz))
supp-pdb-src {submax = suc submax} (Extend pdb) nz = ewt (ewt (supp-pdb-src pdb nz))
supp-pdb-src (Restr pdb) nz = supp-pdb-src pdb nonZeroTT

supp-pdb-tgt : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → VarSet Γ
supp-pdb-tgt (ExtendM pdb) nz = ewf (ewt (drop full))
supp-pdb-tgt {submax = zero} (Extend pdb) nz = ewf (ewt (drop (supp-pdb-tgt pdb nz)))
supp-pdb-tgt {submax = suc submax} (Extend pdb) nz = ewt (ewt (supp-pdb-tgt pdb nz))
supp-pdb-tgt (Restr pdb) nz = supp-pdb-tgt pdb nonZeroTT

supp-src : (pd : Γ ⊢pd₀ suc dim) → VarSet Γ
supp-src (Finish pdb) = supp-pdb-src pdb tt

supp-tgt : (pd : Γ ⊢pd₀ suc dim) → VarSet Γ
supp-tgt (Finish pdb) = supp-pdb-tgt pdb tt
