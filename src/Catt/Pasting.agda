{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Pasting where

open import Data.Nat
open import Catt.Syntax
open import Catt.Syntax.Properties
-- open import Catt.Dimension
open import Data.Empty
open import Data.Unit
open import Catt.Support
-- open import Catt.Dimension
-- open import Catt.Globular
open import Relation.Binary.PropositionalEquality

variable
  submax submax′ : ℕ

data _⊢pd₀_ : Ctx (suc n) → ℕ → Set

data _⊢pd[_][_] : (Γ : Ctx (suc n)) → ℕ → ℕ → Set

getFocusType : Γ ⊢pd[ submax ][ d ] → Ty (ctxLength Γ) d
getFocusTerm : Γ ⊢pd[ submax ][ d ] → Tm (ctxLength Γ)

-- Uniquely extend a pasting context
extend : {Γ : Ctx (suc n)} → Γ ⊢pd[ submax ][ d ] → Ctx (3 + n)
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

instance
  nonZeroTT : NonZero′ (submax + suc d)
  nonZeroTT {zero} = it
  nonZeroTT {suc submax} = it

newDim : ℕ → ℕ → ℕ
newDim zero d = pred d
newDim (suc submax) d = d

pdb-bd-len-1 : Γ ⊢pd[ submax ][ d ] → .⦃ nz : NonZero′ (submax + d) ⦄ → ℕ
pdb-bd-ctx : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → Ctx (suc (pdb-bd-len-1 pdb))
pdb-bd-pd : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → (pdb-bd-ctx pdb ⊢pd[ pred submax ][ newDim submax d ])

pdb-bd-len-1 (Extend {n} {submax = zero} pdb) = n
pdb-bd-len-1 (Extend {submax = suc zero} pdb) = pdb-bd-len-1 pdb
pdb-bd-len-1 (Extend {submax = suc (suc submax)} pdb) = 2 + pdb-bd-len-1 pdb
pdb-bd-len-1 (Restr pdb) = pdb-bd-len-1 pdb

pdb-bd-ctx (Extend {Γ = Γ} {submax = zero} pdb) = Γ
pdb-bd-ctx (Extend {submax = suc zero} pdb) = pdb-bd-ctx pdb
pdb-bd-ctx (Extend {submax = suc (suc submax)} pdb) = extend (pdb-bd-pd pdb)
pdb-bd-ctx (Restr pdb) = pdb-bd-ctx pdb

pdb-bd-pd (Extend {submax = zero} pdb) = pdb
pdb-bd-pd (Extend {submax = suc zero} pdb) = pdb-bd-pd pdb
pdb-bd-pd (Extend {submax = suc (suc submax)} pdb) = Extend (pdb-bd-pd pdb)
pdb-bd-pd (Restr {submax = zero} pdb) = pdb-bd-pd pdb
pdb-bd-pd (Restr {submax = suc submax} pdb) = Restr (pdb-bd-pd pdb)

pd-bd-len-1 : Γ ⊢pd₀ suc d → ℕ
pd-bd-len-1 (Finish pdb) = pdb-bd-len-1 pdb

pd-bd-ctx : (pd : Γ ⊢pd₀ suc d) → Ctx (suc (pd-bd-len-1 pd))
pd-bd-ctx (Finish pdb) = pdb-bd-ctx pdb

pd-bd-pd : (pd : Γ ⊢pd₀ suc d) → pd-bd-ctx pd ⊢pd₀ d
pd-bd-pd (Finish pdb) = Finish (pdb-bd-pd pdb)

-- Source and Target
pdb-src : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → Sub (suc (pdb-bd-len-1 pdb)) (ctxLength Γ)
pdb-src (Extend {submax = zero} pdb) = liftSub (liftSub (idSub _))
pdb-src (Extend {submax = suc zero} pdb) = liftSub (liftSub (pdb-src pdb))
pdb-src (Extend {submax = suc (suc submax)} pdb) = ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ , 0V ⟩
pdb-src (Restr pdb) = pdb-src pdb

is-zero : ℕ → Set
is-zero zero = ⊤
is-zero (suc n) = ⊥

replacePdSub : Δ ⊢pd[ submax ][ d ] → (σ : Sub (ctxLength Δ) n) → Tm n → .⦃ is-zero submax ⦄ → Sub (ctxLength Δ) n
replacePdSub Base ⟨ σ , x ⟩ t = ⟨ σ , t ⟩
replacePdSub (Extend pdb) ⟨ σ , x ⟩ t = ⟨ σ , t ⟩

pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → Sub (suc (pdb-bd-len-1 pdb)) (ctxLength Γ)
pdb-tgt (Extend {submax = zero} pdb) = replacePdSub (pdb-bd-pd (Extend pdb)) (liftSub (liftSub (idSub _))) 1V
pdb-tgt (Extend {submax = suc zero} pdb) = replacePdSub (pdb-bd-pd (Extend pdb)) (liftSub (liftSub (pdb-tgt pdb))) 1V
pdb-tgt (Extend {submax = suc (suc submax)} pdb) = ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ , 0V ⟩
pdb-tgt (Restr pdb) = pdb-tgt pdb

pd-src : (pd : Γ ⊢pd₀ (suc d)) → Sub (suc (pd-bd-len-1 pd)) (ctxLength Γ)
pd-src (Finish pdb) = pdb-src pdb

pd-tgt : (pd : Γ ⊢pd₀ (suc d)) → Sub (suc (pd-bd-len-1 pd)) (ctxLength Γ)
pd-tgt (Finish pdb) = pdb-tgt pdb


-- Source and target variables
supp-pdb-src : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ NonZero′ (submax + d) ⦄ → VarSet (ctxLength Γ)
supp-pdb-src (Extend {submax = zero} pdb) = ewf (ewf full)
supp-pdb-src (Extend {submax = suc zero} pdb) = ewf (ewf (supp-pdb-src pdb))
supp-pdb-src (Extend {submax = suc (suc submax)} pdb) = ewt (ewt (supp-pdb-src pdb))
supp-pdb-src (Restr pdb) = supp-pdb-src pdb

supp-pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → VarSet (ctxLength Γ)
supp-pdb-tgt (Extend {submax = zero} pdb) = ewf (ewt (drop full))
supp-pdb-tgt (Extend {submax = suc zero} pdb) = ewf (ewt (drop (supp-pdb-tgt pdb)))
supp-pdb-tgt (Extend {submax = suc (suc submax)} pdb) = ewt (ewt (supp-pdb-tgt pdb))
supp-pdb-tgt (Restr pdb) = supp-pdb-tgt pdb

supp-src : (pd : Γ ⊢pd₀ suc d) → VarSet (ctxLength Γ)
supp-src (Finish pdb) = supp-pdb-src pdb

supp-tgt : (pd : Γ ⊢pd₀ suc d) → VarSet (ctxLength Γ)
supp-tgt (Finish pdb) = supp-pdb-tgt pdb

-- Focus of pd
pd-focus-tm : (pd : Γ ⊢pd₀ d) → Tm (ctxLength Γ)
pd-focus-tm (Finish pdb) = getFocusTerm pdb

pd-focus-ty : (pd : Γ ⊢pd₀ d) → Ty (ctxLength Γ) 0
pd-focus-ty (Finish pdb) = getFocusType pdb
