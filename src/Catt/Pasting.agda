{-# OPTIONS --without-K --safe #-}

module Catt.Pasting where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (pred; _+_)
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Syntax
open import Data.Empty
open import Data.Unit
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality

subtract : ℕ → ℕ → ℕ
subtract zero m = m
subtract (suc n) m = pred m

private
  variable
    Γ Δ : Ctx
    submax dim dim′ : ℕ

data _⊢pd₀_ : Ctx → ℕ → Set

data _⊢pd[_][_] : (Γ : Ctx) → ℕ → ℕ → Set

-- Uniquely extend a pasting context
extend : Γ ⊢pd[ submax ][ dim ] → Ctx

data _⊢pd[_][_] where
  Base : ∅ , ⋆ ⊢pd[ 0 ][ 0 ]
  ExtendM : (pdb : Γ ⊢pd[ 0 ][ dim ]) →
            extend pdb ⊢pd[ 0 ][ suc dim ]
  Extend : (pdb : Γ ⊢pd[ suc submax ][ dim ]) →
           extend pdb ⊢pd[ submax ][ suc dim ]
  Restr : Γ ⊢pd[ submax ][ suc dim ] →
          Γ ⊢pd[ suc submax ][ dim ]

getFocusTerm : Γ ⊢pd[ submax ][ dim ] → Term Γ dim
getFocusType : Γ ⊢pd[ submax ][ dim ] → Ty Γ dim


extend {Γ} pdb = Γ , getFocusType pdb , liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var zero

getFocusTerm Base = Var zero
getFocusTerm (ExtendM pdb) = Var zero
getFocusTerm (Extend pdb) = Var zero
getFocusTerm (Restr pdb) with getFocusType pdb
... | s ─⟨ A ⟩⟶ t = t

getFocusType Base = ⋆
getFocusType {Γ , A} (ExtendM pdb) = liftType A
getFocusType {Γ , A} (Extend pdb) = liftType A
getFocusType (Restr pdb) with getFocusType pdb
... | s ─⟨ A ⟩⟶ t = A

data _⊢pd₀_ where
  Finish : {Γ : Ctx} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → Γ ⊢pd₀ submax

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

pdb-bd-ctx : Γ ⊢pd[ submax ][ dim ] → nonZero submax dim → Ctx
pdb-bd-pd : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → (pdb-bd-ctx pdb nz ⊢pd[ pred submax ][ newDim submax dim ])

pdb-bd-ctx (ExtendM {Γ} pdb) nz = Γ
pdb-bd-ctx {submax = zero} (Extend pdb) nz = pdb-bd-ctx pdb nz
pdb-bd-ctx {submax = suc submax} (Extend pdb) nz = extend (pdb-bd-pd pdb nz)
pdb-bd-ctx (Restr pdb) nz = pdb-bd-ctx pdb nonZeroTT

pdb-bd-pd (ExtendM pdb) nz = pdb
pdb-bd-pd {submax = zero} (Extend pdb) nz = pdb-bd-pd pdb nz
pdb-bd-pd {submax = suc submax} (Extend pdb) nz = extend-pd (pdb-bd-pd pdb nz)
pdb-bd-pd (Restr {submax = zero} pdb) nz = pdb-bd-pd pdb nz
pdb-bd-pd (Restr {submax = suc submax} pdb) nz = Restr (pdb-bd-pd pdb nz)

pd-bd-ctx : Γ ⊢pd₀ suc dim → Ctx
pd-bd-ctx (Finish pdb) = pdb-bd-ctx pdb tt

pd-bd-pd : (pd : Γ ⊢pd₀ suc dim) → pd-bd-ctx pd ⊢pd₀ dim
pd-bd-pd (Finish pdb) = Finish (pdb-bd-pd pdb tt)

-- Source and Target
pdb-src : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → Sub Γ (pdb-bd-ctx pdb nz)
pdb-src (ExtendM pdb) nz = liftSub (liftSub idSub)
pdb-src {submax = zero} (Extend pdb) nz = liftSub (liftSub (pdb-src pdb nz))
pdb-src {submax = suc submax} (Extend pdb) nz = ⟨ ⟨ liftSub (liftSub (pdb-src pdb nz)) , Var (suc zero) ⟩ , Var zero ⟩
pdb-src (Restr {submax = zero} pdb) nz = pdb-src pdb nz
pdb-src (Restr {submax = suc submax} pdb) nz = pdb-src pdb nz

replacePdSub : Δ ⊢pd[ 0 ][ dim ] → (σ : Sub Γ Δ) → Term Γ dim → Sub Γ Δ
replacePdSub Base ⟨ σ , x ⟩ t = ⟨ σ , t ⟩
replacePdSub (ExtendM pdb) ⟨ σ , x ⟩ t = ⟨ σ , t ⟩
replacePdSub (Extend pdb) ⟨ σ , x ⟩ t = ⟨ σ , t ⟩

pdb-tgt : (pdb : Γ ⊢pd[ submax ][ dim ]) → (nz : nonZero submax dim) → Sub Γ (pdb-bd-ctx pdb nz)
pdb-tgt (ExtendM pdb) nz = replacePdSub (pdb-bd-pd (ExtendM pdb) nz) (liftSub (liftSub idSub)) (Var 1F)
pdb-tgt {submax = zero} (Extend pdb) nz = replacePdSub (pdb-bd-pd (Extend pdb) nz) (liftSub (liftSub (pdb-tgt pdb nz))) (Var 1F)
pdb-tgt {submax = suc submax} (Extend pdb) nz = ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb nz)) , Var (suc zero) ⟩ , Var zero ⟩
pdb-tgt (Restr {submax = zero} pdb) nz = pdb-tgt pdb nz
pdb-tgt (Restr {submax = suc submax} pdb) nz = pdb-tgt pdb nz

pd-src : (pd : Γ ⊢pd₀ (suc dim)) → Sub Γ (pd-bd-ctx pd)
pd-src (Finish pdb) = pdb-src pdb tt

pd-tgt : (pd : Γ ⊢pd₀ (suc dim)) → Sub Γ (pd-bd-ctx pd)
pd-tgt (Finish pdb) = pdb-tgt pdb tt

-- pdb restriction

-- combine : ℕ → ℕ → ℕ
-- combine zero m = m
-- combine (suc n) m = combine n (suc m)

-- combine-lem : ∀ n m → combine n (suc m) ≡ suc (combine n m)
-- combine-lem zero m = refl
-- combine-lem (suc n) m = combine-lem n (suc m)

-- combine-is-add : ∀ n m → combine n m ≡ n + m
-- combine-is-add zero m = refl
-- combine-is-add (suc n) m = trans (combine-lem n m) (cong suc (combine-is-add n m))

restrict-to-pd : Γ ⊢pd[ submax ][ dim ] → Γ ⊢pd₀ (submax + dim)
restrict-to-pd {Γ} {dim = zero} pdb = subst (Γ ⊢pd₀_) (sym (+-identityʳ _)) (Finish pdb)
restrict-to-pd {Γ} {dim = suc dim} pdb = subst (Γ ⊢pd₀_) (sym (+-suc _ dim)) (restrict-to-pd (Restr pdb))


-- data SourceFree : (Γ ⊢pd[ submax ][ dim ]) → Term Γ dim′ → Set where
--   SFBase : (pdb : Γ ⊢pd[ submax ][ suc dim ]) → SourceFree (Restr pdb) (getFocusTerm pdb)
--   SFStepRestr : (pdb : Γ ⊢pd[ submax ][ suc dim ])
