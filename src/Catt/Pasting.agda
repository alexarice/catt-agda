{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Pasting where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular
open import Catt.Syntax.SyntacticEquality
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Data.Empty
open import Data.Unit
open import Data.Bool

data _⊢pdb : (Γ : Ctx n) → Set

focus-ty : {Γ : Ctx n} → Γ ⊢pdb → Ty n
focus-tm : {Γ : Ctx n} → Γ ⊢pdb → Tm n

data _⊢pdb where
  Base : ∅ , ⋆ ⊢pdb
  Extend : (pdb : Γ ⊢pdb)
         → (p : A ≃ty focus-ty pdb)
         → (q : B ≃ty liftTerm (focus-tm pdb) ─⟨ liftType (focus-ty pdb) ⟩⟶ 0V)
         → Γ , A , B ⊢pdb
  Restr : (pdb : Γ ⊢pdb) → .⦃ NonZero (ty-dim (focus-ty pdb)) ⦄ → Γ ⊢pdb

focus-ty Base = ⋆
focus-ty (Extend {B = B} pdb p q) = liftType B
focus-ty (Restr pdb) = ty-base (focus-ty pdb)

focus-tm Base = 0V
focus-tm (Extend pdb p q) = 0V
focus-tm (Restr pdb) = ty-tgt′ (focus-ty pdb)

data _⊢pd : (Ctx n) → Set where
  Finish : (pdb : Γ ⊢pdb) → .⦃ IsZero (ty-dim (focus-ty pdb)) ⦄ → Γ ⊢pd

pd-to-pdb : {Γ : Ctx n} → Γ ⊢pd → Γ ⊢pdb
pd-to-pdb (Finish pdb) = pdb

pd-focus-ty : {Γ : Ctx n} → Γ ⊢pd → Ty n
pd-focus-ty pd = focus-ty (pd-to-pdb pd)

pd-focus-tm : {Γ : Ctx n} → Γ ⊢pd → Tm n
pd-focus-tm pd = focus-tm (pd-to-pdb pd)

pd-to-pdb-0-d : (pd : Γ ⊢pd) → IsZero (ty-dim (focus-ty (pd-to-pdb pd)))
pd-to-pdb-0-d (Finish pdb) with ty-dim (focus-ty pdb)
... | zero = it

pd-to-pdb-focus-tm : (pd : Γ ⊢pd) → focus-tm (pd-to-pdb pd) ≃tm pd-focus-tm pd
pd-to-pdb-focus-tm (Finish pdb) = refl≃tm

Odd Even : ℕ → Set
Odd zero = ⊥
Odd (suc n) = Even n
Even zero = ⊤
Even (suc n) = Odd n

pdb-odd-length : {Γ : Ctx m} → Γ ⊢pdb → Odd m
pdb-odd-length Base = tt
pdb-odd-length (Extend pdb p q) = pdb-odd-length pdb
pdb-odd-length (Restr pdb) = pdb-odd-length pdb

-- instance
--   nonZeroTT : NonZero′ (submax + suc d)
--   nonZeroTT {zero} = it
--   nonZeroTT {suc submax} = it

pdb-prefix : Γ , A , B ⊢pdb → Γ ⊢pdb
pdb-prefix (Extend pdb p q) = pdb
pdb-prefix (Restr pdb) = pdb-prefix pdb

right-base : Ty n → Tm n → Tm n
right-base ⋆ u = u
right-base (s ─⟨ A ⟩⟶ t) u = right-base A t

pdb-right-base : {Γ : Ctx n} → Γ ⊢pdb → Tm n
pdb-right-base pdb = right-base (focus-ty pdb) (focus-tm pdb)



-- pdb-bd-len : (n : ℕ) → (Γ : Ctx m) → (pdb : Γ ⊢pdb) → ℕ
-- pdb-bd-ctx : (n : ℕ) → (Γ : Ctx m) → (pdb : Γ ⊢pdb) → Ctx (pdb-bd-len n Γ pdb)

-- pdb-non-zero : {Γ : Ctx n} → Γ ⊢pdb → NonZero′ n
-- pdb-non-zero Base = it
-- pdb-non-zero (Extend pdb p q) = it
-- pdb-non-zero (Restr pdb) = pdb-non-zero pdb
-- -- pdb-prefix : Γ , A , B ⊢pdb t ∶ A

-- pdb-bd-len n Γ pdb = {!!}

-- pdb-bd-ctx n ∅ pdb = ⊥-elim (NonZero′.nonZero (pdb-non-zero pdb))
-- pdb-bd-ctx n (∅ , A) pdb = ∅ , A
-- pdb-bd-ctx n (Γ , B , A) pdb = tri-cases (<-cmp n (ty-dim A)) new-bd new-bd (new-bd , {!!} , {!!})
--   where
--     new-bd : Ctx (pdb-bd-len n Γ {!!})
--     new-bd = pdb-bd-ctx n Γ {!!}

-- pdb-bd-pdb n Base = Base
-- pdb-bd-pdb n (Extend {d = d} pdb p q) = {!!}
-- pdb-bd-pdb n (Restr pdb) =


{-
newDim : ℕ → ℕ → ℕ
newDim zero d = pred d
newDim (suc submax) d = d

pdb-bd-len-1 : Γ ⊢pdb d → .⦃ nz : NonZero′ (submax + d) ⦄ → ℕ
pdb-bd-ctx : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → Ctx (suc (pdb-bd-len-1 pdb))
pdb-bd-pd : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → (pdb-bd-ctx pdb ⊢pd[ pred submax ][ newDim submax d ])

pdb-bd-len-1 (Extend {n} {submax = zero} pdb p q) = n
pdb-bd-len-1 (Extend {submax = suc zero} pdb p q) = pdb-bd-len-1 pdb
pdb-bd-len-1 (Extend {submax = suc (suc submax)} pdb p q) = 2 + pdb-bd-len-1 pdb
pdb-bd-len-1 (Restr pdb) = pdb-bd-len-1 pdb

pdb-bd-ctx (Extend {Γ = Γ} {submax = zero} pdb p q) = Γ
pdb-bd-ctx (Extend {submax = suc zero} pdb p q) = pdb-bd-ctx pdb
pdb-bd-ctx (Extend {submax = suc (suc submax)} pdb p q) = extend (pdb-bd-pd pdb)
pdb-bd-ctx (Restr pdb) = pdb-bd-ctx pdb

pdb-bd-pd (Extend {submax = zero} pdb p q) = pdb
pdb-bd-pd (Extend {submax = suc zero} pdb p q) = pdb-bd-pd pdb
pdb-bd-pd (Extend {submax = suc (suc submax)} pdb p q) = Extend (pdb-bd-pd pdb) refl≃ty refl≃ty
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
pdb-src (Extend {submax = zero} pdb p q) = liftSub (liftSub (idSub _))
pdb-src (Extend {submax = suc zero} pdb p q) = liftSub (liftSub (pdb-src pdb))
pdb-src (Extend {submax = suc (suc submax)} pdb p q) = ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ , 0V ⟩
pdb-src (Restr pdb) = pdb-src pdb

is-zero : ℕ → Set
is-zero zero = ⊤
is-zero (suc n) = ⊥

replacePdSub : (σ : Sub (suc m) n) → Tm n → Sub (suc m) n
replacePdSub ⟨ σ , x ⟩ t = ⟨ σ , t ⟩

pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → Sub (suc (pdb-bd-len-1 pdb)) (ctxLength Γ)
pdb-tgt (Extend {submax = zero} pdb p q) = replacePdSub (liftSub (liftSub (idSub _))) 1V
pdb-tgt (Extend {submax = suc zero} pdb p q) = replacePdSub (liftSub (liftSub (pdb-tgt pdb))) 1V
pdb-tgt (Extend {submax = suc (suc submax)} pdb p q) = ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ , 0V ⟩
pdb-tgt (Restr pdb) = pdb-tgt pdb

pd-src : (pd : Γ ⊢pd₀ (suc d)) → Sub (suc (pd-bd-len-1 pd)) (ctxLength Γ)
pd-src (Finish pdb) = pdb-src pdb

pd-tgt : (pd : Γ ⊢pd₀ (suc d)) → Sub (suc (pd-bd-len-1 pd)) (ctxLength Γ)
pd-tgt (Finish pdb) = pdb-tgt pdb

-- Source and target variables
supp-pdb-src : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ NonZero′ (submax + d) ⦄ → VarSet (ctxLength Γ)
supp-pdb-src (Extend {submax = zero} pdb p q) = ewf (ewf full)
supp-pdb-src (Extend {submax = suc zero} pdb p q) = ewf (ewf (supp-pdb-src pdb))
supp-pdb-src (Extend {submax = suc (suc submax)} pdb p q) = ewt (ewt (supp-pdb-src pdb))
supp-pdb-src (Restr pdb) = supp-pdb-src pdb

supp-pdb-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ nz : NonZero′ (submax + d) ⦄ → VarSet (ctxLength Γ)
supp-pdb-tgt (Extend {submax = zero} pdb p q) = ewf (ewt (drop full))
supp-pdb-tgt (Extend {submax = suc zero} pdb p q) = ewf (ewt (drop (supp-pdb-tgt pdb)))
supp-pdb-tgt (Extend {submax = suc (suc submax)} pdb p q) = ewt (ewt (supp-pdb-tgt pdb))
supp-pdb-tgt (Restr pdb) = supp-pdb-tgt pdb

supp-src : (pd : Γ ⊢pd₀ d) → .⦃ _ : NonZero′ d ⦄ → VarSet (ctxLength Γ)
supp-src {d = suc d} (Finish pdb) = supp-pdb-src pdb

supp-tgt : (pd : Γ ⊢pd₀ d) → .⦃ _ : NonZero′ d ⦄ → VarSet (ctxLength Γ)
supp-tgt {d = suc d} (Finish pdb) = supp-pdb-tgt pdb

-- Focus of pd
pd-focus-tm : (pd : Γ ⊢pd₀ d) → Tm (ctxLength Γ)
pd-focus-tm (Finish pdb) = getFocusTerm pdb

pd-focus-ty : (pd : Γ ⊢pd₀ d) → Ty (ctxLength Γ) 0
pd-focus-ty (Finish pdb) = getFocusType pdb
-}
