{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Unbiased where

open import Catt.Syntax
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Data.Nat

pdb-is-extends : (Γ ⊢pd[ submax ][ d ]) → Set
pdb-is-extends Base = ⊤
pdb-is-extends (Extend pdb) = pdb-is-extends pdb
pdb-is-extends (Restr pdb) = ⊥

pdb-is-linear : (Γ ⊢pd[ submax ][ d ]) → Set
pdb-is-linear Base = ⊤
pdb-is-linear (Extend pdb) = pdb-is-extends pdb
pdb-is-linear (Restr pdb) = pdb-is-linear pdb

pdb-is-extends-dec : (pdb : Γ ⊢pd[ submax ][ d ]) → Dec (pdb-is-extends pdb)
pdb-is-extends-dec Base = yes tt
pdb-is-extends-dec (Extend pdb) = pdb-is-extends-dec pdb
pdb-is-extends-dec (Restr pdb) = no (λ x → x)

pdb-is-linear-dec : (pdb : Γ ⊢pd[ submax ][ d ]) → Dec (pdb-is-linear pdb)
pdb-is-linear-dec Base = yes tt
pdb-is-linear-dec (Extend pdb) = pdb-is-extends-dec pdb
pdb-is-linear-dec (Restr pdb) = pdb-is-linear-dec pdb

pd-is-linear : Γ ⊢pd₀ d → Set
pd-is-linear (Finish pdb) = pdb-is-linear pdb

pd-is-linear-dec : (pd : Γ ⊢pd₀ d) → Dec (pd-is-linear pd)
pd-is-linear-dec (Finish pdb) = pdb-is-linear-dec pdb

unbiased-term : (Γ ⊢pd₀ d) → Tm (ctxLength Γ)
unbiased-type : (Γ ⊢pd₀ d) → Ty (ctxLength Γ) d

unbiased-term {Γ = Γ} pd with pd-is-linear-dec pd
... | yes p = 0V
... | no p = Coh Γ (unbiased-type pd) (idSub _)

unbiased-type {d = zero} pd = ⋆
unbiased-type {d = suc d} pd = (unbiased-term (pd-bd-pd pd) [ pd-src pd ]tm) ─⟨ unbiased-type (pd-bd-pd pd) [ pd-src pd ]ty ⟩⟶ (unbiased-term (pd-bd-pd pd) [ pd-tgt pd ]tm)
