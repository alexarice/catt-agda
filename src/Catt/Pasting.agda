module Catt.Pasting where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular

data _⊢pdb : (Γ : Ctx n) → Set

focus-ty : {Γ : Ctx n} → Γ ⊢pdb → Ty n
focus-tm : {Γ : Ctx n} → Γ ⊢pdb → Tm n

data _⊢pdb where
  Base : ∅ , ⋆ ⊢pdb
  Extend : (pdb : Γ ⊢pdb)
         → (p : A ≃ty focus-ty pdb)
         → (q : B ≃ty lift-tm (focus-tm pdb) ─⟨ lift-ty (focus-ty pdb) ⟩⟶ 0V)
         → Γ , A , B ⊢pdb
  Restr : (pdb : Γ ⊢pdb) → .⦃ NonZero (ty-dim (focus-ty pdb)) ⦄ → Γ ⊢pdb

focus-ty Base = ⋆
focus-ty (Extend {B = B} pdb p q) = lift-ty B
focus-ty (Restr pdb) = ty-base (focus-ty pdb)

focus-tm Base = 0V
focus-tm (Extend pdb p q) = 0V
focus-tm (Restr pdb) = ty-tgt (focus-ty pdb)

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

pdb-prefix : Γ , A , B ⊢pdb → Γ ⊢pdb
pdb-prefix (Extend pdb p q) = pdb
pdb-prefix (Restr pdb) = pdb-prefix pdb

right-base : Ty n → Tm n → Tm n
right-base ⋆ u = u
right-base (s ─⟨ A ⟩⟶ t) u = right-base A t

pdb-right-base : {Γ : Ctx n} → Γ ⊢pdb → Tm n
pdb-right-base pdb = right-base (focus-ty pdb) (focus-tm pdb)

pdb-length : {Γ : Ctx n} → Γ ⊢pdb → ℕ
pdb-length Base = 0
pdb-length (Extend pdb p q) = suc (pdb-length pdb)
pdb-length (Restr pdb) = pdb-length pdb

pd-length : {Γ : Ctx n} → Γ ⊢pd → ℕ
pd-length (Finish pdb) = pdb-length pdb

pdb-focus-dim : {Γ : Ctx n} → Γ ⊢pdb → ℕ
pdb-focus-dim Base = 0
pdb-focus-dim (Extend pdb p q) = suc (pdb-focus-dim pdb)
pdb-focus-dim (Restr pdb) = pred (pdb-focus-dim pdb)

pd-focus-dim : {Γ : Ctx n} → Γ ⊢pd → ℕ
pd-focus-dim (Finish pdb) = pdb-focus-dim pdb
