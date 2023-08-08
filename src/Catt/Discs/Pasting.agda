module Catt.Discs.Pasting where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Discs

disc-pdb : (d : ℕ) → Disc d ⊢pdb
disc-pdb-focus-ty : (d : ℕ) → focus-ty (disc-pdb d) ≃ty lift-ty (sphere-type d)
disc-pdb-focus-tm : (d : ℕ) → focus-tm (disc-pdb d) ≃tm 0V {n = disc-size d}

disc-pdb zero = Base
disc-pdb (suc d) = Extend (disc-pdb d) (sym≃ty (disc-pdb-focus-ty d)) (sym≃ty (Arr≃ (lift-tm-≃ (disc-pdb-focus-tm d)) (lift-ty-≃ (disc-pdb-focus-ty d)) refl≃tm))

disc-pdb-focus-ty zero = refl≃ty
disc-pdb-focus-ty (suc d) = refl≃ty

disc-pdb-focus-tm zero = refl≃tm
disc-pdb-focus-tm (suc d) = refl≃tm

disc-pd : (d : ℕ) → Disc d ⊢pd
disc-pd d = pdb-to-pd (Disc d) (disc-pdb d)
