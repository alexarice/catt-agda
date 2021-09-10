{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Pasting.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule props
open import Catt.Syntax
open import Catt.Pasting

pdb-to-Ty : Γ ⊢pd[ submax ][ d ] → Typing-Ctx Γ
pdb-focus-ty-Ty : (pdb : Γ ⊢pd[ submax ][ d ]) → Typing-Ty Γ (getFocusType pdb)
pdb-focus-tm-Ty : (pdb : Γ ⊢pd[ submax ][ d ]) → Typing-Tm Γ (getFocusTerm pdb) (getFocusType pdb)

pdb-to-Ty Base = TyAdd TyEmp TyStar
pdb-to-Ty (Extend pdb) = TyAdd (TyAdd (pdb-to-Ty pdb) (pdb-focus-ty-Ty pdb))
                               (TyArr (lift-tm-typing (pdb-focus-tm-Ty pdb))
                                      (lift-ty-typing (pdb-focus-ty-Ty pdb))
                                      (TyVarZ refl≈ty))
pdb-to-Ty (Restr pdb) = pdb-to-Ty pdb

pdb-focus-ty-Ty Base = TyStar
pdb-focus-ty-Ty (Extend pdb) = TyArr (lift-tm-typing (lift-tm-typing (pdb-focus-tm-Ty pdb)))
                                     (lift-ty-typing (lift-ty-typing (pdb-focus-ty-Ty pdb)))
                                     (lift-tm-typing (TyVarZ refl≈ty))
pdb-focus-ty-Ty (Restr pdb) = ty-base-Ty (pdb-focus-ty-Ty pdb)

pdb-focus-tm-Ty Base = TyVarZ Star≈
pdb-focus-tm-Ty (Extend pdb) = TyVarZ refl≈ty
pdb-focus-tm-Ty (Restr pdb) = ty-tgt-Ty (pdb-focus-ty-Ty pdb)
