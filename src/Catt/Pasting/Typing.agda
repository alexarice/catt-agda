open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Pasting.Typing (index : ℕ)
                           (rule : Fin index → Rule)
                           (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open import Catt.Syntax
open import Catt.Pasting
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Globular.Typing index rule lift-rule
open P index rule


pdb-to-Ty : Γ ⊢pdb → Typing-Ctx Γ
pdb-focus-ty-Ty : (pdb : Γ ⊢pdb) → Typing-Ty Γ (focus-ty pdb)
pdb-focus-tm-Ty : (pdb : Γ ⊢pdb) → Typing-Tm Γ (focus-tm pdb) (focus-ty pdb)

pdb-to-Ty Base = TyAdd TyEmp TyStar
pdb-to-Ty (Extend pdb p q) with ≃ty-to-≡ p | ≃ty-to-≡ q
... | refl | refl = TyAdd (TyAdd (pdb-to-Ty pdb)
                                 (pdb-focus-ty-Ty pdb))
                          (TyArr (lift-tm-typing (pdb-focus-tm-Ty pdb))
                                 (lift-ty-typing (pdb-focus-ty-Ty pdb))
                                 (TyVarZ (pdb-focus-ty-Ty pdb) refl≈ty))
pdb-to-Ty (Restr pdb) = pdb-to-Ty pdb

pdb-focus-ty-Ty Base = TyStar
pdb-focus-ty-Ty (Extend pdb p q) with ≃ty-to-≡ p | ≃ty-to-≡ q
... | refl | refl = lift-ty-typing (TyArr (lift-tm-typing (pdb-focus-tm-Ty pdb))
                                          (lift-ty-typing (pdb-focus-ty-Ty pdb))
                                          (TyVarZ (pdb-focus-ty-Ty pdb) refl≈ty))
pdb-focus-ty-Ty (Restr pdb) = ty-base-Ty (pdb-focus-ty-Ty pdb)

pdb-focus-tm-Ty Base = TyVarZ TyStar refl≈ty
pdb-focus-tm-Ty (Extend pdb p q) with ≃ty-to-≡ p | ≃ty-to-≡ q
... | refl | refl = TyVarZ (TyArr (lift-tm-typing (pdb-focus-tm-Ty pdb))
                                  (lift-ty-typing (pdb-focus-ty-Ty pdb))
                                  (TyVarZ (pdb-focus-ty-Ty pdb) refl≈ty))
                           refl≈ty
pdb-focus-tm-Ty (Restr pdb) = ty-tgt-Ty (pdb-focus-ty-Ty pdb)

pd-to-Ty : Γ ⊢pd → Typing-Ctx Γ
pd-to-Ty pd = pdb-to-Ty (pd-to-pdb pd)
