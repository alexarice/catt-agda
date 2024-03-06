open import Catt.Typing.Rule

module Catt.Pasting.Typing (ops : Op)
                           (rules : RuleSet)
                           (lift-cond : LiftCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Lifting ops rules lift-cond
open import Catt.Globular.Typing ops rules



pdb-to-Ty : Γ ⊢pdb → Typing-Ctx Γ
pdb-focus-ty-Ty : (pdb : Γ ⊢pdb) → Typing-Ty Γ (focus-ty pdb)
pdb-focus-tm-Ty : (pdb : Γ ⊢pdb) → Typing-Tm Γ (focus-tm pdb) (focus-ty pdb)

pdb-to-Ty Base = TyAdd TyEmp TyStar
pdb-to-Ty (Extend pdb p q) with ≃ty-to-≡ p | ≃ty-to-≡ q
... | refl | refl = TyAdd (TyAdd (pdb-to-Ty pdb)
                                 (pdb-focus-ty-Ty pdb))
                          (TyArr (lift-tm-typing (pdb-focus-tm-Ty pdb))
                                 (lift-ty-typing (pdb-focus-ty-Ty pdb))
                                 (TyVar zero))
pdb-to-Ty (Restr pdb) = pdb-to-Ty pdb

pdb-focus-ty-Ty Base = TyStar
pdb-focus-ty-Ty (Extend pdb p q) with ≃ty-to-≡ p | ≃ty-to-≡ q
... | refl | refl = lift-ty-typing (TyArr (lift-tm-typing (pdb-focus-tm-Ty pdb))
                                          (lift-ty-typing (pdb-focus-ty-Ty pdb))
                                          (TyVar zero))
pdb-focus-ty-Ty (Restr pdb) = ty-base-Ty (pdb-focus-ty-Ty pdb)

pdb-focus-tm-Ty Base = TyVar zero
pdb-focus-tm-Ty (Extend pdb p q) with ≃ty-to-≡ p | ≃ty-to-≡ q
... | refl | refl = TyVar zero
pdb-focus-tm-Ty (Restr pdb) = ty-tgt-Ty (pdb-focus-ty-Ty pdb)

pd-to-Ty : Γ ⊢pd → Typing-Ctx Γ
pd-to-Ty pd = pdb-to-Ty (pd-to-pdb pd)
