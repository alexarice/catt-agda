open import Catt.Typing.Rule

module Catt.Dyck.Typing (rules : RuleSet)
                        (lift-cond : LiftCond rules)
                        (sub-cond : SubCond rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules
open import Catt.Typing.Properties.Lifting rules lift-cond
open import Catt.Globular.Typing rules lift-cond

⌊⌋d-Ty : (dy : Dyck n d) → Typing-Ctx ⌊ dy ⌋d
dyck-type-Ty : (dy : Dyck n d) → Typing-Ty ⌊ dy ⌋d (dyck-type dy)
dyck-term-Ty : (dy : Dyck n d) → Typing-Tm ⌊ dy ⌋d (dyck-term dy) (dyck-type dy)
dyck-pre-type-Ty : (dy : Dyck n d) → Typing-Ty (⌊ dy ⌋d , dyck-type dy)
      (lift-tm (dyck-term dy) ─⟨ lift-ty (dyck-type dy) ⟩⟶ 0V)
dyck-pre-type-Ty dy = TyArr (lift-tm-typing (dyck-term-Ty dy)) (lift-ty-typing (dyck-type-Ty dy)) (TyVar zero)

⌊⌋d-Ty End = TyAdd TyEmp TyStar
⌊⌋d-Ty (⇑ dy) = TyAdd (TyAdd (⌊⌋d-Ty dy) (dyck-type-Ty dy)) (dyck-pre-type-Ty dy)
⌊⌋d-Ty (⇓ dy) = ⌊⌋d-Ty dy

dyck-type-Ty End = TyStar
dyck-type-Ty (⇑ dy) = lift-ty-typing (TyArr (lift-tm-typing (dyck-term-Ty dy)) (lift-ty-typing (dyck-type-Ty dy)) (TyVar zero))
dyck-type-Ty (⇓ dy) = transport-typing-ty (ty-base-Ty (dyck-type-Ty dy) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄) refl≃c (ty-base-lift (dyck-pre-type dy))

dyck-term-Ty End = TyVar zero
dyck-term-Ty (⇑ dy) = TyVar zero
dyck-term-Ty (⇓ dy) = TyConv (ty-tgt′-Ty (dyck-type-Ty dy) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄) (reflexive≈ty (ty-base-lift (dyck-pre-type dy)))
