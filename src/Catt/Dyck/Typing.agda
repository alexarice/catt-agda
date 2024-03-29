open import Catt.Typing.Rule

module Catt.Dyck.Typing (ops : Op)
                        (rules : RuleSet)
                        (wk-cond : WkCond rules)
                        (sub-cond : SubCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Weakening ops rules wk-cond
open import Catt.Globular.Typing ops rules

⌊⌋d-Ty : (dy : Dyck n d) → Typing-Ctx ⌊ dy ⌋d
dyck-type-Ty : (dy : Dyck n d) → Typing-Ty ⌊ dy ⌋d (dyck-type dy)
dyck-term-Ty : (dy : Dyck n d) → Typing-Tm ⌊ dy ⌋d (dyck-term dy) (dyck-type dy)
dyck-pre-type-Ty : (dy : Dyck n d) → Typing-Ty (⌊ dy ⌋d , dyck-type dy)
      (wk-tm (dyck-term dy) ─⟨ wk-ty (dyck-type dy) ⟩⟶ 0V)
dyck-pre-type-Ty dy = TyArr (wk-tm-typing (dyck-term-Ty dy)) (wk-ty-typing (dyck-type-Ty dy)) (TyVar zero)

⌊⌋d-Ty ⊝ = TyAdd TyEmp TyStar
⌊⌋d-Ty (⇑ dy) = TyAdd (TyAdd (⌊⌋d-Ty dy) (dyck-type-Ty dy)) (dyck-pre-type-Ty dy)
⌊⌋d-Ty (⇓ dy) = ⌊⌋d-Ty dy

dyck-type-Ty ⊝ = TyStar
dyck-type-Ty (⇑ dy) = wk-ty-typing (TyArr (wk-tm-typing (dyck-term-Ty dy)) (wk-ty-typing (dyck-type-Ty dy)) (TyVar zero))
dyck-type-Ty (⇓ dy) = transport-typing-ty (ty-base-Ty (dyck-type-Ty dy) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄) refl≃c (ty-base-wk (dyck-pre-type dy))

dyck-term-Ty ⊝ = TyVar zero
dyck-term-Ty (⇑ dy) = TyVar zero
dyck-term-Ty (⇓ dy) = TyConv (ty-tgt′-Ty (dyck-type-Ty dy) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄) (reflexive≈ty (ty-base-wk (dyck-pre-type dy)))
