open import Catt.Typing.Rule

module Catt.Dyck.Typing {index : Set}
                        (rule : index → Rule)
                        (lift-rule : ∀ i → LiftRule rule (rule i))
                        (sub-rule : ∀ i → SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule
open import Catt.Typing.Properties.Lifting rule lift-rule
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Globular.Typing rule lift-rule
open import Catt.Globular.Properties

dyck-to-ctx-Ty : (dy : Dyck n d) → Typing-Ctx (dyck-to-ctx dy)
dyck-type-Ty : (dy : Dyck n d) → Typing-Ty (dyck-to-ctx dy) (dyck-type dy)
dyck-term-Ty : (dy : Dyck n d) → Typing-Tm (dyck-to-ctx dy) (dyck-term dy) (dyck-type dy)
dyck-pre-type-Ty : (dy : Dyck n d) → Typing-Ty (dyck-to-ctx dy , dyck-type dy)
      (lift-tm (dyck-term dy) ─⟨ lift-ty (dyck-type dy) ⟩⟶ 0V)
dyck-pre-type-Ty dy = TyArr (lift-tm-typing (dyck-term-Ty dy)) (lift-ty-typing (dyck-type-Ty dy)) (TyVar zero)

dyck-to-ctx-Ty End = TyAdd TyEmp TyStar
dyck-to-ctx-Ty (⇑ dy) = TyAdd (TyAdd (dyck-to-ctx-Ty dy) (dyck-type-Ty dy)) (dyck-pre-type-Ty dy)
dyck-to-ctx-Ty (⇓ dy) = dyck-to-ctx-Ty dy

dyck-type-Ty End = TyStar
dyck-type-Ty (⇑ dy) = lift-ty-typing (TyArr (lift-tm-typing (dyck-term-Ty dy)) (lift-ty-typing (dyck-type-Ty dy)) (TyVar zero))
dyck-type-Ty (⇓ dy) = transport-typing-ty (ty-base-Ty (dyck-type-Ty dy) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄) refl≃c (ty-base-lift (dyck-pre-type dy))

dyck-term-Ty End = TyVar zero
dyck-term-Ty (⇑ dy) = TyVar zero
dyck-term-Ty (⇓ dy) = TyConv (ty-tgt′-Ty (dyck-type-Ty dy) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄) (reflexive≈ty (ty-base-lift (dyck-pre-type dy)))
