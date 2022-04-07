open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Dyck.Typing (index : ℕ)
                        (rule : Fin index → Rule)
                        (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                        (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Dyck
open import Catt.Typing.Properties.Lifting index rule lift-rule
open import Catt.Globular
open import Catt.Globular.Typing index rule lift-rule
open import Catt.Typing.Properties.Substitution index rule lift-rule sub-rule
open import Catt.Globular.Properties
open import Catt.Dyck.Properties
open import Catt.Syntax.SyntacticEquality
open P index rule

dyck-to-ctx-Ty : (dy : Dyck n d) → Typing-Ctx (dyck-to-ctx dy)
dyck-type-Ty : (dy : Dyck n d) → Typing-Ty (dyck-to-ctx dy) (dyck-type dy)
dyck-term-Ty : (dy : Dyck n d) → Typing-Tm (dyck-to-ctx dy) (dyck-term dy) (dyck-type dy)
dyck-pre-type-Ty : (dy : Dyck n d) → Typing-Ty (dyck-to-ctx dy , dyck-type dy)
      (liftTerm (dyck-term dy) ─⟨ liftType (dyck-type dy) ⟩⟶ 0V)
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
