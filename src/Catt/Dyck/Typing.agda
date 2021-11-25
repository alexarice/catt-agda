{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Dyck.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Dyck
open import Catt.Typing.Properties.Lifting index rule lift-rule
open import Catt.Globular
open import Catt.Globular.Typing index rule lift-rule
open import Catt.Dyck.Properties
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open P index rule



dyck-to-ctx-Ty : (dy : Dyck n d) → Typing-Ctx (dyck-to-ctx dy)
dyck-type-Ty : (dy : Dyck n d) → Typing-Ty (dyck-to-ctx dy) (dyck-type dy)
dyck-term-Ty : (dy : Dyck n d) → Typing-Tm (dyck-to-ctx dy) (dyck-term dy) (dyck-type dy)
dyck-lem-Ty : (dy : Dyck n d) → Typing-Ty (dyck-to-ctx dy , dyck-type dy)
      (liftTerm (dyck-term dy) ─⟨ liftType (dyck-type dy) ⟩⟶ 0V)
dyck-lem-Ty dy = TyArr (lift-tm-typing (dyck-term-Ty dy)) (lift-ty-typing (dyck-type-Ty dy)) (TyVarZ (dyck-type-Ty dy) refl≈ty)

dyck-to-ctx-Ty End = TyAdd TyEmp TyStar
dyck-to-ctx-Ty (⇑ dy) = TyAdd (TyAdd (dyck-to-ctx-Ty dy) (dyck-type-Ty dy)) (dyck-lem-Ty dy)
dyck-to-ctx-Ty (⇓ dy) = dyck-to-ctx-Ty dy

dyck-type-Ty End = TyStar
dyck-type-Ty (⇑ dy) = lift-ty-typing (TyArr (lift-tm-typing (dyck-term-Ty dy)) (lift-ty-typing (dyck-type-Ty dy)) (TyVarZ (dyck-type-Ty dy) refl≈ty))
dyck-type-Ty (⇓ dy) = ty-base-Ty (dyck-type-Ty dy) (<-transˡ 0<1+n (≤-reflexive (sym (dyck-type-dim dy))))

dyck-term-Ty End = TyVarZ TyStar refl≈ty
dyck-term-Ty (⇑ dy) = TyVarZ (dyck-lem-Ty dy) refl≈ty
dyck-term-Ty (⇓ dy) = ty-tgt-Ty (dyck-type-Ty dy) (<-transˡ 0<1+n (≤-reflexive (sym (dyck-type-dim dy))))
