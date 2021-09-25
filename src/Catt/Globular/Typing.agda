{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Globular.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open P index rule
open import Catt.Syntax
open import Catt.Globular

tm-to-ty-prop : Typing-Tm Γ t A → tm-to-ty Γ t ≈[ Γ ]ty A
tm-to-ty-prop (TyVarZ x) = x
tm-to-ty-prop (TyVarS i tty x) = trans≈ty (lift-ty-equality (tm-to-ty-prop tty)) x
tm-to-ty-prop (TyCoh v w x y z) = z

tm-to-ty-Ty : Typing-Tm Γ t A → Typing-Tm Γ t (tm-to-ty Γ t)
tm-to-ty-Ty (TyVarZ x) = TyVarZ refl≈ty
tm-to-ty-Ty (TyVarS i tty x) = TyVarS i (tm-to-ty-Ty tty) refl≈ty
tm-to-ty-Ty (TyCoh v w x y z) = TyCoh v w x y refl≈ty
