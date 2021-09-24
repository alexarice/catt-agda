{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Discs.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule props
open import Catt.Syntax
open import Catt.Discs
open import Catt.Globular
open import Catt.Globular.Typing index rule props
open import Catt.Discs.Properties
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality

sub-from-sphere-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Sub (Sphere d) Γ (sub-from-sphere d A p)
sub-from-sphere-Ty zero TyStar p = TyNull TyStar
sub-from-sphere-Ty (suc d) (TyArr sty Aty tty) p = TyExt (TyExt (sub-from-sphere-Ty d Aty (cong pred p))
                                                      (term-conversion sty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ (cong pred p))))))
                                               (term-conversion tty (reflexive≈ty (sym≃ty (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere d _ (cong pred p)) (sphere-type _)) (sub-from-sphere-prop d _ (cong pred p))))))

sub-from-disc-Ty : (d : ℕ) → Typing-Ty Γ A → .(p : ty-dim A ≡ d) → Typing-Tm Γ t A → Typing-Sub (Disc d) Γ (sub-from-disc d A p t)
sub-from-disc-Ty {t = t} d Aty p tty = TyExt (sub-from-sphere-Ty d Aty p) (term-conversion tty (reflexive≈ty (sym≃ty (sub-from-sphere-prop d _ p))))
