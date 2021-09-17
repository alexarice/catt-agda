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

sub-from-sphere-Ty : {A : Ty n d} → Typing-Ty Γ A → Typing-Sub (Sphere d) Γ (sub-from-sphere A)
sub-from-sphere-Ty TyStar = TyNull
sub-from-sphere-Ty (TyArr sty Aty tty) = TyExt (TyExt (sub-from-sphere-Ty Aty)
                                                      (term-conversion sty (reflexive≈ty (sym≃ty (sub-from-sphere-prop _)))))
                                               (term-conversion tty (reflexive≈ty (sym≃ty (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere _) (sphere-type _)) (sub-from-sphere-prop _)))))

sub-from-disc-Ty : Typing-Ty Γ (tm-to-ty Γ t) → Typing-Tm Γ t A → Typing-Sub (Disc (get-tm-height Γ t)) Γ (sub-from-disc Γ t)
sub-from-disc-Ty {Γ = Γ} {t = t} Aty tty = TyExt (sub-from-sphere-Ty Aty) (term-conversion tty (sym≈ty (trans≈ty (reflexive≈ty (sub-from-sphere-prop (tm-to-ty Γ t))) (tm-to-ty-prop {Γ = Γ} tty))))
