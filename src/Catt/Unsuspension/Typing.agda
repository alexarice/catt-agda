{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Unsuspension.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Typing.Properties index rule props
open import Catt.Unsuspension
open import Catt.Unsuspension.Properties
open import Data.Product renaming (_,_ to _,,_)

unsuspend-ctx-Ty : Typing-Ctx Γ
                 → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                 → Typing-Ctx (unsuspend-ctx Γ)
unsuspend-ty-Ty : Typing-Ty Γ A
                → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                → .⦃ _ : is-unsuspendable-ty A ⦄
                → Typing-Ty (unsuspend-ctx Γ) (unsuspend-ty A)
unsuspend-tm-Ty : Typing-Tm Γ t A
                → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                → .⦃ _ : is-unsuspendable-tm t ⦄
                → .⦃ _ : is-unsuspendable-ty A ⦄
                → Typing-Tm (unsuspend-ctx Γ) (unsuspend-tm t) (unsuspend-ty A)
unsuspend-sub-Ty : Typing-Sub Γ Δ σ
                 → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                 → .⦃ _ : is-unsuspendable-ctx Δ ⦄
                 → .⦃ _ : is-unsuspendable-sub σ ⦄
                 → Typing-Sub (unsuspend-ctx Γ) (unsuspend-ctx Δ) (unsuspend-sub σ)

unsuspend-ctx-Ty (TyAdd (TyAdd TyEmp TyStar) TyStar) = TyEmp
unsuspend-ctx-Ty (TyAdd (TyAdd (TyAdd Γty z) y) x) ⦃ us ⦄ = TyAdd (unsuspend-ctx-Ty (TyAdd (TyAdd Γty z) y) ⦃ proj₁ us ⦄) (unsuspend-ty-Ty x ⦃ proj₁ us ⦄ ⦃ proj₂ us ⦄)

unsuspend-ty-Ty (TyArr sty TyStar tty) = TyStar
unsuspend-ty-Ty (TyArr sty Aty@(TyArr _ _ _) tty) ⦃ usc ⦄ ⦃ usy ⦄ = let
  instance .x : _
           x = proj₁ usy
           .y : _
           y = proj₁ (proj₂ usy)
           .z : _
           z = proj₂ (proj₂ usy)
  in TyArr (unsuspend-tm-Ty sty) (unsuspend-ty-Ty Aty) (unsuspend-tm-Ty tty)

unsuspend-tm-Ty (TyVarZ {A = A} x) = {!!}
unsuspend-tm-Ty (TyVarS i tty x) = {!!}
unsuspend-tm-Ty (TyCoh {Δ = Δ , A , B , C} pd w x y z) ⦃ uΓ ⦄ ⦃ u ⦄ ⦃ _ ⦄ = TyCoh (unsuspend-pd pd ⦃ proj₁ u ⦄) (unsuspend-ty-Ty w ⦃ proj₁ u ⦄ ⦃ proj₁ (proj₂ u) ⦄) (unsuspend-sub-Ty x ⦃ proj₁ u ⦄ ⦃ uΓ ⦄ ⦃ {!proj₂ (proj₂ u)!} ⦄) {!!} {!!}
unsuspend-tm-Ty (TyComp pd v w x y z) = {!!}

unsuspend-sub-Ty (TyExt {A = B} (TyExt {A = A} TyNull y) x) with B | A
... | ⋆ | ⋆ = TyNull
unsuspend-sub-Ty (TyExt (TyExt (TyExt σty z) y) x) ⦃ usΓ ⦄ ⦃ usΔ ⦄ ⦃ usσ ⦄ = TyExt (unsuspend-sub-Ty (TyExt (TyExt σty z) y) ⦃ proj₁ usΓ ⦄ ⦃ it ⦄ ⦃ proj₁ usσ ⦄) (term-conversion (unsuspend-tm-Ty x ⦃ it ⦄ ⦃ proj₂ usσ ⦄ ⦃ is-unsuspendable-functorial-ty _ ⦃ proj₂ usΓ ⦄ _ ⦃ proj₁ usσ ⦄ ⦄) (reflexive≈ty (unsuspend-functorial-ty _ ⦃ proj₂ usΓ ⦄ _ ⦃ proj₁ usσ ⦄)))
