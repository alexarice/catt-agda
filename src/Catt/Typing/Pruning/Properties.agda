open import Catt.Typing.Rule
import Catt.Typing.Pruning as Pr

module Catt.Typing.Pruning.Properties (rules : RuleSet)
                                      (lift-cond : LiftCond rules)
                                      (sub-cond : SubCond rules)
                                      (pr : Pr.HasPruning rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Discs
open import Catt.Dyck
open import Catt.Dyck.Pasting
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Properties

open import Catt.Typing rules
open import Catt.Dyck.Pruning.Typing rules lift-cond sub-cond
open import Catt.Typing.Properties.Base rules
open import Catt.Typing.Properties.Substitution rules lift-cond sub-cond
open import Catt.Globular.Typing rules lift-cond

open Pr rules
{-
conv-rule : {Γ : Ctx n}
          → {dy : Dyck (suc m) 0}
          → (p : Peak dy)
          → {B : Ty n}
          → {t : Tm n}
          → peak-term p [ σ ]tm ≃tm identity-term B t
          → ConvRule (Pruning Γ dy A p σ)
conv-rule {σ = σ} {A = A} {Γ = Γ} {dy} p pf {C} tty
  = TyConv (TyCoh ⦃ dyck-to-pd (dy // p) ⦄
                  (apply-sub-ty-typing Aty (π-Ty p))
                  (prune-sub-Ty p σty pf))
           lem
  where
    Aty : Typing-Ty ⌊ dy ⌋d A
    Aty = coh-ty-ty tty

    σty : Typing-Sub ⌊ dy ⌋d _ σ
    σty = coh-sub-ty tty

    lem : (A [ π p ]ty) [ σ //s p ]ty ≈[ Γ ]ty C
    lem = begin
      (A [ π p ]ty) [ σ //s p ]ty
        ≈˘⟨ reflexive≈ty (assoc-ty (σ //s p) (π p) A) ⟩
      A [ (σ //s p) ● π p ]ty
        ≈˘⟨ apply-sub-eq-ty A (prune-Eq p σty pf) ⟩
      A [ σ ]ty
        ≈⟨ tm-to-ty-prop tty ⟩
      C ∎
      where
        open Reasoning (ty-setoid-≈ Γ)
-}
