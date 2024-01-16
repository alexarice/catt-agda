open import Catt.Typing.Rule

module Catt.Tree.Path.Typing (rules : RuleSet)
                             (tame : Tame rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

open import Catt.Typing rules
open import Catt.Typing.Properties rules tame
open import Catt.Suspension.Typing rules lift-cond susp-cond
open import Catt.Connection.Typing rules tame

path-to-term-Ty : (P : Path S) → Typing-Tm ⌊ S ⌋ (path-to-term P) (sty-to-type (getPathType P))
path-to-term-Ty {S = S} PHere = fromℕ-Ty ⌊ S ⌋
path-to-term-Ty (PExt {T = T} P) = TyConv (apply-sub-tm-typing (susp-tmTy (path-to-term-Ty P)) (connect-susp-inc-left-Ty ⌊ T ⌋)) (reflexive≈ty (begin
  < susp-ty (sty-to-type (getPathType P)) [ connect-susp-inc-left _ _ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (susp-sty-to-type (getPathType P)) refl≃s ⟩
  < sty-to-type (susp-sty (getPathType P)) [ connect-susp-inc-left _ (tree-size T) ]ty >ty
    ≈˘⟨ sty-sub-to-type (susp-sty (getPathType P)) (connect-susp-inc-left _ (tree-size T)) ⟩
  < sty-to-type (susp-sty (getPathType P) [ connect-susp-inc-left _ (tree-size T) ]sty) >ty
    ≈⟨ map-sty-ext-prop (getPathType P) .get  ⟩
  < sty-to-type (map-sty-ext (getPathType P)) >ty ∎))
  where
    open Reasoning ty-setoid
path-to-term-Ty (PShift {S = S} P) = TyConv (apply-sub-tm-typing (path-to-term-Ty P) (connect-susp-inc-right-Ty ⌊ S ⌋)) (reflexive≈ty (begin
  < sty-to-type (getPathType P) [ connect-susp-inc-right _ _ ]ty >ty
    ≈˘⟨ sty-sub-to-type (getPathType P) (connect-susp-inc-right _ _) ⟩
  < sty-to-type (getPathType P [ connect-susp-inc-right (tree-size S) _ ]sty) >ty
    ≈˘⟨ map-sty-shift-prop (getPathType P) .get ⟩
  < sty-to-type (map-sty-shift (getPathType P)) >ty ∎))
  where
    open Reasoning ty-setoid
