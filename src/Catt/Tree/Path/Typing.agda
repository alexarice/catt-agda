open import Catt.Typing.Rule

module Catt.Tree.Path.Typing {index : Set}
                             (rule : index → Rule)
                             (lift-rule : ∀ i → LiftRule rule (rule i))
                             (susp-rule : ∀ i → SuspRule rule (rule i))
                             (sub-rule : ∀ i → SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

open import Catt.Typing rule
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Suspension.Typing rule lift-rule susp-rule
open import Catt.Connection.Typing rule lift-rule susp-rule sub-rule

getPathType : (P : Path S) → STy (someTree S)
getPathType PHere = S⋆
getPathType (PExt P) = map-sty-ext (getPathType P)
getPathType (PShift P) = map-sty-shift (getPathType P)

path-to-term-Ty : (P : Path S) → Typing-Tm (tree-to-ctx S) (path-to-term P) (sty-to-type (getPathType P))
path-to-term-Ty {S = S} PHere = fromℕ-Ty (tree-to-ctx S)
path-to-term-Ty (PExt {T = T} P) = TyConv (apply-sub-tm-typing (susp-tmTy (path-to-term-Ty P)) (connect-susp-inc-left-Ty (tree-to-ctx T))) (reflexive≈ty (begin
  < susp-ty (sty-to-type (getPathType P)) [ connect-susp-inc-left _ _ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (susp-sty-to-type (getPathType P)) refl≃s ⟩
  < sty-to-type (susp-sty (getPathType P)) [ connect-susp-inc-left _ (tree-size T) ]ty >ty
    ≈˘⟨ sty-sub-to-type (susp-sty (getPathType P)) (connect-susp-inc-left _ (tree-size T)) ⟩
  < sty-to-type (susp-sty (getPathType P) [ connect-susp-inc-left _ (tree-size T) ]sty) >ty
    ≈⟨ map-sty-ext-prop (getPathType P) .get  ⟩
  < sty-to-type (map-sty-ext (getPathType P)) >ty ∎))
  where
    open Reasoning ty-setoid
path-to-term-Ty (PShift {S = S} P) = TyConv (apply-sub-tm-typing (path-to-term-Ty P) (connect-susp-inc-right-Ty (tree-to-ctx S))) (reflexive≈ty (begin
  < sty-to-type (getPathType P) [ connect-susp-inc-right _ _ ]ty >ty
    ≈˘⟨ sty-sub-to-type (getPathType P) (connect-susp-inc-right _ _) ⟩
  < sty-to-type (getPathType P [ connect-susp-inc-right (tree-size S) _ ]sty) >ty
    ≈˘⟨ map-sty-shift-prop (getPathType P) .get ⟩
  < sty-to-type (map-sty-shift (getPathType P)) >ty ∎))
  where
    open Reasoning ty-setoid
