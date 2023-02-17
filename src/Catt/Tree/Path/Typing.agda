open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Path.Typing {index : Set}
                             (rule : index → Rule)
                             (lift-rule : ∀ i → P.LiftRule rule (rule i))
                             (susp-rule : ∀ i → P.SuspRule rule (rule i))
                             (sub-rule : ∀ i → P.SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Typing rule
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Properties
open import Catt.Tree.Typing rule lift-rule susp-rule sub-rule
open import Catt.Suspension
open import Catt.Suspension.Typing rule lift-rule susp-rule
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Typing rule lift-rule susp-rule sub-rule
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing rule lift-rule
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties

getPathType : (P : Path S) → STy (someTree S)
getPathType PHere = S⋆
getPathType (PExt P) = map-sty-pext (getPathType P)
getPathType (PShift P) = map-sty-pshift (getPathType P)

path-to-term-Ty : (P : Path S) → Typing-Tm (tree-to-ctx S) (path-to-term P) (sty-to-type (getPathType P))
path-to-term-Ty {S = S} PHere = fromℕ-Ty (tree-to-ctx S)
path-to-term-Ty (PExt {T = T} P) = TyConv (apply-sub-tm-typing (susp-tmTy (path-to-term-Ty P)) (connect-susp-inc-left-Ty (tree-to-ctx T))) (reflexive≈ty (begin
  < susp-ty (sty-to-type (getPathType P)) [ connect-susp-inc-left _ _ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (susp-sty-to-type (getPathType P)) refl≃s ⟩
  < sty-to-type (susp-sty (getPathType P)) [ connect-susp-inc-left _ (tree-size T) ]ty >ty
    ≈˘⟨ sty-sub-prop (susp-sty (getPathType P)) (connect-susp-inc-left _ (tree-size T)) ⟩
  < sty-to-type (sty-sub (susp-sty (getPathType P)) (connect-susp-inc-left _ (tree-size T))) >ty
    ≈⟨ map-sty-pext-prop (getPathType P) .get  ⟩
  < sty-to-type (map-sty-pext (getPathType P)) >ty ∎))
  where
    open Reasoning ty-setoid
path-to-term-Ty (PShift {S = S} P) = TyConv (apply-sub-tm-typing (path-to-term-Ty P) (connect-susp-inc-right-Ty (tree-to-ctx S))) (reflexive≈ty (begin
  < sty-to-type (getPathType P) [ connect-susp-inc-right _ _ ]ty >ty
    ≈˘⟨ sty-sub-prop (getPathType P) (connect-susp-inc-right _ _) ⟩
  < sty-to-type (sty-sub (getPathType P) (connect-susp-inc-right (tree-size S) _)) >ty
    ≈˘⟨ map-sty-pshift-prop (getPathType P) .get ⟩
  < sty-to-type (map-sty-pshift (getPathType P)) >ty ∎))
  where
    open Reasoning ty-setoid
