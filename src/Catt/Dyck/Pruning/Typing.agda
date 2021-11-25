{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Dyck.Pruning.Typing (index : ℕ)
                                 (rule : Fin index → Rule)
                                 (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                 (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                 (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Syntax
open import Catt.Typing index rule
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Dyck.Typing index rule lift-rule
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased.Typing index rule lift-rule susp-rule sub-rule

open import Catt.Dyck
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Properties

open import Catt.Syntax.Bundles
import Relation.Binary.Reasoning.Setoid as Reasoning

prune-project-Ty : {dy : Dyck (2 + n) d} → (p : Peak dy) → Typing-Sub (dyck-to-ctx dy) (dyck-to-ctx (prune-peak p)) (prune-project p)
prune-project-Ty (⇕pk dy)
  = TyExt (TyExt (id-Ty (dyck-to-ctx-Ty dy))
                 (dyck-type-Ty dy)
                 (term-conversion (dyck-term-Ty dy) (reflexive≈ty (sym≃ty (id-on-ty (dyck-type dy))))))
          (dyck-lem-Ty dy)
          (term-conversion (identity-Ty (dyck-term-Ty dy) (dyck-type-Ty dy))
                           (reflexive≈ty (sym≃ty (Arr≃ (trans≃tm (lift-sub-comp-lem-tm (idSub _) (dyck-term dy)) (id-on-tm (dyck-term dy)))
                                                       (trans≃ty (lift-sub-comp-lem-ty (idSub _) (dyck-type dy)) (id-on-ty (dyck-type dy)))
                                                       refl≃tm))))
prune-project-Ty (⇑pk {dy = dy} p)
  = TyExt (TyExt (lift-sub-typing (lift-sub-typing (prune-project-Ty p)))
                 (dyck-type-Ty dy)
                   (TyVarS zero (TyVarZ (dyck-type-Ty (prune-peak p)) (reflexive≈ty (lift-ty-≃ (dyck-type-prune p)))) (reflexive≈ty l1)))
          (dyck-lem-Ty dy)
          (TyVarZ (dyck-lem-Ty (prune-peak p)) (reflexive≈ty (trans≃ty (dyck-type-prune (⇑pk p)) (Arr≃ (lift-sub-comp-lem-tm ⟨ (liftSub (liftSub (prune-project p))) , 1V ⟩ (liftTerm (dyck-term dy))) (lift-sub-comp-lem-ty ⟨ (liftSub (liftSub (prune-project p))) , 1V ⟩ (liftType (dyck-type dy))) refl≃tm))))
  where
    l1 : liftType (liftType (dyck-type dy [ prune-project p ]ty)) ≃ty
           (dyck-type dy [ liftSub (liftSub (prune-project p)) ]ty)
    l1 = begin
      < liftType (liftType (dyck-type dy [ prune-project p ]ty)) >ty
        ≈˘⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type dy) (prune-project p)) ⟩
      < liftType (dyck-type dy [ liftSub (prune-project p) ]ty) >ty
        ≈˘⟨ apply-lifted-sub-ty-≃ (dyck-type dy) (liftSub (prune-project p)) ⟩
      < dyck-type dy [ liftSub (liftSub (prune-project p)) ]ty >ty ∎
      where
        open Reasoning ty-setoid
prune-project-Ty (⇓pk p) = prune-project-Ty p
