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

prune-project-Ty : (p : Peak dy) → Typing-Sub (dyck-to-ctx dy) (dyck-to-ctx (prune-peak p)) (prune-project p)
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

prune-sub-Ty : (p : Peak dy) → Typing-Sub (dyck-to-ctx dy) Γ σ → Typing-Sub (dyck-to-ctx (prune-peak p)) Γ (prune-sub p σ)
prune-Eq : (p : Peak dy) → Typing-Sub (dyck-to-ctx dy) Γ σ → σ ≈[ Γ ]s prune-sub p σ ∘ prune-project p

prune-sub-Ty (⇕pk dy) (TyExt (TyExt σty Aty sty) Bty tty) = σty
prune-sub-Ty (⇑pk {dy = dy} p) (TyExt (TyExt {Δ = Δ} {σ = σ} σty Aty sty) Bty tty) = TyExt (TyExt (prune-sub-Ty p σty) (dyck-type-Ty (prune-peak p)) (term-conversion sty l1)) (dyck-lem-Ty (prune-peak p)) (term-conversion tty (Arr≈ l2 l3 refl≈tm))
  where
    l1 : (dyck-type dy [ σ ]ty) ≈[ Δ ]ty
           (dyck-type (prune-peak p) [ prune-sub p σ ]ty)
    l1 = begin
      dyck-type dy [ σ ]ty
        ≈⟨ apply-sub-eq-ty (dyck-type dy) {!!} ⟩
      dyck-type dy [ prune-sub p σ ∘ prune-project p ]ty
        ≈⟨ reflexive≈ty (assoc-ty (prune-sub p σ) (prune-project p) (dyck-type dy)) ⟩
      dyck-type dy [ prune-project p ]ty [ prune-sub p σ ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (dyck-type-prune p) refl≃s) ⟩
      dyck-type (prune-peak p) [ prune-sub p σ ]ty ∎
      where
        open Reasoning (ty-setoid-≈ Δ)

    l2 : (liftTerm (dyck-term dy) [ ⟨ σ , _ ⟩ ]tm) ≈[ Δ ]tm
           (liftTerm (dyck-term (prune-peak p)) [ ⟨ prune-sub p σ , _ ⟩ ]tm)
    l2 = begin
      liftTerm (dyck-term dy) [ ⟨ σ , _ ⟩ ]tm
        ≈⟨ reflexive≈tm (lift-sub-comp-lem-tm σ (dyck-term dy)) ⟩
      dyck-term dy [ σ ]tm
        ≈⟨ apply-sub-eq-tm (dyck-term dy) {!!} ⟩
      dyck-term dy [ prune-sub p σ ∘ prune-project p ]tm
        ≈⟨ reflexive≈tm (assoc-tm (prune-sub p σ) (prune-project p) (dyck-term dy)) ⟩
      dyck-term dy [ prune-project p ]tm [ prune-sub p σ ]tm
        ≈˘⟨ reflexive≈tm (sub-action-≃-tm (dyck-term-prune p) refl≃s) ⟩
      dyck-term (prune-peak p) [ prune-sub p σ ]tm
        ≈˘⟨ reflexive≈tm (lift-sub-comp-lem-tm (prune-sub p σ) (dyck-term (prune-peak p))) ⟩
      liftTerm (dyck-term (prune-peak p)) [ ⟨ prune-sub p σ , _ ⟩ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Δ)

    l3 : (liftType (dyck-type dy) [ ⟨ σ , _ ⟩ ]ty) ≈[ Δ ]ty
           (liftType (dyck-type (prune-peak p)) [ ⟨ prune-sub p σ , _ ⟩ ]ty)
    l3 = begin
      liftType (dyck-type dy) [ ⟨ σ , _ ⟩ ]ty
        ≈⟨ reflexive≈ty (lift-sub-comp-lem-ty σ (dyck-type dy)) ⟩
      dyck-type dy [ σ ]ty
        ≈⟨ l1 ⟩
      dyck-type (prune-peak p) [ prune-sub p σ ]ty
        ≈˘⟨ reflexive≈ty (lift-sub-comp-lem-ty (prune-sub p σ) (dyck-type (prune-peak p))) ⟩
      liftType (dyck-type (prune-peak p)) [ ⟨ prune-sub p σ , _ ⟩ ]ty ∎
      where
        open Reasoning (ty-setoid-≈ Δ)

prune-sub-Ty (⇓pk p) σty = prune-sub-Ty p σty

prune-Eq (⇕pk dy) (TyExt (TyExt {σ = σ} σty Aty sty) Bty tty) = Ext≈ (Ext≈ (reflexive≈s (sym≃s (id-right-unit σ))) {!!}) {!!}
prune-Eq (⇑pk {dy = dy} p) (TyExt (TyExt {Δ = Δ} {σ = σ} σty Aty sty) Bty tty) = Ext≈ (Ext≈ lem refl≈tm) refl≈tm
  where
    lem : σ ≈[ Δ ]s  ⟨ ⟨ prune-sub p σ , _ ⟩ , _ ⟩ ∘ liftSub (liftSub (prune-project p))
    lem = begin
      < σ >s′
        ≈⟨ prune-Eq p σty ⟩
      < prune-sub p σ ∘ prune-project p >s′
        ≈˘⟨ reflexive≈s (lift-sub-comp-lem-sub (prune-sub p σ) (prune-project p)) ⟩
      < ⟨ prune-sub p σ , _ ⟩ ∘ liftSub (prune-project p) >s′
        ≈˘⟨ reflexive≈s (lift-sub-comp-lem-sub ⟨ prune-sub p σ , _ ⟩ (liftSub (prune-project p))) ⟩
      < ⟨ ⟨ prune-sub p σ , _ ⟩ , _ ⟩ ∘ liftSub (liftSub (prune-project p)) >s′ ∎
      where
        open Reasoning (sub-setoid-≈ _ Δ)
prune-Eq (⇓pk p) σty = prune-Eq p σty
