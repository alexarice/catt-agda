open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Dyck.Pruning.Typing (index : ℕ)
                                (rule : Fin index → Rule)
                                (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Typing index rule
-- open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Typing.Properties.Lifting index rule lift-rule
open import Catt.Dyck.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular.Typing index rule lift-rule
open import Catt.Dyck
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Discs.Typing index rule lift-rule
open import Catt.Syntax.Bundles
open P index rule

prune-project-Ty : (p : Peak dy) → Typing-Sub (dyck-to-ctx dy) (dyck-to-ctx (prune-peak p)) (prune-project p)
prune-project-Ty (⇕pk dy)
  = TyExt (TyExt (id-Ty (dyck-to-ctx-Ty dy))
                 (dyck-type-Ty dy)
                 (term-conversion (dyck-term-Ty dy) (reflexive≈ty (sym≃ty (id-on-ty (dyck-type dy))))))
          (dyck-pre-type-Ty dy)
          (term-conversion (identity-Ty (dyck-term-Ty dy) (dyck-type-Ty dy))
                           (reflexive≈ty (sym≃ty (Arr≃ (trans≃tm (lift-sub-comp-lem-tm idSub (dyck-term dy)) (id-on-tm (dyck-term dy)))
                                                       (trans≃ty (lift-sub-comp-lem-ty idSub (dyck-type dy)) (id-on-ty (dyck-type dy)))
                                                       refl≃tm))))
prune-project-Ty (⇑pk {dy = dy} p)
  = TyExt (TyExt (lift-sub-typing (lift-sub-typing (prune-project-Ty p)))
                 (dyck-type-Ty dy)
                   (TyVarS zero (TyVarZ (dyck-type-Ty (prune-peak p)) (reflexive≈ty (lift-ty-≃ (dyck-type-prune p)))) (reflexive≈ty l1)))
          (dyck-pre-type-Ty dy)
          (TyVarZ (dyck-pre-type-Ty (prune-peak p)) (reflexive≈ty (trans≃ty (dyck-type-prune (⇑pk p)) (Arr≃ (lift-sub-comp-lem-tm ⟨ (liftSub (liftSub (prune-project p))) , 1V ⟩ (liftTerm (dyck-term dy))) (lift-sub-comp-lem-ty ⟨ (liftSub (liftSub (prune-project p))) , 1V ⟩ (liftType (dyck-type dy))) refl≃tm))))
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


prune-Eq : {Γ : Ctx n} → (p : Peak dy) → Typing-Sub (dyck-to-ctx dy) Γ σ → {t : Tm n} → {A : Ty n} → peak-term p [ σ ]tm ≃tm identity t A → σ ≈[ Γ ]s prune-sub p σ ∘ prune-project p
prune-Eq {Γ = Γ} (⇕pk dy) (TyExt {t = u} (TyExt {σ = σ} {t = s} σty Aty sty) Bty tty) {t} {A} q = Ext≈ (Ext≈ (reflexive≈s (sym≃s (id-right-unit σ))) l1) l2
  where
    ity : Typing-Tm Γ (identity t A) _
    ity = transport-typing tty q

    tty2 : Typing-Tm Γ t A
    tty2 = identity-to-term-Ty ity

    Aty2 : Typing-Ty Γ A
    Aty2 = identity-to-type-Ty ity

    lem : ((liftTerm (dyck-term dy) ─⟨ liftType (dyck-type dy) ⟩⟶ Var zero) [
             ⟨ σ , s ⟩ ]ty)
            ≈[ Γ ]ty (t ─⟨ A ⟩⟶ t)
    lem = Ty-unique-≃ q tty (identity-Ty tty2 Aty2)

    l1 : s ≈[ Γ ]tm
           (dyck-term dy [ σ ]tm)
    l1 = begin
      s
        ≈⟨ tgt-eq lem  ⟩
      t
        ≈˘⟨ src-eq lem ⟩
      liftTerm (dyck-term dy) [ ⟨ σ , s ⟩ ]tm
        ≈⟨ reflexive≈tm (lift-sub-comp-lem-tm σ (dyck-term dy)) ⟩
      dyck-term dy [ σ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    l2 : u ≈[ Γ ]tm (identity (dyck-term dy) (dyck-type dy) [ σ ]tm)
    l2 = begin
      u
        ≈⟨ reflexive≈tm q ⟩
      identity t A
        ≈⟨ identity-≈ (trans≈tm (sym≈tm (src-eq lem)) (reflexive≈tm (lift-sub-comp-lem-tm σ (dyck-term dy)))) (trans≈ty (sym≈ty (base-eq lem)) (reflexive≈ty (lift-sub-comp-lem-ty σ (dyck-type dy)))) ⟩
      identity (dyck-term dy [ σ ]tm) (dyck-type dy [ σ ]ty)
        ≈˘⟨ reflexive≈tm (identity-sub (dyck-term dy) (dyck-type dy) σ) ⟩
      identity (dyck-term dy) (dyck-type dy) [ σ ]tm ∎

      where
        open Reasoning (tm-setoid-≈ Γ)



prune-Eq (⇑pk {dy = dy} p) (TyExt (TyExt {Δ = Δ} {σ = σ} σty Aty sty) Bty tty) {t} {A} q = Ext≈ (Ext≈ lem refl≈tm) refl≈tm
  where
    l4 : peak-term p [ σ ]tm ≃tm identity t A
    l4 = begin
      < peak-term p [ σ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm σ (peak-term p) ⟩
      < liftTerm (peak-term p) [ ⟨ σ , _ ⟩ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm ⟨ σ , _ ⟩ (liftTerm (peak-term p)) ⟩
      < liftTerm (liftTerm (peak-term p)) [ ⟨ ⟨ σ , _ ⟩ , _ ⟩ ]tm >tm
        ≈⟨ q ⟩
      < identity t A >tm ∎
      where
        open Reasoning tm-setoid

    lem : σ ≈[ Δ ]s  ⟨ ⟨ prune-sub p σ , _ ⟩ , _ ⟩ ∘ liftSub (liftSub (prune-project p))
    lem = begin
      < σ >s′
        ≈⟨ prune-Eq p σty l4 ⟩
      < prune-sub p σ ∘ prune-project p >s′
        ≈˘⟨ reflexive≈s (lift-sub-comp-lem-sub (prune-sub p σ) (prune-project p)) ⟩
      < ⟨ prune-sub p σ , _ ⟩ ∘ liftSub (prune-project p) >s′
        ≈˘⟨ reflexive≈s (lift-sub-comp-lem-sub ⟨ prune-sub p σ , _ ⟩ (liftSub (prune-project p))) ⟩
      < ⟨ ⟨ prune-sub p σ , _ ⟩ , _ ⟩ ∘ liftSub (liftSub (prune-project p)) >s′ ∎
      where
        open Reasoning (sub-setoid-≈ _ Δ)

prune-Eq (⇓pk p) σty q = prune-Eq p σty q

prune-sub-Ty : {Γ : Ctx n} → (p : Peak dy) → Typing-Sub (dyck-to-ctx dy) Γ σ → {t : Tm n} → {A : Ty n} → peak-term p [ σ ]tm ≃tm identity t A → Typing-Sub (dyck-to-ctx (prune-peak p)) Γ (prune-sub p σ)
prune-sub-Ty (⇕pk dy) (TyExt (TyExt σty Aty sty) Bty tty) q = σty
prune-sub-Ty (⇑pk {dy = dy} p) (TyExt (TyExt {Δ = Δ} {σ = σ} σty Aty sty) Bty tty) {t} {A} q = TyExt (TyExt (prune-sub-Ty p σty l4) (dyck-type-Ty (prune-peak p)) (term-conversion sty l1)) (dyck-pre-type-Ty (prune-peak p)) (term-conversion tty (Arr≈ l2 l3 refl≈tm))
  where
    l4 : peak-term p [ σ ]tm ≃tm identity t A
    l4 = begin
      < peak-term p [ σ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm σ (peak-term p) ⟩
      < liftTerm (peak-term p) [ ⟨ σ , _ ⟩ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm ⟨ σ , _ ⟩ (liftTerm (peak-term p)) ⟩
      < liftTerm (liftTerm (peak-term p)) [ ⟨ ⟨ σ , _ ⟩ , _ ⟩ ]tm >tm
        ≈⟨ q ⟩
      < identity t A >tm ∎
      where
        open Reasoning tm-setoid

    l1 : (dyck-type dy [ σ ]ty) ≈[ Δ ]ty
           (dyck-type (prune-peak p) [ prune-sub p σ ]ty)
    l1 = begin
      dyck-type dy [ σ ]ty
        ≈⟨ apply-sub-eq-ty (dyck-type dy) (prune-Eq p σty l4) ⟩
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
        ≈⟨ apply-sub-eq-tm (dyck-term dy) (prune-Eq p σty l4) ⟩
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

prune-sub-Ty (⇓pk p) σty q = prune-sub-Ty p σty q
