open import Catt.Typing.Rule

module Catt.Dyck.Pruning.Typing {index : Set}
                                (rule : index → Rule)
                                (lift-rule : ∀ i → LiftRule rule (rule i))
                                (sub-rule : ∀ i → SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Dyck
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Properties

open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule
open import Catt.Typing.Properties.Lifting rule lift-rule
open import Catt.Typing.Properties.Substitution rule lift-rule sub-rule
open import Catt.Globular.Typing rule lift-rule
open import Catt.Discs.Typing rule lift-rule
open import Catt.Dyck.Typing rule lift-rule sub-rule

π-Ty : (p : Peak dy) → Typing-Sub ⌊ dy ⌋d ⌊ _ // p ⌋d (π p)
π-Ty (⇕pk dy)
  = TyExt (TyExt id-Ty
                 (TyConv (dyck-term-Ty dy) (reflexive≈ty (sym≃ty (id-on-ty (dyck-type dy))))))
          (TyConv (identity-term-Ty (dyck-type-Ty dy) (dyck-term-Ty dy))
                           (reflexive≈ty (sym≃ty (Arr≃ (trans≃tm (lift-sub-comp-lem-tm idSub (dyck-term dy)) (id-on-tm (dyck-term dy)))
                                                       (trans≃ty (lift-sub-comp-lem-ty idSub (dyck-type dy)) (id-on-ty (dyck-type dy)))
                                                       refl≃tm))))
π-Ty (⇑pk {dy = dy} p)
  = TyExt (TyExt (lift-sub-typing (lift-sub-typing (π-Ty p)))
                 (TyConv (TyVar (suc zero)) (reflexive≈ty l1)))
          (TyConv (TyVar zero)
                  (reflexive≈ty (trans≃ty (dyck-type-prune (⇑pk p))
                                          (Arr≃ (lift-sub-comp-lem-tm ⟨ lift-sub (lift-sub (π p)) , 1V ⟩
                                                                      (lift-tm (dyck-term dy)))
                                                (lift-sub-comp-lem-ty ⟨ (lift-sub (lift-sub (π p))) , 1V ⟩
                                                                      (lift-ty (dyck-type dy)))
                                                refl≃tm))))
  where
    l1 : lift-ty (lift-ty (dyck-type (dy // p))) ≃ty
           (dyck-type dy [ lift-sub (lift-sub (π p)) ]ty)
    l1 = begin
      < lift-ty (lift-ty (dyck-type (dy // p))) >ty
        ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-prune p)) ⟩
      < lift-ty (lift-ty (dyck-type dy [ π p ]ty)) >ty
        ≈˘⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type dy) (π p)) ⟩
      < lift-ty (dyck-type dy [ lift-sub (π p) ]ty) >ty
        ≈˘⟨ apply-lifted-sub-ty-≃ (dyck-type dy) (lift-sub (π p)) ⟩
      < dyck-type dy [ lift-sub (lift-sub (π p)) ]ty >ty ∎
      where
        open Reasoning ty-setoid
π-Ty (⇓pk p) = π-Ty p


prune-Eq : {Γ : Ctx n}
         → (p : Peak dy)
         → Typing-Sub ⌊ dy ⌋d Γ σ
         → {t : Tm n}
         → {A : Ty n}
         → peak-term p [ σ ]tm
           ≃tm
           identity-term A t
         → σ ≈[ Γ ]s (σ //s p) ● π p
prune-Eq {Γ = Γ} (⇕pk dy) (TyExt {t = u} (TyExt {σ = σ} {t = s} σty sty) tty) {t} {A} q
  = Ext≈ (Ext≈ (reflexive≈s (sym≃s (id-right-unit σ))) l1) l2
  where
    ity : Typing-Tm Γ (identity-term A t) _
    ity = transport-typing tty q

    tty2 : Typing-Tm Γ t A
    tty2 = identity-to-term-Ty ity

    Aty2 : Typing-Ty Γ A
    Aty2 = identity-to-type-Ty ity

    lem : ((lift-tm (dyck-term dy) ─⟨ lift-ty (dyck-type dy) ⟩⟶ Var zero) [
             ⟨ σ , s ⟩ ]ty)
            ≈[ Γ ]ty (t ─⟨ A ⟩⟶ t)
    lem = Ty-unique-≃ q tty (identity-term-Ty Aty2 tty2)

    l1 : s ≈[ Γ ]tm
           (dyck-term dy [ σ ]tm)
    l1 = begin
      s
        ≈⟨ tgt-eq lem  ⟩
      t
        ≈˘⟨ src-eq lem ⟩
      lift-tm (dyck-term dy) [ ⟨ σ , s ⟩ ]tm
        ≈⟨ reflexive≈tm (lift-sub-comp-lem-tm σ (dyck-term dy)) ⟩
      dyck-term dy [ σ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    l2 : u ≈[ Γ ]tm (identity-term (dyck-type dy) (dyck-term dy) [ σ ]tm)
    l2 = begin
      u
        ≈⟨ reflexive≈tm q ⟩
      identity-term A t
        ≈⟨ identity-term-≈ (trans≈ty (sym≈ty (base-eq lem)) (reflexive≈ty (lift-sub-comp-lem-ty σ (dyck-type dy))))
                           (trans≈tm (sym≈tm (src-eq lem)) (reflexive≈tm (lift-sub-comp-lem-tm σ (dyck-term dy))))  ⟩
      identity-term (dyck-type dy [ σ ]ty) (dyck-term dy [ σ ]tm)
        ≈˘⟨ reflexive≈tm (identity-term-sub (dyck-type dy) (dyck-term dy) σ) ⟩
      identity-term (dyck-type dy) (dyck-term dy) [ σ ]tm ∎

      where
        open Reasoning (tm-setoid-≈ Γ)

prune-Eq (⇑pk {dy = dy} p) (TyExt (TyExt {Δ = Δ} {σ = σ} σty sty) tty) {t} {A} q = Ext≈ (Ext≈ lem refl≈tm) refl≈tm
  where
    l4 : peak-term p [ σ ]tm ≃tm identity-term A t
    l4 = begin
      < peak-term p [ σ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm σ (peak-term p) ⟩
      < lift-tm (peak-term p) [ ⟨ σ , _ ⟩ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm ⟨ σ , _ ⟩ (lift-tm (peak-term p)) ⟩
      < lift-tm (lift-tm (peak-term p)) [ ⟨ ⟨ σ , _ ⟩ , _ ⟩ ]tm >tm
        ≈⟨ q ⟩
      < identity-term A t >tm ∎
      where
        open Reasoning tm-setoid

    lem : σ ≈[ Δ ]s  ⟨ ⟨ σ //s p , _ ⟩ , _ ⟩ ● lift-sub (lift-sub (π p))
    lem = begin
      < σ >s′
        ≈⟨ prune-Eq p σty l4 ⟩
      < (σ //s p) ● π p >s′
        ≈˘⟨ reflexive≈s (lift-sub-comp-lem-sub (σ //s p) (π p)) ⟩
      < ⟨ σ //s p , _ ⟩ ● lift-sub (π p) >s′
        ≈˘⟨ reflexive≈s (lift-sub-comp-lem-sub ⟨ σ //s p , _ ⟩ (lift-sub (π p))) ⟩
      < ⟨ ⟨ σ //s p , _ ⟩ , _ ⟩ ● lift-sub (lift-sub (π p)) >s′ ∎
      where
        open Reasoning (sub-setoid-≈ _)

prune-Eq (⇓pk p) σty q = prune-Eq p σty q

prune-sub-Ty : {Γ : Ctx n}
             → (p : Peak dy)
             → Typing-Sub ⌊ dy ⌋d Γ σ
             → {t : Tm n}
             → {A : Ty n}
             → peak-term p [ σ ]tm
               ≃tm
               identity-term A t → Typing-Sub ⌊ _ // p ⌋d Γ (σ //s p)
prune-sub-Ty (⇕pk dy) (TyExt (TyExt σty sty) tty) q = σty
prune-sub-Ty (⇑pk {dy = dy} p) (TyExt (TyExt {Δ = Δ} {σ = σ} σty sty) tty) {t} {A} q
  = TyExt (TyExt (prune-sub-Ty p σty l4) (TyConv sty l1)) (TyConv tty (Arr≈ l2 l3 refl≈tm))
  where
    l4 : peak-term p [ σ ]tm ≃tm identity-term A t
    l4 = begin
      < peak-term p [ σ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm σ (peak-term p) ⟩
      < lift-tm (peak-term p) [ ⟨ σ , _ ⟩ ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm ⟨ σ , _ ⟩ (lift-tm (peak-term p)) ⟩
      < lift-tm (lift-tm (peak-term p)) [ ⟨ ⟨ σ , _ ⟩ , _ ⟩ ]tm >tm
        ≈⟨ q ⟩
      < identity-term A t >tm ∎
      where
        open Reasoning tm-setoid

    l1 : (dyck-type dy [ σ ]ty) ≈[ Δ ]ty
           (dyck-type (dy // p) [ σ //s p ]ty)
    l1 = begin
      dyck-type dy [ σ ]ty
        ≈⟨ apply-sub-eq-ty (dyck-type dy) (prune-Eq p σty l4) ⟩
      dyck-type dy [ (σ //s p) ● π p ]ty
        ≈⟨ reflexive≈ty (assoc-ty (σ //s p) (π p) (dyck-type dy)) ⟩
      dyck-type dy [ π p ]ty [ σ //s p ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (dyck-type-prune p) refl≃s) ⟩
      dyck-type (dy // p) [ σ //s p ]ty ∎
      where
        open Reasoning (ty-setoid-≈ Δ)

    l2 : (lift-tm (dyck-term dy) [ ⟨ σ , _ ⟩ ]tm) ≈[ Δ ]tm
           (lift-tm (dyck-term (dy // p)) [ ⟨ σ //s p , _ ⟩ ]tm)
    l2 = begin
      lift-tm (dyck-term dy) [ ⟨ σ , _ ⟩ ]tm
        ≈⟨ reflexive≈tm (lift-sub-comp-lem-tm σ (dyck-term dy)) ⟩
      dyck-term dy [ σ ]tm
        ≈⟨ apply-sub-eq-tm (dyck-term dy) (prune-Eq p σty l4) ⟩
      dyck-term dy [ (σ //s p) ● π p ]tm
        ≈⟨ reflexive≈tm (assoc-tm (σ //s p) (π p) (dyck-term dy)) ⟩
      dyck-term dy [ π p ]tm [ σ //s p ]tm
        ≈˘⟨ reflexive≈tm (sub-action-≃-tm (dyck-term-prune p) refl≃s) ⟩
      dyck-term (dy // p) [ σ //s p ]tm
        ≈˘⟨ reflexive≈tm (lift-sub-comp-lem-tm (σ //s p) (dyck-term (dy // p))) ⟩
      lift-tm (dyck-term (dy // p)) [ ⟨ σ //s p , _ ⟩ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Δ)

    l3 : (lift-ty (dyck-type dy) [ ⟨ σ , _ ⟩ ]ty) ≈[ Δ ]ty
           (lift-ty (dyck-type (dy // p)) [ ⟨ σ //s p , _ ⟩ ]ty)
    l3 = begin
      lift-ty (dyck-type dy) [ ⟨ σ , _ ⟩ ]ty
        ≈⟨ reflexive≈ty (lift-sub-comp-lem-ty σ (dyck-type dy)) ⟩
      dyck-type dy [ σ ]ty
        ≈⟨ l1 ⟩
      dyck-type (dy // p) [ σ //s p ]ty
        ≈˘⟨ reflexive≈ty (lift-sub-comp-lem-ty (σ //s p) (dyck-type (dy // p))) ⟩
      lift-ty (dyck-type (dy // p)) [ ⟨ σ //s p , _ ⟩ ]ty ∎
      where
        open Reasoning (ty-setoid-≈ Δ)

prune-sub-Ty (⇓pk p) σty q = prune-sub-Ty p σty q
