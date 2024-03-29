open import Catt.Typing.Rule

module Catt.Dyck.Pruning.Typing (ops : Op)
                                (standard-op : StandardOp ops)
                                (rules : RuleSet)
                                (wk-cond : WkCond rules)
                                (sub-cond : SubCond ops rules) where

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

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Weakening ops rules wk-cond
open import Catt.Typing.Properties.Substitution ops rules sub-cond
open import Catt.Globular.Typing ops rules
open import Catt.Discs.Typing ops standard-op rules wk-cond
open import Catt.Dyck.Typing ops rules wk-cond sub-cond

π-Ty : (p : Peak dy) → Typing-Sub ⌊ dy ⌋d ⌊ _ // p ⌋d (π p)
π-Ty (⇕pk dy)
  = TyExt (TyExt id-Ty
                 (TyConv (dyck-term-Ty dy) (reflexive≈ty (sym≃ty (id-on-ty (dyck-type dy))))))
          (TyConv (identity-term-Ty (dyck-type-Ty dy) (dyck-term-Ty dy))
                           (reflexive≈ty (sym≃ty (Arr≃ (trans≃tm (apply-sub-wk-tm-≃ (dyck-term dy) ⟨ idSub , dyck-term dy ⟩)
                                                                 (id-on-tm (dyck-term dy)))
                                                       (trans≃ty (apply-sub-wk-ty-≃ (dyck-type dy) ⟨ idSub , dyck-term dy ⟩)
                                                                 (id-on-ty (dyck-type dy)))
                                                       refl≃tm))))
π-Ty (⇑pk {dy = dy} p)
  = TyExt (TyExt (wk-sub-typing (wk-sub-typing (π-Ty p)))
                 (TyConv (TyVar (suc zero)) (reflexive≈ty l1)))
          (TyConv (TyVar zero)
                  (reflexive≈ty (trans≃ty (dyck-type-prune (⇑pk p))
                                          (Arr≃ (apply-sub-wk-tm-≃ (wk-tm (dyck-term dy)) (π (⇑pk p)))
                                                (apply-sub-wk-ty-≃ (wk-ty (dyck-type dy)) (π (⇑pk p)))
                                                refl≃tm))))
  where
    l1 : wk-ty (wk-ty (dyck-type (dy // p))) ≃ty
           (dyck-type dy [ wk-sub (wk-sub (π p)) ]ty)
    l1 = begin
      < wk-ty (wk-ty (dyck-type (dy // p))) >ty
        ≈⟨ wk-ty-≃ (wk-ty-≃ (dyck-type-prune p)) ⟩
      < wk-ty (wk-ty (dyck-type dy [ π p ]ty)) >ty
        ≈˘⟨ wk-ty-≃ (apply-wk-sub-ty-≃ (dyck-type dy) (π p)) ⟩
      < wk-ty (dyck-type dy [ wk-sub (π p) ]ty) >ty
        ≈˘⟨ apply-wk-sub-ty-≃ (dyck-type dy) (wk-sub (π p)) ⟩
      < dyck-type dy [ wk-sub (wk-sub (π p)) ]ty >ty ∎
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
         → σ ≈[ Γ ]s π p ● (σ //s p)
prune-Eq {Γ = Γ} (⇕pk dy) (TyExt {t = u} (TyExt {σ = σ} {t = s} σty sty) tty) {t} {A} q
  = Ext≈ (Ext≈ (reflexive≈s (sym≃s (id-left-unit σ))) l1) l2
  where
    ity : Typing-Tm Γ (identity-term A t) _
    ity = transport-typing tty q

    tty2 : Typing-Tm Γ t A
    tty2 = identity-to-term-Ty ity

    Aty2 : Typing-Ty Γ A
    Aty2 = identity-to-type-Ty ity

    lem : ((wk-tm (dyck-term dy) ─⟨ wk-ty (dyck-type dy) ⟩⟶ Var zero) [
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
      wk-tm (dyck-term dy) [ ⟨ σ , s ⟩ ]tm
        ≈⟨ reflexive≈tm (apply-sub-wk-tm-≃ (dyck-term dy) ⟨ σ , s ⟩) ⟩
      dyck-term dy [ σ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Γ)

    l2 : u ≈[ Γ ]tm (identity-term (dyck-type dy) (dyck-term dy) [ σ ]tm)
    l2 = begin
      u
        ≈⟨ reflexive≈tm q ⟩
      identity-term A t
        ≈⟨ identity-term-≈ (trans≈ty (sym≈ty (base-eq lem)) (reflexive≈ty (apply-sub-wk-ty-≃ (dyck-type dy) ⟨ σ , s ⟩)))
                           (trans≈tm (sym≈tm (src-eq lem)) (reflexive≈tm (apply-sub-wk-tm-≃ (dyck-term dy) ⟨ σ , s ⟩)))  ⟩
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
        ≈˘⟨ apply-sub-wk-tm-≃ (peak-term p) ⟨ σ , _ ⟩ ⟩
      < wk-tm (peak-term p) [ ⟨ σ , _ ⟩ ]tm >tm
        ≈˘⟨ apply-sub-wk-tm-≃ (wk-tm (peak-term p)) ⟨ ⟨ σ , _ ⟩ , _ ⟩ ⟩
      < wk-tm (wk-tm (peak-term p)) [ ⟨ ⟨ σ , _ ⟩ , _ ⟩ ]tm >tm
        ≈⟨ q ⟩
      < identity-term A t >tm ∎
      where
        open Reasoning tm-setoid

    lem : σ ≈[ Δ ]s wk-sub (wk-sub (π p)) ● ⟨ ⟨ σ //s p , _ ⟩ , _ ⟩
    lem = begin
      < σ >s′
        ≈⟨ prune-Eq p σty l4 ⟩
      < π p ● (σ //s p) >s′
        ≈˘⟨ reflexive≈s (apply-sub-wk-sub-≃ (π p) ⟨ σ //s p , _ ⟩) ⟩
      < wk-sub (π p) ● ⟨ σ //s p , _ ⟩ >s′
        ≈˘⟨ reflexive≈s (apply-sub-wk-sub-≃ (wk-sub (π p)) ⟨ ⟨ σ //s p , _ ⟩ , _ ⟩) ⟩
      < wk-sub (wk-sub (π p)) ● ⟨ ⟨ σ //s p , _ ⟩ , _ ⟩ >s′ ∎
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
               identity-term A t
             → Typing-Sub ⌊ _ // p ⌋d Γ (σ //s p)
prune-sub-Ty (⇕pk dy) (TyExt (TyExt σty sty) tty) q = σty
prune-sub-Ty (⇑pk {dy = dy} p) (TyExt (TyExt {Δ = Δ} {σ = σ} σty sty) tty) {t} {A} q
  = TyExt (TyExt (prune-sub-Ty p σty l4) (TyConv sty l1)) (TyConv tty (Arr≈ l2 l3 refl≈tm))
  where
    l4 : peak-term p [ σ ]tm ≃tm identity-term A t
    l4 = begin
      < peak-term p [ σ ]tm >tm
        ≈˘⟨ apply-sub-wk-tm-≃ (peak-term p) ⟨ σ , _ ⟩ ⟩
      < wk-tm (peak-term p) [ ⟨ σ , _ ⟩ ]tm >tm
        ≈˘⟨ apply-sub-wk-tm-≃ (wk-tm (peak-term p)) ⟨ ⟨ σ , _ ⟩ , _ ⟩ ⟩
      < wk-tm (wk-tm (peak-term p)) [ ⟨ ⟨ σ , _ ⟩ , _ ⟩ ]tm >tm
        ≈⟨ q ⟩
      < identity-term A t >tm ∎
      where
        open Reasoning tm-setoid

    l1 : (dyck-type dy [ σ ]ty) ≈[ Δ ]ty
           (dyck-type (dy // p) [ σ //s p ]ty)
    l1 = begin
      dyck-type dy [ σ ]ty
        ≈⟨ apply-sub-eq-ty (dyck-type dy) (prune-Eq p σty l4) ⟩
      dyck-type dy [ π p ● (σ //s p) ]ty
        ≈⟨ reflexive≈ty (assoc-ty (π p) (σ //s p) (dyck-type dy)) ⟩
      dyck-type dy [ π p ]ty [ σ //s p ]ty
        ≈˘⟨ reflexive≈ty (sub-action-≃-ty (dyck-type-prune p) refl≃s) ⟩
      dyck-type (dy // p) [ σ //s p ]ty ∎
      where
        open Reasoning (ty-setoid-≈ Δ)

    l2 : (wk-tm (dyck-term dy) [ ⟨ σ , _ ⟩ ]tm) ≈[ Δ ]tm
           (wk-tm (dyck-term (dy // p)) [ ⟨ σ //s p , _ ⟩ ]tm)
    l2 = begin
      wk-tm (dyck-term dy) [ ⟨ σ , _ ⟩ ]tm
        ≈⟨ reflexive≈tm (apply-sub-wk-tm-≃ (dyck-term dy) ⟨ σ , _ ⟩) ⟩
      dyck-term dy [ σ ]tm
        ≈⟨ apply-sub-eq-tm (dyck-term dy) (prune-Eq p σty l4) ⟩
      dyck-term dy [ π p ● (σ //s p) ]tm
        ≈⟨ reflexive≈tm (assoc-tm (π p) (σ //s p) (dyck-term dy)) ⟩
      dyck-term dy [ π p ]tm [ σ //s p ]tm
        ≈˘⟨ reflexive≈tm (sub-action-≃-tm (dyck-term-prune p) refl≃s) ⟩
      dyck-term (dy // p) [ σ //s p ]tm
        ≈˘⟨ reflexive≈tm (apply-sub-wk-tm-≃ (dyck-term (dy // p)) ⟨ σ //s p , _ ⟩) ⟩
      wk-tm (dyck-term (dy // p)) [ ⟨ σ //s p , _ ⟩ ]tm ∎
      where
        open Reasoning (tm-setoid-≈ Δ)

    l3 : (wk-ty (dyck-type dy) [ ⟨ σ , _ ⟩ ]ty) ≈[ Δ ]ty
           (wk-ty (dyck-type (dy // p)) [ ⟨ σ //s p , _ ⟩ ]ty)
    l3 = begin
      wk-ty (dyck-type dy) [ ⟨ σ , _ ⟩ ]ty
        ≈⟨ reflexive≈ty (apply-sub-wk-ty-≃ (dyck-type dy) ⟨ σ , _ ⟩) ⟩
      dyck-type dy [ σ ]ty
        ≈⟨ l1 ⟩
      dyck-type (dy // p) [ σ //s p ]ty
        ≈˘⟨ reflexive≈ty (apply-sub-wk-ty-≃ (dyck-type (dy // p)) ⟨ σ //s p , _ ⟩) ⟩
      wk-ty (dyck-type (dy // p)) [ ⟨ σ //s p , _ ⟩ ]ty ∎
      where
        open Reasoning (ty-setoid-≈ Δ)

prune-sub-Ty (⇓pk p) σty q = prune-sub-Ty p σty q
