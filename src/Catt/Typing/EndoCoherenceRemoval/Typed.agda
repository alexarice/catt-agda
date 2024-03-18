open import Catt.Typing.Rule

module Catt.Typing.EndoCoherenceRemoval.Typed (ops : Op)
                                              (standard-op : StandardOp ops)
                                              (rules : RuleSet)
                                              (wk-cond : WkCond rules)
                                              (sub-cond : SubCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Discs.Properties

open import Catt.Typing.EndoCoherenceRemoval.Rule

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Substitution ops rules sub-cond
open import Catt.Globular.Typing ops rules
open import Catt.Discs.Typing ops standard-op rules wk-cond

ecr-pres : PresCond′ ops rules ECRSet
ecr-pres [ ECR Γ Δ s sfull A σ ] {A = B} tty
  = TyConv (identity-Ty (ty-dim A) (sub-from-disc-Ty (ty-dim A)
                                                     (apply-sub-ty-typing A_ty σty)
                                                     (sym (sub-dim σ A))
                                                     (apply-sub-tm-typing s_ty σty)))
           lem
  where
    σty : Typing-Sub Δ Γ σ
    σty = coh-sub-ty tty

    s_ty : Typing-Tm Δ s A
    s_ty = ty-src-Ty (coh-ty-ty tty)

    A_ty : Typing-Ty Δ A
    A_ty = ty-base-Ty (coh-ty-ty tty)

    l2 : wk-ty (sphere-type (ty-dim A))
           [ ⟨ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ , s [ σ ]tm ⟩ ]ty
         ≃ty
         A [ σ ]ty
    l2 = begin
      < wk-ty (sphere-type (ty-dim A)) [ ⟨ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ , s [ σ ]tm ⟩ ]ty >ty
        ≈⟨ apply-sub-wk-ty-≃ (sphere-type (ty-dim A)) ⟨ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ , s [ σ ]tm ⟩ ⟩
      < sphere-type (ty-dim A) [ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ ]ty >ty
        ≈⟨ sub-from-sphere-prop (ty-dim A) (A [ σ ]ty) (sym (sub-dim σ A)) ⟩
      < A [ σ ]ty >ty ∎
      where
        open Reasoning ty-setoid

    lem : (Var 0F ─⟨ wk-ty (sphere-type (ty-dim A)) ⟩⟶ Var 0F)
            [ sub-from-disc (ty-dim A) (A [ σ ]ty) _ (s [ σ ]tm) ]ty
          ≈[ Γ ]ty
          B
    lem = begin
      (s [ σ ]tm) ─⟨ wk-ty (sphere-type (ty-dim A)) [ ⟨ sub-from-sphere (ty-dim A) (A [ σ ]ty) _ , s [ σ ]tm ⟩ ]ty ⟩⟶ (s [ σ ]tm)
        ≈⟨ Arr≈ refl≈tm (reflexive≈ty l2) refl≈tm ⟩
      (s [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ (s [ σ ]tm)
        ≈⟨ tm-to-ty-prop tty ⟩
      B ∎
      where
        open Reasoning (ty-setoid-≈ Γ)
