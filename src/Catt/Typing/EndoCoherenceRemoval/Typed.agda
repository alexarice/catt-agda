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
  = TyConv (identity-term-Ty (apply-sub-ty-typing A_ty σty)
                             (apply-sub-tm-typing s_ty σty))
           (tm-to-ty-prop tty)
  where
    σty : Typing-Sub Δ Γ σ
    σty = coh-sub-ty tty

    s_ty : Typing-Tm Δ s A
    s_ty = ty-src-Ty (coh-ty-ty tty)

    A_ty : Typing-Ty Δ A
    A_ty = ty-base-Ty (coh-ty-ty tty)
