open import Catt.Typing.Rule
open import Catt.Ops.Pruning

module Catt.Typing.Strict.Units (ops : Op) (tameOp : TameOp ops) (pruning-op : PruningOp ops) where

open import Catt.Prelude
open import Catt.Syntax

open import Catt.Typing.DiscRemoval.Rule
open import Catt.Typing.EndoCoherenceRemoval.Rule
open import Catt.Typing.Pruning.Rule

Unit-Rules : RuleSet
Unit-Rules = DiscRemovalSet ∪r ECRSet ∪r PruningSet

open import Catt.Typing ops Unit-Rules
open import Catt.Typing.DiscRemoval ops Unit-Rules
open import Catt.Typing.EndoCoherenceRemoval ops Unit-Rules
open import Catt.Typing.Pruning ops Unit-Rules

hasDiscRemovalRule : HasDiscRemovalRule
hasDiscRemovalRule = ⊆r-∪-1

hasDiscRemoval : HasDiscRemoval
hasDiscRemoval = dr-from-rule hasDiscRemovalRule

hasEndoCoherenceRemovalRule : HasEndoCoherenceRemovalRule
hasEndoCoherenceRemovalRule = ⊆r-trans ⊆r-∪-1 ⊆r-∪-2

hasEndoCoherenceRemoval : HasEndoCoherenceRemoval
hasEndoCoherenceRemoval = ecr-from-rule hasEndoCoherenceRemovalRule

hasPruningRule : HasPruningRule
hasPruningRule = ⊆r-trans ⊆r-∪-2 ⊆r-∪-2

hasPruning : HasPruning
hasPruning = pruning-from-rule hasPruningRule

units-wk : WkCond Unit-Rules
units-wk = WkCond-∪ dr-wk (WkCond-∪ ecr-wk pruning-wk)

units-susp : SuspCond Unit-Rules
units-susp = SuspCond-∪ dr-susp (SuspCond-∪ ecr-susp pruning-susp)

units-sub : SubCond ops Unit-Rules
units-sub = SubCond-∪ ops dr-sub (SubCond-∪ ops ecr-sub pruning-sub)

units-tame : Tame ops Unit-Rules
units-tame .Tame.tame-op = tameOp
units-tame .Tame.wk-cond = units-wk
units-tame .Tame.susp-cond = units-susp
units-tame .Tame.sub-cond = units-sub

open TameOp tameOp

open import Catt.Typing.DiscRemoval.Typed ops standard-op Unit-Rules units-wk
open import Catt.Typing.EndoCoherenceRemoval.Typed ops standard-op Unit-Rules units-wk units-sub
open import Catt.Typing.Pruning.Typed ops standard-op pruning-op Unit-Rules units-wk units-sub

units-pres : PresCond ops Unit-Rules
units-pres = PresCond-∪ ops dr-pres (PresCond-∪ ops ecr-pres pruning-pres)

module _ where
  open import Catt.Support.Typing ops Unit-Rules
  open import Catt.Typing.DiscRemoval.Support ops standard-op rulesWithSupp (rulesWithSupp-wk units-wk) rulesWithSupp-supp
  open import Catt.Typing.EndoCoherenceRemoval.Support ops standard-op rulesWithSupp rulesWithSupp-supp
  open import Catt.Typing.Pruning.Support ops standard-op
                                          rulesWithSupp
                                          (rulesWithSupp-wk units-wk)
                                          (rulesWithSupp-sub units-sub)
                                          rulesWithSupp-supp

  units-supp′ : SupportCond′ ops rulesWithSupp Unit-Rules
  units-supp′ = SupportCond-∪ ops dr-supp (SupportCond-∪ ops ecr-supp pruning-supp)

  units-supp : SupportCond ops Unit-Rules
  units-supp = SupportCond-prop units-supp′
