open import Catt.Typing.Rule
open import Catt.Tree.Insertion.Ops

module Catt.Typing.Strict.UA (ops : Op) (tameOp : TameOp ops) (ins-op : InsertionSOp ops) where

open import Catt.Prelude
open import Catt.Syntax

open import Catt.Typing.DiscRemoval.Rule
open import Catt.Typing.EndoCoherenceRemoval.Rule
open import Catt.Typing.Insertion.Rule

SUA-Rules : RuleSet
SUA-Rules = DiscRemovalSet ∪r ECRSet ∪r InsertionSet

open import Catt.Typing ops SUA-Rules public
open import Catt.Typing.DiscRemoval ops SUA-Rules
open import Catt.Typing.EndoCoherenceRemoval ops SUA-Rules
open import Catt.Typing.Insertion ops SUA-Rules

hasDiscRemovalRule : HasDiscRemovalRule
hasDiscRemovalRule = ⊆r-∪-1

hasDiscRemoval : HasDiscRemoval
hasDiscRemoval = dr-from-rule hasDiscRemovalRule

hasEndoCoherenceRemovalRule : HasEndoCoherenceRemovalRule
hasEndoCoherenceRemovalRule = ⊆r-trans ⊆r-∪-1 ⊆r-∪-2

hasEndoCoherenceRemoval : HasEndoCoherenceRemoval
hasEndoCoherenceRemoval = ecr-from-rule hasEndoCoherenceRemovalRule

hasInsertionRule : HasInsertionRule
hasInsertionRule = ⊆r-trans ⊆r-∪-2 ⊆r-∪-2

hasInsertion : HasInsertion
hasInsertion = ins-from-rule hasInsertionRule

sua-lift : LiftCond SUA-Rules
sua-lift = LiftCond-∪ dr-lift (LiftCond-∪ ecr-lift ins-lift)

sua-susp : SuspCond SUA-Rules
sua-susp = SuspCond-∪ dr-susp (SuspCond-∪ ecr-susp ins-susp)

sua-sub : SubCond ops SUA-Rules
sua-sub = SubCond-∪ ops dr-sub (SubCond-∪ ops ecr-sub ins-sub)

sua-tame : Tame ops SUA-Rules
sua-tame .Tame.tame-op = tameOp
sua-tame .Tame.lift-cond = sua-lift
sua-tame .Tame.susp-cond = sua-susp
sua-tame .Tame.sub-cond = sua-sub

open TameOp tameOp

open import Catt.Typing.DiscRemoval.Typed ops standard-op SUA-Rules sua-lift
open import Catt.Typing.EndoCoherenceRemoval.Typed ops standard-op SUA-Rules sua-lift sua-sub
open import Catt.Typing.Insertion.Typed ops ins-op SUA-Rules sua-tame

sua-conv : ConvCond ops SUA-Rules
sua-conv = ConvCond-∪ ops dr-conv (ConvCond-∪ ops ecr-conv ins-conv)

module _ where
  open import Catt.Support.Typing ops SUA-Rules
  open import Catt.Typing.DiscRemoval.Support ops standard-op rulesWithSupp (rulesWithSupp-lift sua-lift) rulesWithSupp-supp
  open import Catt.Typing.EndoCoherenceRemoval.Support ops standard-op rulesWithSupp rulesWithSupp-supp
  open import Catt.Typing.Insertion.Support ops rulesWithSupp (rulesWithSupp-tame sua-tame) rulesWithSupp-supp

  sua-supp′ : SupportCond′ ops rulesWithSupp SUA-Rules
  sua-supp′ = SupportCond-∪ ops dr-supp (SupportCond-∪ ops ecr-supp ins-supp)

  sua-supp : SupportCond ops SUA-Rules
  sua-supp = SupportCond-prop sua-supp′
