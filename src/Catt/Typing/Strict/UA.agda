module Catt.Typing.Strict.UA where

open import Catt.Prelude
open import Catt.Syntax

open import Catt.Typing.Rule

open import Catt.Typing.DiscRemoval.Rule
open import Catt.Typing.EndoCoherenceRemoval.Rule
open import Catt.Typing.Insertion.Rule

SUA-Rules : RuleSet
SUA-Rules = DiscRemovalSet ∪r ECRSet ∪r InsertionSet

open import Catt.Typing SUA-Rules public
open import Catt.Typing.DiscRemoval SUA-Rules
open import Catt.Typing.EndoCoherenceRemoval SUA-Rules
open import Catt.Typing.Insertion SUA-Rules

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

sua-sub : SubCond SUA-Rules
sua-sub = SubCond-∪ dr-sub (SubCond-∪ ecr-sub ins-sub)

open Tame

sua-tame : Tame SUA-Rules
sua-tame .lift-cond = sua-lift
sua-tame .susp-cond = sua-susp
sua-tame .sub-cond = sua-sub

open import Catt.Typing.DiscRemoval.Typed SUA-Rules sua-lift
open import Catt.Typing.EndoCoherenceRemoval.Typed SUA-Rules sua-lift sua-sub
open import Catt.Typing.Insertion.Typed SUA-Rules sua-tame

sua-conv : ConvCond SUA-Rules
sua-conv = ConvCond-∪ dr-conv (ConvCond-∪ ecr-conv ins-conv)
