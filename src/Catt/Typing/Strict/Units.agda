module Catt.Typing.Strict.Units where

open import Catt.Prelude
open import Catt.Syntax

open import Catt.Typing.Rule

open import Catt.Typing.DiscRemoval.Rule
open import Catt.Typing.EndoCoherenceRemoval.Rule
open import Catt.Typing.Pruning.Rule

Unit-Rules : RuleSet
Unit-Rules = DiscRemovalSet ∪r ECRSet ∪r PruningSet

open import Catt.Typing Unit-Rules public
open import Catt.Typing.DiscRemoval Unit-Rules
open import Catt.Typing.EndoCoherenceRemoval Unit-Rules
open import Catt.Typing.Pruning Unit-Rules

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

units-lift : LiftCond Unit-Rules
units-lift = LiftCond-∪ dr-lift (LiftCond-∪ ecr-lift pruning-lift)

units-susp : SuspCond Unit-Rules
units-susp = SuspCond-∪ dr-susp (SuspCond-∪ ecr-susp pruning-susp)

units-sub : SubCond Unit-Rules
units-sub = SubCond-∪ dr-sub (SubCond-∪ ecr-sub pruning-sub)

open Tame

units-tame : Tame Unit-Rules
units-tame .lift-cond = units-lift
units-tame .susp-cond = units-susp
units-tame .sub-cond = units-sub

open import Catt.Typing.DiscRemoval.Typed Unit-Rules units-lift
open import Catt.Typing.EndoCoherenceRemoval.Typed Unit-Rules units-lift units-sub
open import Catt.Typing.Pruning.Typed Unit-Rules units-lift units-sub

units-conv : ConvCond Unit-Rules
units-conv = ConvCond-∪ dr-conv (ConvCond-∪ ecr-conv pruning-conv)
