module Catt.Typing.Strict.Units where

open import Catt.Prelude
open import Catt.Syntax

open import Catt.Typing.Rule

open import Catt.Typing.DiscRemoval.Rule
open import Catt.Typing.EndoCoherenceRemoval.Rule
open import Catt.Typing.Pruning.Rule

Unit-Rules : RuleSet
Unit-Rules = DiscRemovalSet ∪r ECRSet ∪r PruningSet

open import Catt.Typing.Rule.Typed Unit-Rules

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

units-tame : Tame Unit-Rules
units-tame = Tame-∪ dr-tame (Tame-∪ ecr-tame pruning-tame)

open Tame units-tame renaming (lift-cond to units-lift; susp-cond to units-susp; sub-cond to units-sub) public

open import Catt.Typing.DiscRemoval.Typed Unit-Rules units-lift
open import Catt.Typing.EndoCoherenceRemoval.Typed Unit-Rules units-lift units-sub
open import Catt.Typing.Pruning.Typed Unit-Rules units-lift units-sub

units-conv : ConvCond Unit-Rules
units-conv = ConvCond-∪ dr-conv (ConvCond-∪ ecr-conv pruning-conv)
