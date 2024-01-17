module Catt.Typing.Strict.UA where

open import Catt.Prelude
open import Catt.Syntax

open import Catt.Typing.Rule

open import Catt.Typing.DiscRemoval.Rule
open import Catt.Typing.EndoCoherenceRemoval.Rule
open import Catt.Typing.Insertion.Rule

SUA-Rules : RuleSet
SUA-Rules = DiscRemovalSet ∪r ECRSet ∪r InsertionSet

open import Catt.Typing.Rule.Typed SUA-Rules

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

sua-tame : Tame SUA-Rules
sua-tame = Tame-∪ dr-tame (Tame-∪ ecr-tame ins-tame)

open Tame sua-tame renaming (lift-cond to sua-lift; susp-cond to sua-susp; sub-cond to sua-sub) public

open import Catt.Typing.DiscRemoval.Typed SUA-Rules sua-lift
open import Catt.Typing.EndoCoherenceRemoval.Typed SUA-Rules sua-lift sua-sub
open import Catt.Typing.Insertion.Typed SUA-Rules sua-tame

sua-conv : ConvCond SUA-Rules
sua-conv = ConvCond-∪ dr-conv (ConvCond-∪ ecr-conv ins-conv)
