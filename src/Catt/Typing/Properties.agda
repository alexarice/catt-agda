open import Catt.Typing.Rule

module Catt.Typing.Properties (ops : Op)
                              (rules : RuleSet)
                              (tame : Tame ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Globular
open import Catt.Suspension

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Base ops rules public
open import Catt.Typing.Properties.Lifting ops rules lift-cond public
open import Catt.Typing.Properties.Substitution.Suspended ops rules tame public
