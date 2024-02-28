open import Catt.Typing.Rule

module Catt.Typing.Properties (rules : RuleSet)
                              (tame : Tame rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Globular
open import Catt.Suspension

open import Catt.Typing rules
open import Catt.Typing.Properties.Base rules public
open import Catt.Typing.Properties.Lifting rules lift-cond public
open import Catt.Typing.Properties.Substitution.Suspended rules tame public
