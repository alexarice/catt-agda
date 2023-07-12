module Catt.Typing.Weak where

open import Catt.Prelude
open import Catt.Typing.Base

Weak-Rules : ⊥ → Rule
Weak-Rules ()

open import Catt.Typing Weak-Rules public

open import Catt.Typing.Rule Weak-Rules

weak-lift-rule : (x : ⊥) → LiftRule (Weak-Rules x)
weak-lift-rule ()
