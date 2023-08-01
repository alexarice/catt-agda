module Catt.Typing.Weak where

open import Catt.Prelude
open import Catt.Typing.Base

Weak-Rules : ⊥ → Rule
Weak-Rules ()

open import Catt.Typing Weak-Rules public

open import Catt.Typing.Rule Weak-Rules

weak-lift-rule : (x : ⊥) → LiftRule (Weak-Rules x)
weak-lift-rule ()

weak-susp-rule : (x : ⊥) → SuspRule (Weak-Rules x)
weak-susp-rule ()

weak-sub-rule : (x : ⊥) → SubRule (Weak-Rules x)
weak-sub-rule ()

weak-conv-rule : (x : ⊥) → ConvRule (Weak-Rules x)
weak-conv-rule ()

weak-supp-rule : (x : ⊥) → SupportRule (Weak-Rules x)
weak-supp-rule ()
