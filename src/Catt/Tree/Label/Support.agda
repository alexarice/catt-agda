module Catt.Tree.Label.Support where

open import Catt.Prelude
open import Catt.Tree.Label
open import Catt.Tree.Path
open import Catt.Support
open import Catt.Tree
open import Catt.Syntax

FVLabel : {X : MaybeTree n} → Label X S A → VarSet n
FVLabel {S = Sing} L = FVTm (apt L PPHere)
FVLabel {S = Join S T} L = FVTm (apt L PPHere) ∪ FVLabel (label₁ L) ∪ FVLabel (label₂ L)

label-to-sub-FV : (L : Label X S A) → FVSub (label-to-sub L) ≡ FVTy A ∪ FVLabel L
label-to-sub-FV {S = Sing} L = refl
label-to-sub-FV {S = Join S₁ S₂} L = {!!}
