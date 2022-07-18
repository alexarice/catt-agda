module Catt.Tree.Label.Support where

open import Catt.Prelude
open import Catt.Tree.Label
open import Catt.Tree.Path
open import Catt.Support
open import Catt.Suspension.Support
open import Catt.Connection.Support
open import Catt.Tree.Support
open import Catt.Tree
open import Catt.Syntax

FVSTm : {X : MaybeTree n} → STm X → VarSet n
FVLabel : {X : MaybeTree n} → Label X S → VarSet n
FVSTy : {X : MaybeTree n} → STy X → VarSet n

FVSTm (SExt a) = connect-supp (suspSupp (FVSTm a)) empty
FVSTm (SShift a) = {!connect-supp empty (FVSTm )!}
FVSTm (SPath x) = {!!}
FVSTm (SCoh S A L) = {!!}
FVSTm (SOther t) = {!!}

FVLabel {S = Sing} L = FVSTm (L PHere)
FVLabel {S = Join S T} L = FVSTm (L PHere) ∪ FVLabel (L ∘ PExt) ∪ FVLabel (L ∘ PShift)

FVSTy As = {!!}

label-to-sub-FV : (L : Label-WT X S) → FVSub (label-to-sub L) ≡ FVSTy (lty L) ∪ FVLabel (ap L)
label-to-sub-FV {S = Sing} L = {!!}
label-to-sub-FV {S = Join S₁ S₂} L = {!!}
