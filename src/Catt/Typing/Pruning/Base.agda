module Catt.Typing.Pruning.Base where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Discs
open import Catt.Dyck
open import Catt.Dyck.Pruning
open import Catt.Typing.Rule

open Rule

Pruning : (Γ : Ctx m)
        → (dy : Dyck (suc n) 0)
        → (A : Ty (3 + n * 2))
        → (p : Peak dy)
        → (σ : Sub (3 + n * 2) m ⋆)
        → Rule
Pruning Γ dy A p σ .len = _
Pruning Γ dy A p σ .tgtCtx = Γ
Pruning Γ dy A p σ .lhs = Coh ⌊ dy ⌋d A σ
Pruning Γ dy A p σ .rhs = Coh ⌊ prune-peak p ⌋d (A [ prune-project p ]ty) (prune-sub p σ)
