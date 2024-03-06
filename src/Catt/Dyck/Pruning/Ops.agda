open import Catt.Typing.Base

module Catt.Dyck.Pruning.Ops (ops : Op) where

open import Catt.Prelude
open import Catt.Dyck
open import Catt.Dyck.Pasting
open import Catt.Dyck.Pruning
open import Catt.Support

PruningOp : Set
PruningOp = ∀ {n} (dy : Dyck (suc n) 0)
                → (pk : Peak dy)
                → (xs : VarSet (3 + (n * 2)))
                → (ys : VarSet (3 + (n * 2)))
                → ops ⌊ dy ⌋d ⦃ dyck-to-pd dy ⦄ xs ys
                → ops ⌊ dy // pk ⌋d ⦃ dyck-to-pd (dy // pk) ⦄
                      (TransportVarSet xs (π pk))
                      (TransportVarSet ys (π pk))
