{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Dyck.Pruning where

open import Catt.Syntax
open import Data.Nat
open import Catt.Dyck
open import Catt.Tree.Unbiased
open import Catt.Globular

prune-peak : {dy : Dyck (2 + n) d} → Peak dy → Dyck n d
prune-peak (⇕pk d) = d
prune-peak (⇑pk p) = ⇑ (prune-peak p)
prune-peak (⇓pk p) = ⇓ (prune-peak p)

prune-project : {dy : Dyck (2 + n) d} → Peak dy → Sub (3 + n) (1 + n) ⋆
prune-project (⇕pk dy) = ⟨ ⟨ (idSub (suc _)) , dyck-term dy ⟩ , identity (dyck-term dy) (dyck-type dy) ⟩
prune-project (⇑pk p) = ⟨ ⟨ (liftSub (liftSub (prune-project p))) , 1V ⟩ , 0V ⟩
prune-project (⇓pk p) = prune-project p

_//_ : {dy : Dyck (2 + n) d} → Sub (3 + n) m ⋆ → Peak dy → Sub (1 + n) m ⋆
⟨ ⟨ σ , s ⟩ , t ⟩ // ⇕pk dy = σ
⟨ ⟨ σ , s ⟩ , t ⟩ // ⇑pk p = ⟨ ⟨ (σ // p) , s ⟩ , t ⟩
⟨ ⟨ σ , s ⟩ , t ⟩ // ⇓pk p = ⟨ ⟨ σ , s ⟩ , t ⟩ // p
