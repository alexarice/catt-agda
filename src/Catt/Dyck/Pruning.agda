{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Dyck.Pruning where

open import Catt.Syntax
open import Data.Nat
open import Catt.Dyck
open import Catt.Tree.Unbiased
open import Catt.Globular

prune-peak : {dy : Dyck (suc n) d} → Peak dy → Dyck n d
prune-peak (⇕pk d) = d
prune-peak (⇑pk p) = ⇑ (prune-peak p)
prune-peak (⇓pk p) = ⇓ (prune-peak p)

prune-project : {dy : Dyck (suc n) d} → Peak dy → Sub (3 + n * 2) (1 + n * 2) ⋆
prune-project (⇕pk dy) = ⟨ ⟨ idSub , dyck-term dy ⟩ , identity (dyck-term dy) (dyck-type dy) ⟩
prune-project (⇑pk p) = ⟨ ⟨ (liftSub (liftSub (prune-project p))) , 1V ⟩ , 0V ⟩
prune-project (⇓pk p) = prune-project p

prune-sub : {dy : Dyck (suc n) d} → Peak dy → Sub (3 + n * 2) m ⋆ → Sub (1 + n * 2) m ⋆
prune-sub (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ = σ
prune-sub (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ = ⟨ ⟨ (prune-sub p σ) , s ⟩ , t ⟩
prune-sub (⇓pk p) σ = prune-sub p σ
