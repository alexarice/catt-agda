module Catt.Typing.Pruning.Base where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
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
        → (B : Ty m)
        → (t : Tm m)
        → (peak-term p [ σ ]tm ≃tm identity-term B t)
        → Rule
Pruning Γ dy A p σ B t pf .len = _
Pruning Γ dy A p σ B t pf .tgtCtx = Γ
Pruning Γ dy A p σ B t pf .lhs = Coh (dyck-to-ctx dy) A σ
Pruning Γ dy A p σ B t pf .rhs = Coh (dyck-to-ctx (prune-peak p)) (A [ prune-project p ]ty) (prune-sub p σ)
