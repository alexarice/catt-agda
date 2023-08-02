module Catt.Typing.Strict.Units where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Discs
open import Catt.Dyck
open import Catt.Typing.Base

data Index : Set where
  DR : .⦃ NonZero n ⦄ → (Γ : Ctx m) → (σ : Sub (disc-size n) m ⋆) → Index
  ECR : (Γ : Ctx m) → (Δ : Ctx (suc n)) → (s : Tm (suc n)) → (A : Ty (suc n)) → (σ : Sub (suc n) m ⋆) → Index
  Prune : (Γ : Ctx m)
        → (dy : Dyck (suc n) 0)
        → (A : Ty (3 + n * 2))
        → (p : Peak dy)
        → (σ : Sub (3 + n * 2) m ⋆)
        → (B : Ty m)
        → (t : Tm m)
        → (peak-term p [ σ ]tm ≃tm identity-term B t)
        → Index

module _ where
  open import Catt.Typing.DiscRemoval.Base
  open import Catt.Typing.EndoCoherenceRemoval.Base
  open import Catt.Typing.Pruning.Base

  Unit-Rules : Index → Rule
  Unit-Rules (DR Γ σ) = DiscRemoval Γ σ
  Unit-Rules (ECR Γ Δ s A σ) = EndoCoherenceRemoval Γ Δ s A σ
  Unit-Rules (Prune Γ dy A p σ B t pf) = Pruning Γ dy A p σ

open import Catt.Typing Unit-Rules public
open import Catt.Typing.DiscRemoval Unit-Rules as D
open import Catt.Typing.EndoCoherenceRemoval Unit-Rules as E
open import Catt.Typing.Pruning Unit-Rules as P

open import Catt.Typing.Rule Unit-Rules

hasDiscRemoval : HasDiscRemoval
hasDiscRemoval tty = Rule≈ (DR _ _) tty

hasEndoCoherenceRemoval : HasEndoCoherenceRemoval
hasEndoCoherenceRemoval tty = Rule≈ (ECR _ _ _ _ _) tty

hasPruning : HasPruning
hasPruning p pf tty = Rule≈ (Prune _ _ _ p _ _ _ pf) tty

units-lift-rule : (i : Index) → LiftRule (Unit-Rules i)
units-lift-rule (DR Γ σ) = lift-rule
  where
    open D.Conditions hasDiscRemoval
units-lift-rule (ECR Γ Δ s A σ) = lift-rule
  where
    open E.Conditions hasEndoCoherenceRemoval
units-lift-rule (Prune Γ dy A p σ B t pf) = lift-rule p pf
  where
    open P.Conditions hasPruning

units-susp-rule : (i : Index) → SuspRule (Unit-Rules i)
units-susp-rule (DR Γ σ) = susp-rule
  where
    open D.Conditions hasDiscRemoval
units-susp-rule (ECR Γ Δ s A σ) = susp-rule
  where
    open E.Conditions hasEndoCoherenceRemoval
units-susp-rule (Prune Γ dy A p σ B t pf) = susp-rule p pf
  where
    open P.Conditions hasPruning

units-sub-rule : (i : Index) → SubRule (Unit-Rules i)
units-sub-rule (DR Γ σ) = sub-rule
  where
    open D.Conditions hasDiscRemoval
units-sub-rule (ECR Γ Δ s A σ) = sub-rule
  where
    open E.Conditions hasEndoCoherenceRemoval
units-sub-rule (Prune Γ dy A p σ B t pf) = sub-rule p pf
  where
    open P.Conditions hasPruning
