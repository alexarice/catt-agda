open import Catt.Typing.Rule

module Catt.Typing.Weak (ops : Op) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Properties

Weak-Rules : RuleSet
Weak-Rules r = ⊥

open import Catt.Typing ops Weak-Rules

weak-wk : WkCond Weak-Rules
weak-wk A ()

weak-susp : SuspCond Weak-Rules
weak-susp ()

weak-sub : SubCond ops Weak-Rules
weak-sub Γ σ ()

open Tame

weak-tame : (tame : TameOp ops) → Tame ops Weak-Rules
weak-tame tame .tame-op = tame
weak-tame tame .wk-cond = weak-wk
weak-tame tame .susp-cond = weak-susp
weak-tame tame .sub-cond = weak-sub

weak-conv : ConvCond ops Weak-Rules
weak-conv ()

weak-supp : SupportCond ops Weak-Rules
weak-supp ()

weak-eq-is-refl-tm : s ≈[ Γ ]tm t → s ≃tm t
weak-eq-is-refl-sub : σ ≈[ Γ ]s τ → σ ≃s τ
weak-eq-is-refl-ty : A ≈[ Γ ]ty B → A ≃ty B

weak-eq-is-refl-tm (Var≈ p) = Var≃ refl p
weak-eq-is-refl-tm (Sym≈ p) = sym≃tm (weak-eq-is-refl-tm p)
weak-eq-is-refl-tm (Trans≈ p q) = trans≃tm (weak-eq-is-refl-tm p) (weak-eq-is-refl-tm q)
weak-eq-is-refl-tm (Coh≈ p q) = Coh≃ refl≃c (weak-eq-is-refl-ty p) (weak-eq-is-refl-sub q)

weak-eq-is-refl-sub (Null≈ x) = Null≃ (weak-eq-is-refl-ty x)
weak-eq-is-refl-sub (Ext≈ p x) = Ext≃ (weak-eq-is-refl-sub p) (weak-eq-is-refl-tm x)

weak-eq-is-refl-ty Star≈ = Star≃ refl
weak-eq-is-refl-ty (Arr≈ x p y) = Arr≃ (weak-eq-is-refl-tm x)
                                       (weak-eq-is-refl-ty p)
                                       (weak-eq-is-refl-tm y)

weak-⊆ : (r : RuleSet) → Weak-Rules ⊆r r
weak-⊆ r ()
