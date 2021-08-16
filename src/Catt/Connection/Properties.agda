{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection.Properties where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Connection
open import Data.Nat
open import Data.Empty
open import Relation.Binary.PropositionalEquality

-- connect left unit

connect-left-unit : (Γ : Ctx (suc n)) → connect (∅ , ⋆) 0V Γ ≃c Γ
connect-inc-right-left-unit : (Γ : Ctx (suc n)) → connect-inc-right (∅ , ⋆) 0V Γ ≃s idSub Γ

connect-left-unit (∅ , ⋆) = Add≃ Emp≃ Star≃
connect-left-unit (∅ , s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)
connect-left-unit (Γ , A , B) = Add≃ (connect-left-unit (Γ , A)) (trans≃ty (sub-action-sub-≃-ty B (connect-inc-right-left-unit (Γ , A))) (id-on-ty B))

connect-inc-right-left-unit (∅ , ⋆) = Ext≃ Null≃ (Var≃ refl)
connect-inc-right-left-unit (∅ , s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)
connect-inc-right-left-unit (Γ , A , B) = Ext≃ (lift-sub-≃ (connect-inc-right-left-unit (Γ , A))) (Var≃ refl)

connect-pdb-left-unit : (Γ : Ctx (suc n)) → connect-pdb Base Γ ≃c Γ
connect-pdb-left-unit Γ = connect-left-unit Γ
