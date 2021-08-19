{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection.Properties where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Connection
open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles

-- connect left unit

connect-left-unit : (Γ : Ctx (suc n)) → connect (∅ , ⋆) 0V Γ ≃c Γ
connect-inc-right-left-unit : (Γ : Ctx (suc n)) → connect-inc-right (∅ , ⋆) 0V Γ ≃s idSub Γ

connect-left-unit (∅ , ⋆) = Add≃ Emp≃ Star≃
connect-left-unit (∅ , s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)
connect-left-unit (Γ , A , B) = Add≃ (connect-left-unit (Γ , A)) (trans≃ty (sub-action-≃-ty refl≃ty (connect-inc-right-left-unit (Γ , A))) (id-on-ty B))

connect-inc-right-left-unit (∅ , ⋆) = Ext≃ Null≃ (Var≃ refl)
connect-inc-right-left-unit (∅ , s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)
connect-inc-right-left-unit (Γ , A , B) = Ext≃ (lift-sub-≃ (connect-inc-right-left-unit (Γ , A))) (Var≃ refl)

connect-pdb-left-unit : (Γ : Ctx (suc n)) → connect-pdb Base Γ ≃c Γ
connect-pdb-left-unit Γ = connect-left-unit Γ

sub-from-connect-inc-left : (σ : Sub Γ Υ) → (t : Tm Γ 2) → (τ : Sub Δ Υ) → sub-from-connect σ t τ ∘ connect-inc-left Γ t Δ ≃s σ
sub-from-connect-inc-left σ t τ@(⟨ ⟨⟩ , s ⟩) = id-right-unit (sub-from-connect σ t τ)
sub-from-connect-inc-left σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = trans≃s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-left _ t (_ , _))) (sub-from-connect-inc-left σ t ⟨ τ , s ⟩)

sub-from-connect-pdb-inc-left : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub Γ Υ) → (τ : Sub Δ Υ) → sub-from-connect-pdb pdb σ τ ∘ connect-pdb-inc-left pdb Δ ≃s σ
sub-from-connect-pdb-inc-left pdb σ τ = sub-from-connect-inc-left σ (getFocusTerm pdb) τ

sub-from-connect-inc-right : (σ : Sub Γ Υ) → (t : Tm Γ 2) → (τ : Sub Δ Υ) → (t [ σ ]tm ≃tm Var (fromℕ _) [ τ ]tm) → sub-from-connect σ t τ ∘ connect-inc-right Γ t Δ ≃s τ
sub-from-connect-inc-right {Δ = ∅ , ⋆} σ t ⟨ ⟨⟩ , s ⟩ p = Ext≃ Null≃ p
sub-from-connect-inc-right {Δ = ∅ , s₁ ─⟨ A ⟩⟶ t₁} σ t ⟨ ⟨⟩ , s ⟩ p = ⊥-elim (no-term-in-empty-context s₁)
sub-from-connect-inc-right {Δ = Δ , A , B} σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≃ (trans≃s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-right _ t (Δ , A))) (sub-from-connect-inc-right σ t ⟨ τ , s ⟩ p)) refl≃tm

sub-from-connect-pdb-inc-right : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub Γ Υ) → (τ : Sub Δ Υ) → (getFocusTerm pdb [ σ ]tm ≃tm (Var (fromℕ _) [ τ ]tm)) → sub-from-connect-pdb pdb σ τ ∘ connect-pdb-inc-right pdb Δ ≃s τ
sub-from-connect-pdb-inc-right pdb σ τ p = sub-from-connect-inc-right σ (getFocusTerm pdb) τ p

connect-inc-fst-var : (Γ : Ctx (suc n)) → (t : Tm Γ 2) → (Δ : Ctx (suc m)) → t [ connect-inc-left Γ t Δ ]tm ≃tm Var (fromℕ _) [ connect-inc-right Γ t Δ ]tm
connect-inc-fst-var Γ t (∅ , ⋆) = id-on-tm t
connect-inc-fst-var Γ t (∅ , s ─⟨ A ⟩⟶ t₁) = ⊥-elim (no-term-in-empty-context s)
connect-inc-fst-var Γ t (Δ , A , B) = begin
  < t [ connect-inc-left Γ t (Δ , A , B) ]tm >tm ≈⟨ apply-lifted-sub-tm-≃ t (connect-inc-left Γ t (Δ , A)) ⟩
  < liftTerm (t [ connect-inc-left Γ t (Δ , A) ]tm) >tm ≈⟨ lift-tm-≃ (connect-inc-fst-var Γ t (Δ , A)) ⟩
  < liftTerm (Var (fromℕ _) [ connect-inc-right Γ t (Δ , A) ]tm) >tm ≈˘⟨ apply-lifted-sub-tm-≃ (Var (fromℕ _)) (connect-inc-right Γ t (Δ , A)) ⟩
  < Var (fromℕ (suc _)) [ connect-inc-right Γ t (Δ , A , B) ]tm >tm ∎
  where
    open Reasoning tm-setoid

connect-pdb-inc-fst-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → (getFocusTerm pdb) [ connect-pdb-inc-left pdb Δ ]tm ≃tm Var (fromℕ _) [ connect-pdb-inc-right pdb Δ ]tm
connect-pdb-inc-fst-var pdb Δ = connect-inc-fst-var _ (getFocusTerm pdb) Δ

connect-inc-left-fst-var : (Γ : Ctx (suc n)) → (t : Tm Γ 2) → (Δ : Ctx (suc m)) → Var (fromℕ _) [ connect-inc-left Γ t Δ ]tm ≃tm Var {Γ = connect Γ t Δ} (fromℕ _)
connect-inc-left-fst-var Γ t (∅ , A) = id-on-tm (Var (fromℕ _))
connect-inc-left-fst-var Γ t (Δ , A , B) = trans≃tm (apply-lifted-sub-tm-≃ (Var (fromℕ _)) (connect-inc-left Γ t (Δ , A))) (lift-tm-≃ (connect-inc-left-fst-var Γ t (Δ , A)))

connect-pdb-inc-left-fst-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → Var (fromℕ _) [ connect-pdb-inc-left pdb Δ ]tm ≃tm Var {Γ = connect-pdb pdb Δ } (fromℕ _)
connect-pdb-inc-left-fst-var pdb Δ = connect-inc-left-fst-var _ (getFocusTerm pdb) Δ

sub-from-connect-fst-var : (σ : Sub Γ Υ) → (t : Tm Γ 2) → (τ : Sub Δ Υ) → Var (fromℕ _) [ sub-from-connect σ t τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-fst-var σ t ⟨ ⟨⟩ , s ⟩ = refl≃tm
sub-from-connect-fst-var σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = sub-from-connect-fst-var σ t ⟨ τ , s ⟩

sub-from-connect-pdb-fst-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub Γ Υ) → (τ : Sub Δ Υ) → Var (fromℕ _) [ sub-from-connect-pdb pdb σ τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-pdb-fst-var pdb σ τ = sub-from-connect-fst-var σ (getFocusTerm pdb) τ
