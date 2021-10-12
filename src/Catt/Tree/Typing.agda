{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Tree.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Connection.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing index rule lift-rule
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Properties
open import Data.Bool using (Bool; true; false)
open import Data.Empty
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Data.Unit using (tt)

tree-to-ctx-Ty : (T : Tree n) → Typing-Ctx (tree-to-ctx T)
tree-to-ctx-Ty Sing = TyAdd TyEmp TyStar
tree-to-ctx-Ty (Join S T) = connect-susp-Ty (tree-to-ctx-Ty S) (tree-to-ctx-Ty T)

fst-var-Ty : (Γ : Ctx (suc n)) → Typing-Tm Γ (Var (fromℕ _)) ⋆
fst-var-Ty (∅ , ⋆) = TyVarZ TyStar refl≈ty
fst-var-Ty (∅ , s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)
fst-var-Ty (Γ , B , A) = lift-tm-typing (fst-var-Ty (Γ , B))

tree-last-var-Ty : (T : Tree n) → Typing-Tm (tree-to-ctx T) (tree-last-var T) ⋆
tree-last-var-Ty Sing = TyVarZ TyStar refl≈ty
tree-last-var-Ty (Join S T) = apply-sub-tm-typing (tree-last-var-Ty T) (connect-susp-inc-right-Ty (tree-to-ctx S) (tree-to-ctx-Ty T))

tree-inc-Ty : (d : ℕ) → (T : Tree n) → (b : Bool) → Typing-Sub (tree-to-ctx (tree-bd d T)) (tree-to-ctx T) (tree-inc d T b)
tree-inc-Ty zero T false = TyExt (TyNull TyStar) TyStar (fst-var-Ty (tree-to-ctx T))
tree-inc-Ty zero T true = TyExt (TyNull TyStar) TyStar (tree-last-var-Ty T)
tree-inc-Ty (suc d) Sing b = id-Ty (TyAdd TyEmp TyStar)
tree-inc-Ty (suc d) (Join S T) b = sub-between-connect-susps-Ty (tree-inc-Ty d S b) (tree-inc-Ty (suc d) T b) (tree-to-ctx-Ty S) (tree-to-ctx-Ty T) (reflexive≈tm (tree-inc-preserve-fst-var d T b))

sub-from-linear-Eq : (T : Tree n) → .⦃ is-linear T ⦄ → Typing-Sub (tree-to-ctx T) Γ σ → Typing-Sub (tree-to-ctx T) Γ τ → 0V [ σ ]tm ≃tm 0V [ τ ]tm → σ ≈[ Γ ]s τ
sub-from-linear-Eq Sing (TyExt (TyNull Aty) x sty) (TyExt (TyNull Bty) x₃ tty) p = Ext≈ (Null≈ (Ty-unique-≃ p sty tty)) (reflexive≈tm p)
sub-from-linear-Eq {σ = σ} {τ = τ} (Join T Sing) σty τty p = begin
  < σ >s′
    ≈˘⟨ unrestrict-restrict-≈ σ refl≈tm refl≈tm ⟩
  < unrestrict (restrict σ (getFst [ σ ]tm) (getSnd [ σ ]tm)) >s′
    ≈⟨ unrestrictEq (sub-from-linear-Eq T (restrictTy σty
                                                      (tree-to-ctx-Ty T)
                                                      (apply-sub-tm-typing getFstTy σty)
                                                      (apply-sub-tm-typing getSndTy σty)
                                                      refl≈tm
                                                      refl≈tm)
                                          (restrictTy τty
                                                      (tree-to-ctx-Ty T)
                                                      (apply-sub-tm-typing getFstTy τty)
                                                      (apply-sub-tm-typing getSndTy τty)
                                                      refl≈tm
                                                      refl≈tm)
                                          lem) ⟩
  < unrestrict (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm)) >s′
    ≈⟨ unrestrict-restrict-≈ τ refl≈tm refl≈tm ⟩
  < τ >s′ ∎
  where
    lem : (Var zero [ restrict σ (getFst [ σ ]tm) (getSnd [ σ ]tm) ]tm) ≃tm
            (Var zero [ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm)
    lem = begin
      < Var zero [ restrict σ (getFst [ σ ]tm) (getSnd [ σ ]tm) ]tm >tm
        ≈˘⟨ restrict-susp 0V σ ⟩
      < 0V [ σ ]tm >tm
        ≈⟨ p ⟩
      < 0V [ τ ]tm >tm
        ≈⟨ restrict-susp 0V τ ⟩
      < Var zero [ restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm) ]tm >tm ∎
      where
        open Reasoning tm-setoid
    open Reasoning (sub-setoid-≈ _ _)
