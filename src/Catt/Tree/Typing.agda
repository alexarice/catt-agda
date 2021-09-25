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
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Properties
open import Data.Bool using (Bool; true; false)

fst-var-Ty : (Γ : Ctx (suc n)) → Typing-Tm Γ (Var (fromℕ _)) ⋆
fst-var-Ty (∅ , A) = TyVarZ (reflexive≈ty (lift-ty-≃ (⋆-is-only-ty-in-empty-context A)))
fst-var-Ty (Γ , B , A) = lift-tm-typing (fst-var-Ty (Γ , B))

tree-last-var-Ty : (T : Tree n) → Typing-Tm (tree-to-ctx T) (tree-last-var T) ⋆
tree-last-var-Ty Sing = TyVarZ refl≈ty
tree-last-var-Ty (Join S T) = apply-sub-tm-typing (tree-last-var-Ty T) (connect-susp-inc-right-Ty (tree-to-ctx S) (tree-to-ctx T))

tree-inc-Ty : (d : ℕ) → (T : Tree n) → (b : Bool) → Typing-Sub (tree-to-ctx (tree-bd d T)) (tree-to-ctx T) (tree-inc d T b)
tree-inc-Ty zero T false = TyExt (TyNull TyStar) (fst-var-Ty (tree-to-ctx T))
tree-inc-Ty zero T true = TyExt (TyNull TyStar) (tree-last-var-Ty T)
tree-inc-Ty (suc d) Sing b = id-Ty
tree-inc-Ty (suc d) (Join S T) b = sub-between-connect-susps-Ty (tree-inc-Ty d S b) (tree-inc-Ty (suc d) T b) (reflexive≈tm (tree-inc-preserve-fst-var d T b))
