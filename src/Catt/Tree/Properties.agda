{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Tree
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Variables
open import Catt.Variables.Properties
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false; not)
open import Data.Fin using (Fin; zero; suc; fromℕ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Catt.Globular
open import Catt.Globular.Properties
open import Data.Product renaming (_,_ to _,,_)

connect-tree-to-ctx : (S : Tree n) → (T : Tree m)
                    → tree-to-ctx (connect-tree S T) ≃c connect (tree-to-ctx S) (tree-last-var S) (tree-to-ctx T)
connect-tree-to-ctx Sing T = sym≃c (connect-left-unit (tree-to-ctx T)) -- sym≃c (connect-pdb-left-unit (tree-to-ctx T))
connect-tree-to-ctx (Join S₁ S₂) T = begin
  < tree-to-ctx (connect-tree (Join S₁ S₂) T) >c ≡⟨⟩
  < connect-susp (tree-to-ctx S₁) (tree-to-ctx (connect-tree S₂ T)) >c
    ≈⟨ connect-≃ refl≃c refl≃tm (connect-tree-to-ctx S₂ T) ⟩
  < connect-susp (tree-to-ctx S₁) (connect (tree-to-ctx S₂) (tree-last-var S₂) (tree-to-ctx T))
    >c
    ≈˘⟨ connect-susp-assoc (tree-to-ctx S₁) (tree-to-ctx S₂) (tree-last-var S₂) (tree-to-ctx T) ⟩
  < connect (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
            (tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
            (tree-to-ctx T) >c ∎
  where
    open Reasoning ctx-setoid

tree-last-var-is-var : (T : Tree n) → isVar (tree-last-var T)
tree-last-var-is-var Sing = tt
tree-last-var-is-var (Join S T) = var-to-var-comp-tm (tree-last-var T) ⦃ tree-last-var-is-var T ⦄ (connect-susp-inc-right (tree-size S) (tree-size T)) ⦃ connect-susp-inc-right-var-to-var (tree-size S) (tree-size T) ⦄

tree-inc-preserve-fst-var : (d : ℕ) → (T : Tree n) → (b : Bool) → Var (fromℕ _) [ tree-inc (suc d) T b ]tm ≃tm Var {suc (tree-size T)} (fromℕ _)
tree-inc-preserve-fst-var d Sing b = refl≃tm
tree-inc-preserve-fst-var d (Join S T) b = sub-between-connect-susps-fst-var (tree-inc d S b) (tree-inc (suc d) T b)

tree-inc-preserve-last-var : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-last-var (tree-bd (suc d) T) [ tree-inc (suc d) T b ]tm ≃tm tree-last-var T
tree-inc-preserve-last-var d Sing b = refl≃tm
tree-inc-preserve-last-var d (Join S T) b = begin
  < tree-last-var (tree-bd (suc d) T)
    [ connect-susp-inc-right (tree-bd-len d S) (tree-bd-len (suc d) T) ]tm
    [ sub-between-connect-susps (tree-inc d S b)
                                (tree-inc (suc d) T b) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (tree-last-var (tree-bd (suc d) T)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ sub-between-connect-susps (tree-inc d S b)
                                (tree-inc (suc d) T b)
      ∘ connect-susp-inc-right (tree-bd-len d S) (tree-bd-len (suc d) T) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var (tree-bd (suc d) T)})
       (sub-between-connect-susps-inc-right (tree-inc d S b)
                                            (tree-inc (suc d) T b)
                                            (tree-inc-preserve-fst-var d T b)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ connect-susp-inc-right (tree-size S) (tree-size T) ∘ tree-inc (suc d) T b ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var (tree-bd (suc d) T)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ tree-inc (suc d) T b ]tm
    [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm
    ≈⟨ sub-action-≃-tm (tree-inc-preserve-last-var d T b) refl≃s ⟩
  < tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm ∎
  where
    open Reasoning tm-setoid

tree-bd-glob : (d₁ d₂ : ℕ) → (T : Tree n) → d₁ < d₂ → tree-bd d₁ (tree-bd d₂ T) ≃ tree-bd d₁ T
tree-bd-glob zero d₂ T p = Sing≃
tree-bd-glob (suc d₁) (suc d₂) Sing p = Sing≃
tree-bd-glob (suc d₁) (suc d₂) (Join S T) p = Join≃ (tree-bd-glob d₁ d₂ S (≤-pred p)) (tree-bd-glob (suc d₁) (suc d₂) T p)

tree-inc-glob : (d₁ d₂ : ℕ) → (T : Tree n) → (b₁ b₂ : Bool) → d₁ < d₂ → tree-inc d₂ T b₂ ∘ tree-inc d₁ (tree-bd d₂ T) b₁ ≃s tree-inc d₁ T b₁
tree-inc-glob zero (suc d₂) T false b₂ p = Ext≃ refl≃s (tree-inc-preserve-fst-var d₂ T b₂)
tree-inc-glob zero (suc d₂) T true b₂ p = Ext≃ refl≃s (tree-inc-preserve-last-var d₂ T b₂)
tree-inc-glob (suc d₁) (suc d₂) Sing b₁ b₂ p = refl≃s
tree-inc-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ p = begin
  < sub-between-connect-susps (tree-inc d₂ S b₂) (tree-inc (suc d₂) T b₂)
    ∘ sub-between-connect-susps (tree-inc d₁ (tree-bd d₂ S) b₁) (tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁) >s
    ≈⟨ sub-between-connect-susps-comp (tree-inc d₁ (tree-bd d₂ S) b₁) (tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁) (tree-inc d₂ S b₂) (tree-inc (suc d₂) T b₂) (tree-inc-preserve-fst-var d₂ T b₂) ⟩
  < sub-between-connect-susps
    (tree-inc d₂ S b₂ ∘ tree-inc d₁ (tree-bd d₂ S) b₁)
    (tree-inc (suc d₂) T b₂ ∘ tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁)
    >s
    ≈⟨ sub-between-connect-susps-≃ (tree-inc d₂ S b₂ ∘ tree-inc d₁ (tree-bd d₂ S) b₁)
                                   (tree-inc d₁ S b₁)
                                   (tree-inc (suc d₂) T b₂ ∘ tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁)
                                   (tree-inc (suc d₁) T b₁)
                                   (≃-to-same-n (tree-bd-glob d₁ d₂ S (≤-pred p)))
                                   (≃-to-same-n (tree-bd-glob (suc d₁) (suc d₂) T p))
                                   (tree-inc-glob d₁ d₂ S b₁ b₂ (≤-pred p))
                                   (tree-inc-glob (suc d₁) (suc d₂) T b₁ b₂ p) ⟩
  < sub-between-connect-susps (tree-inc d₁ S b₁)
      (tree-inc (suc d₁) T b₁) >s ∎
  where
    open Reasoning sub-setoid

tree-inc-glob-step : (d : ℕ) → (T : Tree n) (b₁ b₂ : Bool) → tree-inc (suc d) T b₁ ∘ tree-inc d (tree-bd (suc d) T) b₂ ≃s tree-inc (suc d) T (not b₁) ∘ tree-inc d (tree-bd (suc d) T) b₂
tree-inc-glob-step d T b₁ b₂ = begin
  < tree-inc (suc d) T b₁ ∘ tree-inc d (tree-bd (suc d) T) b₂ >s
    ≈⟨ tree-inc-glob d (suc d) T b₂ b₁ (s≤s ≤-refl) ⟩
  < tree-inc d T b₂ >s
    ≈˘⟨ tree-inc-glob d (suc d) T b₂ (not b₁) (s≤s ≤-refl)  ⟩
  < tree-inc (suc d) T (not b₁) ∘ tree-inc d (tree-bd (suc d) T) b₂
    >s ∎
  where
    open Reasoning sub-setoid

tree-dim-bd : (d : ℕ) → (T : Tree n) → tree-dim (tree-bd d T) ≡ d ⊓ tree-dim T
tree-dim-bd zero T = refl
tree-dim-bd (suc d) Sing = refl
tree-dim-bd (suc d) (Join S T) = trans (cong₂ _⊔_ (cong suc (tree-dim-bd d S)) (tree-dim-bd (suc d) T)) (sym (⊓-distribˡ-⊔ (suc d) (suc (tree-dim S)) (tree-dim T)))

tree-dim-bd′ : (d : ℕ) → (T : Tree n) → d ≤ tree-dim T → tree-dim (tree-bd d T) ≡ d
tree-dim-bd′ d T p = trans (tree-dim-bd d T) (m≤n⇒m⊓n≡m p)

join-tree-has-non-zero-dim : (S : Tree n) → (T : Tree m) → ¬ (zero ≡ tree-dim (Join S T))
join-tree-has-non-zero-dim S T p with ≤-trans (m≤m⊔n (suc (tree-dim S)) (tree-dim T)) (≤-reflexive (sym p))
... | ()

tree-inc-susp-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → suspSub (tree-inc d T b) ≃s tree-inc (suc d) (suspTree T) b
tree-inc-susp-lem zero T false = sym≃s (id-left-unit ⟨ ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩ , suspTm (Var (fromℕ _)) ⟩)
tree-inc-susp-lem zero T true = sym≃s (id-left-unit ⟨ ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩ , suspTm (tree-last-var T) ⟩)
tree-inc-susp-lem (suc d) Sing b = refl≃s
tree-inc-susp-lem (suc d) (Join S T) b = sym≃s (id-left-unit _)

linear-tree-dim : (S : Tree n) → .⦃ is-linear S ⦄ → tm-height (tree-to-ctx S) 0V ≡ tree-dim S
linear-tree-dim Sing = refl
linear-tree-dim (Join S Sing) = trans (susp-tm-height 0V (tree-to-ctx S)) (cong suc (linear-tree-dim S))

connect-tree-dim : (S : Tree n) → (T : Tree m) → tree-dim (connect-tree S T) ≡ tree-dim S ⊔ tree-dim T
connect-tree-dim Sing T = refl
connect-tree-dim (Join S₁ S₂) T = trans (cong (suc (tree-dim S₁) ⊔_) (connect-tree-dim S₂ T)) (sym (⊔-assoc (suc (tree-dim S₁)) (tree-dim S₂) (tree-dim T)))

connect-tree-length-lem : (S : Tree n) → (T : Tree m) → connect-tree-length S T ≡ tree-size T + tree-size S
connect-tree-length-lem Sing T = sym (+-identityʳ _)
connect-tree-length-lem (Join S₁ S₂) T = trans (cong (_+ (2 + tree-size S₁)) (connect-tree-length-lem S₂ T)) (+-assoc (tree-size T) (tree-size S₂) (2 + tree-size S₁))

connect-tree-last-var : (S : Tree n) → (T : Tree m) → tree-last-var (connect-tree S T) ≃tm tree-last-var T [ idSub≃ (sym≃c (connect-tree-to-ctx S T)) ∘ (connect-inc-right (tree-last-var S) (tree-size T)) ]tm
connect-tree-last-var Sing T = sym≃tm (trans≃tm (sub-action-≃-tm (refl≃tm {s = tree-last-var T}) lem) (id-on-tm (tree-last-var (connect-tree Sing T))))
  where
    lem : idSub≃ (sym≃c (sym≃c (connect-left-unit (tree-to-ctx T)))) ∘ connect-inc-right (Var zero) (tree-size T) ≃s idSub (suc (tree-size T))
    lem = begin
      < idSub≃ (sym≃c (sym≃c (connect-left-unit (tree-to-ctx T))))
        ∘ connect-inc-right (Var zero) (tree-size T) >s
        ≈⟨ idSub≃-on-sub (sym≃c (sym≃c (connect-left-unit (tree-to-ctx T)))) (connect-inc-right (Var zero) _) ⟩
      < connect-inc-right (Var zero) _ >s
        ≈⟨ connect-inc-right-left-unit _ ⟩
      < idSub (suc _) >s ∎
      where
        open Reasoning sub-setoid
connect-tree-last-var (Join S₁ S₂) T = begin
  < tree-last-var (connect-tree S₂ T) [
       connect-susp-inc-right (tree-size S₁)
       (tree-size (connect-tree S₂ T))
       ]tm >tm
    ≈⟨ sub-action-≃-tm (connect-tree-last-var S₂ T) refl≃s ⟩
  < tree-last-var T
    [ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T))
      ∘ connect-inc-right (tree-last-var S₂) (tree-size T) ]tm
    [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (tree-last-var T) ⟩
  < tree-last-var T
    [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
    ∘ (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ∘
      connect-inc-right (tree-last-var S₂) (tree-size T)) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var T}) lem ⟩
  < tree-last-var T
    [ idSub≃ (sym≃c (connect-tree-to-ctx (Join S₁ S₂) T))
      ∘ connect-inc-right (tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm) (tree-size T) ]tm >tm ∎
  where
    l2 : (connect-susp-inc-right (tree-size S₁)
            (tree-size (connect-tree S₂ T))
            ∘ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)))
           ≃s connect-inc-right getSnd (tree-size T + tree-size S₂)
    l2 = begin
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ∘ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) >s
        ≈⟨ idSub≃-right-unit (sym≃c (connect-tree-to-ctx S₂ T)) (connect-susp-inc-right (tree-size S₁)
                                                                  (tree-size (connect-tree S₂ T))) ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) >s
        ≈⟨ connect-inc-right-≃ refl refl≃tm (connect-tree-length-lem S₂ T) ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size T + tree-size S₂) >s ∎
      where
        open Reasoning sub-setoid

    lem : (connect-susp-inc-right (tree-size S₁)
             (tree-size (connect-tree S₂ T))
             ∘
             (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ∘
              connect-inc-right (tree-last-var S₂) (tree-size T)))
            ≃s
            (idSub≃ (sym≃c (connect-tree-to-ctx (Join S₁ S₂) T)) ∘
             connect-inc-right
             (tree-last-var S₂ [
              connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
             (tree-size T))
    lem = begin
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ∘ (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ∘ connect-inc-right (tree-last-var S₂) (tree-size T)) >s
        ≈˘⟨ ∘-assoc _ _ _ ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ∘ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T))
        ∘ connect-inc-right (tree-last-var S₂) (tree-size T) >s
        ≈⟨ sub-action-≃-sub refl≃s l2 ⟩
      < connect-inc-right getSnd (tree-size T + tree-size S₂)
        ∘ connect-inc-right (tree-last-var S₂) (tree-size T) >s
        ≈˘⟨ connect-inc-right-assoc getSnd (tree-last-var S₂) (tree-size T) ⟩
      < connect-inc-right (tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
        (tree-size T) >s
        ≈˘⟨ idSub≃-on-sub (sym≃c (connect-tree-to-ctx (Join S₁ S₂) T)) _ ⟩
      <
        idSub≃ (sym≃c (connect-tree-to-ctx (Join S₁ S₂) T)) ∘
        connect-inc-right
        (tree-last-var S₂ [
         connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
        (tree-size T)
        >s ∎
      where
        open Reasoning sub-setoid

    open Reasoning tm-setoid

tree-to-ctx-glob : (S : Tree n) → ctx-is-globular (tree-to-ctx S)
tree-to-ctx-glob Sing = tt ,, tt
tree-to-ctx-glob (Join S T) = connect-susp-glob (tree-to-ctx S) ⦃ tree-to-ctx-glob S ⦄ (tree-to-ctx T) ⦃ tree-to-ctx-glob T ⦄