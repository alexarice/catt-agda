module Catt.Tree.Insertion.Boundary.Support where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Boundary

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Construct.Support
open import Catt.Tree.Standard.Support

open import Catt.Ops.All

open import Catt.Typing.Strict.UA All all-tame all-insertion-op

open import Catt.Tree.Boundary.Typing All SUA-Rules sua-tame
open import Catt.Tree.Structured.Typing All SUA-Rules
open import Catt.Tree.Structured.Typing.Properties All SUA-Rules sua-tame
open import Catt.Tree.Insertion.Typing All SUA-Rules sua-tame
open import Catt.Typing.Structured.Support All SUA-Rules sua-tame sua-supp
open import Catt.Typing.Insertion.Equality All SUA-Rules sua-tame

open ≡-Reasoning

κ-boundary-vs : (S : Tree n)
              → (P : Branch S d)
              → (T : Tree m)
              → .⦃ _ : has-trunk-height d T ⦄
              → (q : lh P ≥ tree-dim T)
              → (d : ℕ)
              → (b : Bool)
              → tree-bd-vs d S b [ κ S P T ]vl ≡ tree-bd-vs d (S >>[ P ] T) b
κ-boundary-vs S P T q d b = begin
  tree-bd-vs d S b [ κ S P T ]vl
    ≡˘⟨ cong (_[ κ S P T ]vl) (supp-standard-lem d S b) ⟩
  SuppSTm (incTree S) (standard-stm d (tree-bd d S) >>= tree-inc-label d S b) [ κ S P T ]vl
    ≡˘⟨ vs-label-STm (incTree (S >>[ P ] T))
                    (standard-stm d (tree-bd d S) >>= tree-inc-label d S b)
                    (κ S P T)
                    (κ-Ty S P T q) ⟩
  SuppSTm (incTree (S >>[ P ] T)) (standard-stm d (tree-bd d S) >>= tree-inc-label d S b >>= (κ S P T ,, S⋆))
    ≡⟨ SuppSTm-≃ (incTree (S >>[ P ] T))
                 (>>=-assoc (standard-stm d (tree-bd d S)) (tree-inc-label d S b) (κ S P T ,, S⋆)) ⟩
  SuppSTm (incTree (S >>[ P ] T)) (standard-stm d (tree-bd d S) >>= tree-inc-label d S b ●lt (κ S P T ,, S⋆))
    ≡⟨ EqSuppSTm (κ-standard-lem hasDiscRemoval hasInsertion S P T d q b) ⟩
  SuppSTm (incTree (S >>[ P ] T)) (standard-stm d (tree-bd d (S >>[ P ] T)) >>= tree-inc-label d (S >>[ P ] T) b)
    ≡⟨ supp-standard-lem d (S >>[ P ] T) b ⟩
  tree-bd-vs d (S >>[ P ] T) b ∎
