module Catt.Typing.Insertion.Base where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Label
open import Catt.Tree.Insertion
open import Catt.Typing.Rule

open Rule

Insertion : (Γ : Ctx m)
          → (S : Tree n)
          → (As : STy (someTree S))
          → (L : Label (Other m) S)
          → (P : BranchingPoint S l)
          → (T : Tree n′)
          → .⦃ _ : has-linear-height l T ⦄
          → (M : Label (Other m) T)
          → Rule
Insertion Γ S As L P T M .len = _
Insertion Γ S As L P T M .tgtCtx = Γ
Insertion Γ S As L P T M .lhs = stm-to-term (SCoh S As (L ,, S⋆))
Insertion Γ S As L P T M .rhs
  = stm-to-term (SCoh (insertion-tree S P T)
                      (label-on-sty As (exterior-sub-label S P T ,, S⋆))
                      (sub-from-insertion-label S P T L M ,, S⋆))

data IsCompOrIdent {m} (n : ℕ) (T : Tree m) : Set where
  IsComp : n ≡ tree-dim T → IsCompOrIdent n T
  IsIdent : T ≃ n-disc (pred n) → IsCompOrIdent n T
