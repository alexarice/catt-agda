module Catt.Typing.Insertion.Base where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Insertion
open import Catt.Typing.Rule

open Rule

Insertion : (Γ : Ctx m)
          → (S : Tree n)
          → (As : STy (someTree S))
          → (L : Label (Other m) S)
          → (P : Branch S l)
          → (T : Tree n′)
          → .⦃ _ : has-trunk-height l T ⦄
          → (M : Label (Other m) T)
          → Rule
Insertion Γ S As L P T M .len = _
Insertion Γ S As L P T M .tgtCtx = Γ
Insertion Γ S As L P T M .lhs = stm-to-term (SCoh S As (L ,, S⋆))
Insertion Γ S As L P T M .rhs
  = stm-to-term (SCoh (insertion-tree S P T)
                      (As >>=′ (κ S P T ,, S⋆))
                      (label-from-insertion S P T L M ,, S⋆))
