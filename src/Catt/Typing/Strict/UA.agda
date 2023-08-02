module Catt.Typing.Strict.UA where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Discs
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Insertion
open import Catt.Typing.Base

import Catt.Typing.Insertion.Base

data Index : Set where
  DR : .⦃ NonZero n ⦄ → (Γ : Ctx m) → (σ : Sub (disc-size n) m ⋆) → Index
  ECR : (Γ : Ctx m) → (Δ : Ctx (suc n)) → (s : Tm (suc n)) → (A : Ty (suc n)) → (σ : Sub (suc n) m ⋆) → Index
  Insert : (Γ : Ctx m)
         → (X : MaybeTree m)
         → (S : Tree n)
         → (As : STy (someTree S))
         → (L : Label X S)
         → (P : BranchingPoint S l)
         → (T : Tree n′)
         → .⦃ _ : has-linear-height l T ⦄
         → (M : Label X T)
         → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆)
         → Catt.Typing.Insertion.Base.IsCompOrIdent (height-of-branching P) T
         → Index

module _ where
  open import Catt.Typing.DiscRemoval.Base
  open import Catt.Typing.EndoCoherenceRemoval.Base
  open Catt.Typing.Insertion.Base

  SUA-Rules : Index → Rule
  SUA-Rules (DR Γ σ) = DiscRemoval Γ σ
  SUA-Rules (ECR Γ Δ s A σ) = EndoCoherenceRemoval Γ Δ s A σ
  SUA-Rules (Insert Γ X S As L P T M pf p) = Insertion Γ X S As L P T M

open import Catt.Typing SUA-Rules public
open import Catt.Typing.DiscRemoval SUA-Rules as D
open import Catt.Typing.EndoCoherenceRemoval SUA-Rules as E
open import Catt.Typing.Insertion SUA-Rules as I

hasDiscRemoval : HasDiscRemoval
hasDiscRemoval tty = Rule≈ (DR _ _) tty

hasEndoCoherenceRemoval : HasEndoCoherenceRemoval
hasEndoCoherenceRemoval tty = Rule≈ (ECR _ _ _ _ _) tty

hasInsertion : HasSUAInsertion
hasInsertion P pf p [ tty ] = ?
