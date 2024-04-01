module Catt.Tree.Insertion.Support where

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

open ≡-Reasoning

open import Catt.Ops.All

open import Catt.Typing.Weak All

open import Catt.Tree.Boundary.Typing All Weak-Rules (weak-tame all-tame)
open import Catt.Tree.Structured.Typing All Weak-Rules
open import Catt.Tree.Structured.Typing.Properties All Weak-Rules (weak-tame all-tame)
open import Catt.Tree.Insertion.Typing All Weak-Rules (weak-tame all-tame)
open import Catt.Typing.Structured.Support All Weak-Rules (weak-tame all-tame) weak-supp

κ-full : (S : Tree n)
       → (P : Branch S d)
       → (T : Tree m)
       → .⦃ _ : has-trunk-height d T ⦄
       → SuppLabel (incTree (S >>[ P ] T)) (κ S P T) ≡ full
κ-full (Join S₁ S₂) BHere T
  = label-between-++t-full (replace-label (standard-label (Susp S₁) T) SHere)
                           SPath
                           (reflexive≈stm (standard-label-last (Susp S₁) T))
                           refl≈stm
                           lem
                           (id-label-full S₂)
  where
    lem : SuppLabel (incTree T) (replace-label (standard-label (Susp S₁) T) SHere) ≡ full
    lem = begin
      SuppLabel (incTree T) (replace-label (standard-label (Susp S₁) T) SHere)
        ≡⟨ replace-label-supp (standard-label (Susp S₁) T) SHere
                              (reflexive≈stm (sym≃stm (standard-label-fst (Susp S₁) T))) ⟩
      SuppSTm (incTree T) SHere ∪ SuppLabel (incTree T) (standard-label (Susp S₁) T)
        ≡⟨ cong (SuppSTm (incTree T) SHere ∪_) (standard-label-full (Susp S₁) T) ⟩
      SuppSTm (incTree T) SHere ∪ full
        ≡⟨ ∪-right-zero (trueAt (fromℕ _)) ⟩
      full ∎
κ-full (Join S₁ S₂) (BExt P) (Susp T) = label-between-joins-full (κ S₁ P T)
                                                                 (id-label S₂)
                                                                 (κ-full S₁ P T)
                                                                 (id-label-full S₂)
κ-full (Join S₁ S₂) (BShift P) T = label-between-joins-full (id-label S₁)
                                                            (κ S₂ P T)
                                                            (id-label-full S₁)
                                                            (κ-full S₂ P T)
