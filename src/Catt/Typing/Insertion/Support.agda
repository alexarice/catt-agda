open import Catt.Typing.Rule

module Catt.Typing.Insertion.Support (rules : RuleSet)
                                     (tame : Tame rules)
                                     (supp-cond : SupportCond rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Wedge.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Structured.Typing rules
open import Catt.Tree.Structured.Typing.Properties rules tame
open import Catt.Tree.Boundary.Typing rules tame
open import Catt.Tree.Standard.Typing rules tame
open import Catt.Tree.Insertion.Typing rules tame
open import Catt.Typing.Insertion.Rule

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Wedge.Support
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Support.Properties
open import Catt.Tree.Boundary.Support
open import Catt.Tree.Standard.Support

open import Catt.Typing.Structured.Support rules tame supp-cond

κ-full : (S : Tree n)
       → (p : Branch S d)
       → (T : Tree m)
       → .⦃ _ : has-trunk-height d T ⦄
       → DCT (FVLabel (κ S p T)) ≡ tFull
κ-full (Join S₁ S₂) BHere T
  = label-between-++t-full
      (replace-label (standard-label (Susp S₁) T) SHere)
      SPath
      (reflexive≈stm (standard-label-last (Susp S₁) T))
      refl≈stm
      lem
      (trans (cong DCT (id-label-full S₂)) DCT-full)
  where
    open ≡-Reasoning

    lem : DCT (FVLabel (replace-label (standard-label (Susp S₁) T) SHere)) ≡ tFull
    lem = begin
      DCT (FVLabel (replace-label (standard-label (Susp S₁) T) SHere))
        ≡⟨ replace-label-supp (standard-label (Susp S₁) T) SHere (reflexive≈stm (sym≃stm (standard-label-fst (Susp S₁) T))) ⟩
      DCT (FVSTm SHere) ∪m DCT (FVLabel (standard-label (Susp S₁) T))
        ≡⟨ cong (DCT (FVSTm SHere) ∪m_) (standard-label-full (Susp S₁) T) ⟩
      DCT (FVSTm SHere) ∪m tFull
        ≡⟨ ∪t-right-zero (DCT (fromPath PHere)) ⟩
      tFull ∎

κ-full (Join S₁ S₂) (BExt p) (Join T Sing) = label-between-joins-full (κ S₁ p T) (id-label S₂) (κ-full S₁ p T) (trans (cong DCT (id-label-full S₂)) DCT-full)
κ-full (Join S₁ S₂) (BShift p) T = label-between-joins-full (id-label S₁) (κ S₂ p T) (trans (cong DCT (id-label-full S₁)) DCT-full) (κ-full S₂ p T)

κ-boundary-supp : (S : Tree n)
                → (p : Branch S d)
                → (T : Tree m)
                → .⦃ _ : has-trunk-height d T ⦄
                → (q : lh p ≥ tree-dim T)
                → (d : ℕ)
                → (b : Bool)
                → TransportVarSet-Label (supp-tree-bd d S b) (κ S p T) ≡ toVarSet (supp-tree-bd d (S >>[ p ] T) b)
κ-boundary-supp S p T q d b = begin
  TransportVarSet-Label (supp-tree-bd d S b)
    (κ S p T)
    ≡˘⟨ cong (λ a → TransportVarSet-Label a (κ S p T)) (trans (sym (FVLabel-WT-⋆ (ap (tree-inc-label d S b)))) (tree-inc-label-supp d S b)) ⟩
  TransportVarSet-Label (FVLabel (ap (tree-inc-label d S b)))
    (κ S p T)
    ≡˘⟨ TransportVarSet-Label-Label (ap (tree-inc-label d S b)) (κ S p T) (κ-Ty S p T) ⟩
  toVarSet (FVLabel (ap (tree-inc-label d S b) ●l (κ S p T ,, S⋆)))
    ≡˘⟨ DCT-toVarSet (FVLabel (ap (tree-inc-label d S b) ●l (κ S p T ,, S⋆))) ⟩
  toVarSet
    (DCT
     (FVLabel
      (ap (tree-inc-label d S b) ●l (κ S p T ,, S⋆))))
    ≡⟨ cong toVarSet (lem (Bd-Conditions-one-of d p T)) ⟩
  toVarSet (supp-tree-bd d (S >>[ p ] T) b) ∎
  where
    open ≡-Reasoning

    lem : Bd-Conditions d p T → DCT
            (FVLabel
             (ap (tree-inc-label d S b) ●l (κ S p T ,, S⋆)))
            ≡ supp-tree-bd d (S >>[ p ] T) b
    lem (Bd-Cond1 x y) = begin
      DCT
        (FVLabel
         (ap (tree-inc-label d S b) ●l (κ S p T ,, S⋆)))
        ≡⟨ EqSuppLabel (label-max-equality-to-equality (bd-κ-comm-1 S p T d x y q b)
                                                       (label-comp-Ty (tree-inc-Ty d S b) (κ-Ty S p T) TySStar)
                                                       (label-≃-Ty (insertion-bd-1 S p T d y q) (tree-inc-Ty d (S >>[ p ] T) b))) ⟩
      DCT (FVLabel (label-≃ (insertion-bd-1 S p T d y q) (ap (tree-inc-label d (S >>[ p ] T) b))))
        ≡⟨ FV-label-comp-full (SPath ∘ (ppath-≃ (insertion-bd-1 S p T d y q)))
                              (ap (tree-inc-label d (S >>[ p ] T) b))
                              (tree-inc-Ty d (S >>[ p ] T) b)
                              (trans (cong DCT (ppath-≃-full (insertion-bd-1 S p T d y q))) DCT-full) ⟩
      DCT (FVLabel (ap (tree-inc-label d (S >>[ p ] T) b)))
        ≡˘⟨ cong DCT (FVLabel-WT-⋆ (ap (tree-inc-label d (S >>[ p ] T) b))) ⟩
      DCT (FVLabel-WT (tree-inc-label d (S >>[ p ] T) b))
        ≡⟨ cong DCT (tree-inc-label-supp d (S >>[ p ] T) b) ⟩
      DCT (supp-tree-bd d (S >>[ p ] T) b)
        ≡⟨ DCT-supp-tree-bd d (S >>[ p ] T) b ⟩
      supp-tree-bd d (S >>[ p ] T) b ∎
    lem (Bd-Cond2 x) = begin
      DCT (FVLabel (ap (tree-inc-label d S b) ●l (κ S p T ,, S⋆)))
        ≡⟨ EqSuppLabel (label-max-equality-to-equality
                         (bd-κ-comm-2 S p T d b q x)
                         (label-comp-Ty (tree-inc-Ty d S b) (κ-Ty S p T) TySStar)
                         (label-comp-Ty (κ-Ty (tree-bd d S) (bd-branch S p d _) (tree-bd d T) ⦃ _ ⦄)
                                        (label-≃-Ty (insertion-bd-2 S p T d (bd-branch-lem p x)) (tree-inc-Ty d (S >>[ p ] T) b)) TySStar)) ⟩
      DCT (FVLabel (κ (tree-bd d S)
                      (bd-branch S p d (bd-branch-lem p x))
                      (tree-bd d T)
                      ⦃ bd-has-trunk-height d _ T (bd-branch-lem p x) ⦄
                   ●l (label-wt-≃ (insertion-bd-2 S p T d (bd-branch-lem p x)) (tree-inc-label d (S >>[ p ] T) b))))
        ≡⟨ FV-label-comp-full (κ (tree-bd d S)
                                 (bd-branch S p d (bd-branch-lem p x))
                                 (tree-bd d T)
                                 ⦃ _ ⦄)
                              (label-≃ (insertion-bd-2 S p T d _)
                                       (proj₁ (tree-inc-label d (S >>[ p ] T) b)))
                              (label-≃-Ty (insertion-bd-2 S p T d (bd-branch-lem p x))
                                          (tree-inc-Ty d (S >>[ p ] T) b))
                              (κ-full (tree-bd d S) (bd-branch S p d (bd-branch-lem p x)) (tree-bd d T) ⦃ _ ⦄) ⟩
      DCT (FVLabel (label-≃ (insertion-bd-2 S p T d _) (ap (tree-inc-label d (S >>[ p ] T) b))))
        ≡⟨ FV-label-comp-full (SPath ∘ ppath-≃ (insertion-bd-2 S p T d _))
                              (ap (tree-inc-label d (S >>[ p ] T) b))
                              (tree-inc-Ty d (S >>[ p ] T) b)
                              (trans (cong DCT (ppath-≃-full (insertion-bd-2 S p T d _))) DCT-full) ⟩
      DCT (FVLabel (ap (tree-inc-label d (S >>[ p ] T) b)))
        ≡˘⟨ cong DCT (FVLabel-WT-⋆ (ap (tree-inc-label d (S >>[ p ] T) b))) ⟩
      DCT (FVLabel-WT (tree-inc-label d (S >>[ p ] T) b))
        ≡⟨ cong DCT (tree-inc-label-supp d (S >>[ p ] T) b) ⟩
      DCT (supp-tree-bd d (S >>[ p ] T) b)
        ≡⟨ DCT-supp-tree-bd d (S >>[ p ] T) b ⟩
      supp-tree-bd d (S >>[ p ] T) b ∎

ins-supp : SupportCond′ rules InsertionSet
ins-supp [ Insert Γ S As L P T M p ] tty = begin
  SuppTm Γ (stm-to-term (SCoh S As (L ,, S⋆)))
    ≡˘⟨ FVSTm-to-term (SCoh S As (L ,, S⋆)) ⟩
  MtoVarSet (incCtx Γ) (FVLabel-WT (L ,, S⋆))
    ≡⟨⟩
  DC Γ (FVLabel-WT (L ,, S⋆))
    ≡⟨ cong (DC Γ) (FVLabel-WT-⋆ L) ⟩
  DC Γ (FVLabel L)
    ≡˘⟨ EqSuppLabel (label-max-equality-to-equality (κ-comm L P M S⋆ p) (label-comp-Ty (κ-Ty S P T) l2 TySStar) Lty) ⟩
  DC Γ (FVLabel (κ S P T ●l (L >>l[ P ] M ,, S⋆)))
    ≡⟨ TransportVarSet-Label-Label (κ S P T) (L >>l[ P ] M) l2 ⟩
  TransportVarSet-Label {ΓS = incCtx Γ} (FVLabel (κ S P T)) (L >>l[ P ] M)
    ≡˘⟨ TransportVarSet-Label-DCT {ΓS = incCtx Γ} (FVLabel (κ S P T)) (L >>l[ P ] M) ⟩
  TransportVarSet-Label {ΓS = incCtx Γ} (DCT (FVLabel (κ S P T))) (L >>l[ P ] M)
    ≡⟨ cong (λ - → TransportVarSet-Label {ΓS = incCtx Γ} - (L >>l[ P ] M)) (κ-full S P T) ⟩
  TransportVarSet-Label {ΓS = incCtx Γ} tFull (L >>l[ P ] M)
    ≡⟨ TransportVarSet-Label-full (L >>l[ P ] M) l2 ⟩
  DC Γ (FVLabel (L >>l[ P ] M))
    ≡˘⟨ cong (DC Γ) (FVLabel-WT-⋆ (L >>l[ P ] M)) ⟩
  DC Γ (FVLabel-WT (L >>l[ P ] M ,, S⋆))
    ≡⟨⟩
  MtoVarSet (incCtx Γ) (FVLabel-WT (L >>l[ P ] M ,, S⋆))
    ≡⟨ FVSTm-to-term (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆)) ⟩
  SuppTm Γ (stm-to-term (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆))) ∎
  where
    open ≡-Reasoning

    Lty : Typing-Label Γ (L ,, S⋆)
    Lty = SCoh-Label-Ty tty

    lem : Typing-STm Γ (standard-coh (lh P) T >>= (M ,, S⋆)) _
    lem = transport-stm-typing (>>=-Ty (TySPath ⌊ P ⌋p) Lty TySStar)
                               (trans≃stm p (>>=-≃ (standard-coh′-compat (lh P) T) refl≃l refl≃sty))
                               refl≃sty

    Mty : Typing-Label Γ (M ,, S⋆)
    Mty = SCoh-Label-Ty {S = T} {As = standard-sty (lh P) T} {L = M} (stm-to-term-Ty lem)

    l1 : branch-type S P >>=′ (L ,, S⋆)
         ≈[ Γ ]sty
         standard-sty (lh P) T >>=′ (M ,, S⋆)
    l1 = STy-unique-≃ p (>>=-Ty (⌊⌋p-Ty P) Lty TySStar) (>>=-Ty (standard-coh′-Ty (lh P) T) Mty TySStar)

    l2 : Typing-Label Γ (L >>l[ P ] M ,, S⋆)
    l2 = label-from-insertion-Ty Lty P Mty l1
