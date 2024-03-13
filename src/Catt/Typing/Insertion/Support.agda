open import Catt.Typing.Rule

module Catt.Typing.Insertion.Support (ops : Op)
                                     (rules : RuleSet)
                                     (tame : Tame ops rules)
                                     (supp-cond : SupportCond ops rules) where

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
open import Catt.Tree.Insertion.Support
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame
open import Catt.Tree.Boundary.Typing ops rules tame
open import Catt.Tree.Standard.Typing ops rules tame
open import Catt.Tree.Insertion.Typing ops rules tame
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

open import Catt.Typing.Structured.Support ops rules tame supp-cond

ins-supp : SupportCond′ ops rules InsertionSet
ins-supp [ Insert Γ S As L P T q M p ] tty = begin
  SuppTm Γ (stm-to-term (SCoh S As (L ,, S⋆)))
    ≡˘⟨ FVSTm-to-term (SCoh S As (L ,, S⋆)) ⟩
  MtoVarSet (incCtx Γ) (FVLabel-WT (L ,, S⋆))
    ≡⟨⟩
  DC Γ (FVLabel-WT (L ,, S⋆))
    ≡⟨ cong (DC Γ) (FVLabel-WT-⋆ L) ⟩
  DC Γ (FVLabel L)
    ≡˘⟨ EqSuppLabel (label-max-equality-to-equality (κ-comm L P M S⋆ p) (label-comp-Ty (κ-Ty S P T q) l2 TySStar) Lty) ⟩
  DC Γ (FVLabel (κ S P T ●l (L >>l[ P ] M ,, S⋆)))
    ≡⟨ vs-label-Label (κ S P T) (L >>l[ P ] M) l2 ⟩
  _[_]vl {ΓS = incCtx Γ} (FVLabel (κ S P T)) (L >>l[ P ] M)
    ≡˘⟨ vs-label-DCT {ΓS = incCtx Γ} (FVLabel (κ S P T)) (L >>l[ P ] M) ⟩
  _[_]vl {ΓS = incCtx Γ} (DCT (FVLabel (κ S P T))) (L >>l[ P ] M)
    ≡⟨ cong (λ - → _[_]vl {ΓS = incCtx Γ} - (L >>l[ P ] M)) (κ-full S P T) ⟩
  _[_]vl {ΓS = incCtx Γ} tFull (L >>l[ P ] M)
    ≡⟨ vs-label-full (L >>l[ P ] M) l2 ⟩
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
    l1 = STy-unique-≃ p (>>=-Ty (⌊⌋p-Ty P) Lty TySStar) (>>=-Ty (standard-coh′-Ty (lh P) T q) Mty TySStar)

    l2 : Typing-Label Γ (L >>l[ P ] M ,, S⋆)
    l2 = label-from-insertion-Ty Lty P Mty l1

module _ where
  open ≡-Reasoning
  κ-preserves-supp : (S : Tree n)
                   → (As : STy (someTree S))
                   → (P : Branch S l)
                   → (T : Tree m)
                   → .⦃ _ : has-trunk-height l T ⦄
                   → lh P ≥ tree-dim T
                   → (b : Bool)
                   → supp-condition-s b S As
                   → supp-condition-s (b ∧ (tree-dim (S >>[ P ] T) ≡ᵇ tree-dim S)) (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆))
  κ-preserves-supp S As P T p false x = trans (DCT-reflect lem) DCT-full
    where
      lem : toVarSet (FVSTy (As >>=′ (κ S P T ,, S⋆))) ≡ toVarSet (tFull {S = S >>[ P ] T})
      lem = begin
        toVarSet (FVSTy (As >>=′ (κ S P T ,, S⋆)))
          ≡⟨ vs-label-STy As (κ S P T) (κ-Ty S P T p) ⟩
        FVSTy As [ κ S P T ]vl
          ≡˘⟨ vs-label-DCT (FVSTy As) (κ S P T) ⟩
        DCT (FVSTy As) [ κ S P T ]vl
          ≡⟨ cong (_[ κ S P T ]vl) x ⟩
        mFull [ κ S P T ]vl
          ≡⟨ vs-label-full (κ S P T) (κ-Ty S P T p) ⟩
        toVarSet (FVLabel (κ S P T))
          ≡˘⟨ DCT-toVarSet (FVLabel (κ S P T)) ⟩
        toVarSet (DCT (FVLabel (κ S P T)))
          ≡⟨ cong toVarSet (κ-full S P T) ⟩
        toVarSet (tFull {S = S >>[ P ] T}) ∎

  κ-preserves-supp S (SArr s As t) P T p true (nz ,, src ,, tgt)
    with tree-dim (S >>[ P ] T) ≡ᵇ tree-dim S
         | inspect (tree-dim (S >>[ P ] T) ≡ᵇ_) (tree-dim S)
  ... | false | [ eq ]r = begin
    DCT (FVSTy (As >>=′ (κ S P T ,, S⋆))
        ∪t FVSTm (s >>= (κ S P T ,, S⋆))
        ∪t FVSTm (t >>= (κ S P T ,, S⋆)))
      ≡⟨ DCT-∪ _ _ ⟩
    DCT (FVSTy (As >>=′ (κ S P T ,, S⋆)) ∪t FVSTm (s >>= (κ S P T ,, S⋆)))
     ∪t DCT (FVSTm (t >>= (κ S P T ,, S⋆)))
      ≡⟨ cong (DCT (FVSTy (As >>=′ (κ S P T ,, S⋆))
                   ∪t FVSTm (s >>= (κ S P T ,, S⋆))) ∪t_)
              lem ⟩
    DCT (FVSTy (As >>=′ (κ S P T ,, S⋆)) ∪t FVSTm (s >>= (κ S P T ,, S⋆)))
     ∪t tFull
      ≡⟨ ∪t-right-zero _ ⟩
    tFull ∎
    where
      dim-< : tree-dim (S >>[ P ] T) ≤ pred (tree-dim S)
      dim-< with <-cmp (tree-dim (S >>[ P ] T)) (tree-dim S)
      ... | tri< a ¬b ¬c = ≤-pred (≤-trans a (suc-pred-≤ (tree-dim S)))
      ... | tri≈ ¬a b ¬c = ⊥-elim (subst Truth eq (≡⇒≡ᵇ (tree-dim (S >>[ P ] T)) (tree-dim S) b))
      ... | tri> ¬a ¬b c = ⊥-elim (≤⇒≯ (insertion-tree-dim S P T p) c)

      l1 : toVarSet (FVSTm (t >>= (κ S P T ,, S⋆))) ≡ toVarSet (supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) true)
      l1 = begin
        toVarSet (FVSTm (t >>= (κ S P T ,, S⋆)))
          ≡⟨ vs-label-STm t (κ S P T) (κ-Ty S P T p) ⟩
        FVSTm t [ κ S P T ]vl
          ≡˘⟨ vs-label-DCT (FVSTm t) (κ S P T) ⟩
        DCT (FVSTm t) [ κ S P T ]vl
          ≡⟨ cong (_[ κ S P T ]vl) tgt ⟩
        supp-tree-bd (pred (tree-dim S)) S true [ κ S P T ]vl
          ≡⟨ κ-boundary-supp S P T p (pred (tree-dim S)) true ⟩
        toVarSet (supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) true) ∎

      lem : DCT (FVSTm (t >>= (κ S P T ,, S⋆))) ≡ tFull
      lem = begin
        DCT (FVSTm (t >>= (κ S P T ,, S⋆)))
          ≡⟨ DCT-reflect l1 ⟩
        DCT (supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) true)
          ≡⟨ DCT-supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) true ⟩
        supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) true
          ≡⟨ supp-tree-bd-full (pred (tree-dim S)) (S >>[ P ] T) true dim-< ⟩
        tFull ∎
  ... | true | [ eq ]r = NonZero-subst (sym dim-eq) nz ,, lem s false src ,, lem t true tgt
    where
      dim-eq : tree-dim (S >>[ P ] T) ≡ tree-dim S
      dim-eq = ≡ᵇ⇒≡ (tree-dim (S >>[ P ] T)) (tree-dim S) (T-≡ .from eq )

      l1 : (a : STm (someTree S))
         → (b : Bool)
         → DCT (FVSTm a) ≡ supp-tree-bd (pred (tree-dim S)) S b
         → toVarSet (FVSTm (a >>= (κ S P T ,, S⋆)))
           ≡
           toVarSet (supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) b)
      l1 a b q = begin
        toVarSet (FVSTm (a >>= (κ S P T ,, S⋆)))
          ≡⟨ vs-label-STm a (κ S P T) (κ-Ty S P T p) ⟩
        FVSTm a [ κ S P T ]vl
          ≡˘⟨ vs-label-DCT (FVSTm a) (κ S P T) ⟩
        DCT (FVSTm a) [ κ S P T ]vl
          ≡⟨ cong (_[ κ S P T ]vl) q ⟩
        supp-tree-bd (pred (tree-dim S)) S b [ κ S P T ]vl
          ≡⟨ κ-boundary-supp S P T p (pred (tree-dim S)) b ⟩
        toVarSet (supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) b) ∎

      lem : (a : STm (someTree S))
          → (b : Bool)
          → DCT (FVSTm a) ≡ supp-tree-bd (pred (tree-dim S)) S b
          → DCT (FVSTm (a >>= (κ S P T ,, S⋆)))
            ≡
            supp-tree-bd (pred (tree-dim (S >>[ P ] T))) (S >>[ P ] T) b
      lem a b q = begin
        DCT (FVSTm (a >>= (κ S P T ,, S⋆)))
          ≡⟨ DCT-reflect (l1 a b q) ⟩
        DCT (supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) b)
          ≡⟨ DCT-supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) b ⟩
        supp-tree-bd (pred (tree-dim S)) (S >>[ P ] T) b
          ≡˘⟨ cong (λ - → supp-tree-bd (pred -) (S >>[ P ] T) b) dim-eq ⟩
        supp-tree-bd (pred (tree-dim (S >>[ P ] T))) (S >>[ P ] T) b ∎
