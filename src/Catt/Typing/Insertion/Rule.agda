module Catt.Typing.Insertion.Rule where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Canonical
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
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
  = stm-to-term (SCoh (S >>[ P ] T)
                      (As >>=′ (κ S P T ,, S⋆))
                      (L >>l[ P ] M ,, S⋆))

data InsertionSet : RuleSet where
  Insert : (Γ : Ctx m)
         → (S : Tree n)
         → (As : STy (someTree S))
         → (L : Label (Other m) S)
         → (P : Branch S l)
         → (T : Tree n′)
         → .⦃ _ : has-trunk-height l T ⦄
         → (M : Label (Other m) T)
         → (p : L ⌊ P ⌋p ≃stm canonical-comp′ (ih P) T >>= (M ,, S⋆))
         → InsertionSet (Insertion Γ S As L P T M)

ins-lift : LiftCond InsertionSet
ins-lift A [ Insert Γ S As L P T M p ]
  = ∈r-≃ [ Insert (Γ , A) S As (lift-stm ∘ L) P T (lift-stm ∘ M) lem ] γ
  where
    lem : lift-stm (L ⌊ P ⌋p)
          ≃stm
          canonical-comp′ (ih P) T >>= lift-label (M ,, S⋆)
    lem = begin
      < lift-stm (L ⌊ P ⌋p) >stm
        ≈⟨ lift-stm-≃ p ⟩
      < lift-stm (canonical-comp′ (ih P) T >>= (M ,, S⋆)) >stm
        ≈˘⟨ >>=-lift (canonical-comp′ (ih P) T) (M ,, S⋆) ⟩
      < canonical-comp′ (ih P) T >>= lift-label (M ,, S⋆) >stm ∎
      where
        open Reasoning stm-setoid

    γ : Insertion (Γ , A) S As (lift-stm ∘ L) P T (lift-stm ∘ M)
        ≃r
        lift-rule (Insertion Γ S As L P T M) A
    γ .ctxeq = refl≃c
    γ .lhseq = lift-stm-to-term (SCoh S As (L ,, S⋆))
    γ .rhseq = begin
      < stm-to-term (SCoh (S >>[ P ] T)
                          (As >>=′ (κ S P T ,, S⋆))
                          (lift-stm ∘ L >>l[ P ] lift-stm ∘ M ,, S⋆)) >tm
        ≈˘⟨ SCoh≃ (S >>[ P ] T)
                 (refl≃sty {As = As >>=′ (κ S P T ,, S⋆)})
                 (label-from-insertion-map lift-stm L P M)
                 (refl≃sty {As = S⋆}) .get ⟩
      < stm-to-term (SCoh (S >>[ P ] T)
                          (As >>=′ (κ S P T ,, S⋆))
                          (lift-label (L >>l[ P ] M ,, S⋆))) >tm
        ≈⟨ lift-stm-to-term (SCoh (S >>[ P ] T)
                                   (As >>=′ (κ S P T ,, S⋆))
                                   (L >>l[ P ] M ,, S⋆)) ⟩
      < lift-tm (stm-to-term (SCoh (S >>[ P ] T)
                                   (As >>=′ (κ S P T ,, S⋆))
                                   (L >>l[ P ] M ,, S⋆))) >tm ∎
      where
        open Reasoning tm-setoid

ins-susp : SuspCond InsertionSet
ins-susp [ Insert {l = l} Γ S As L P T M p ]
  = ∈r-≃ [ Insert (susp-ctx Γ) (Susp S) (susp-sty As) (susp-label-full L) (BExt P) (Susp T) ⦃ inst ⦄ (susp-label-full M) lem ] γ
  where
    lem : susp-label-full L (PExt ⌊ P ⌋p)
          ≃stm
          SExt (canonical-comp′ (ih P) T) >>= (susp-label-full M ,, S⋆)
    lem = begin
      < susp-stm (L ⌊ P ⌋p) >stm
        ≈⟨ susp-stm-≃ p ⟩
      < susp-stm (canonical-comp′ (ih P) T >>= (M ,, S⋆)) >stm
        ≈⟨ susp-stm-functorial (canonical-comp′ (ih P) T) M ⟩
      < SExt (canonical-comp′ (ih P) T) >>= (susp-label-full M ,, S⋆) >stm ∎
      where
        open Reasoning stm-setoid

    l4 : κ (Susp S) (BExt P) (Susp T) ⦃ inst ⦄
         ≃l
         susp-label-full (κ S P T)
    l4 .get PHere = refl≃stm
    l4 .get (PExt Z) = refl≃stm
    l4 .get (PShift PHere) = refl≃stm

    l2 : susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ⦃ inst ⦄ ,, S⋆)
         ≃sty
         susp-sty (As >>=′ (κ S P T ,, S⋆))
    l2 = begin
      < susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ⦃ inst ⦄ ,, S⋆) >sty
        ≈⟨ >>=′-≃ (refl≃sty {As = susp-sty As}) l4 refl≃sty ⟩
      < susp-sty As >>=′ (susp-label-full (κ S P T) ,, S⋆) >sty
        ≈˘⟨ susp-sty-functorial As (κ S P T) ⟩
      < susp-sty (As >>=′ (κ S P T ,, S⋆)) >sty ∎
      where
        open Reasoning sty-setoid

    l3 : ap ((susp-label-full L >>l[ BExt P ] susp-label-full M) ⦃ inst ⦄ ,, S⋆)
         ≃l
         ap (susp-label-full (L >>l[ P ] M) ,, S⋆)
    l3 .get PHere = refl≃stm
    l3 .get (PExt Z) = sym≃stm (label-from-insertion-map susp-stm L P M ⦃ it ⦄ .get Z)
    l3 .get (PShift PHere) = refl≃stm

    l1 : susp-stm (SCoh (S >>[ P ] T)
                         (As >>=′ (κ S P T ,, S⋆))
                         (L >>l[ P ] M ,, S⋆))
         ≃stm
         SCoh (Susp (S >>[ P ] T))
              (susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ⦃ inst ⦄ ,, S⋆))
              ((susp-label-full L >>l[ BExt P ] susp-label-full M) ⦃ inst ⦄ ,, S⋆)
    l1 = begin
      < SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (susp-label (L >>l[ P ] M ,, S⋆)) >stm
        ≈⟨ SCoh-unrestrict (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (susp-label (L >>l[ P ] M ,, S⋆)) ⟩
      < SCoh (Susp (S >>[ P ] T))
             (susp-sty (As >>=′ (κ S P T ,, S⋆)))
             (susp-label-full (L >>l[ P ] M) ,, S⋆) >stm
        ≈˘⟨ SCoh≃ (Susp (S >>[ P ] T)) l2 l3 refl≃sty ⟩
      < SCoh (Susp (S >>[ P ] T))
             (susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ⦃ inst ⦄ ,, S⋆))
             ((susp-label-full L >>l[ BExt P ] susp-label-full M) ⦃ inst ⦄ ,, S⋆) >stm ∎
      where
        open Reasoning stm-setoid

    open Reasoning tm-setoid

    γ : Insertion (susp-ctx Γ) (Susp S) (susp-sty As) (susp-label-full L) (BExt P) (Susp T) ⦃ inst ⦄ (susp-label-full M)
        ≃r
        susp-rule (Insertion Γ S As L P T M)
    γ .ctxeq = refl≃c
    γ .lhseq = begin
      < stm-to-term (SCoh (Susp S) (susp-sty As) (susp-label-full L ,, S⋆)) >tm
        ≈˘⟨ SCoh-unrestrict S As (susp-label (L ,, S⋆)) .get ⟩
      < stm-to-term (susp-stm (SCoh S As (L ,, S⋆))) >tm
        ≈⟨ susp-stm-to-term (SCoh S As (L ,, S⋆)) ⟩
      < susp-tm (stm-to-term (SCoh S As (L ,, S⋆))) >tm ∎
    γ .rhseq = begin
      < stm-to-term (SCoh (Susp ((S >>[ P ] T) ⦃ _ ⦄))
                          (susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ⦃ _ ⦄ ,, S⋆))
                          ((susp-label-full L >>l[ BExt P ] susp-label-full M) ⦃ inst ⦄ ,, S⋆)) >tm
        ≈˘⟨ l1 .get ⟩
      < stm-to-term (susp-stm (SCoh (S >>[ P ] T)
                                    (As >>=′ (κ S P T ,, S⋆))
                                    (L >>l[ P ] M ,, S⋆))) >tm
        ≈⟨ susp-stm-to-term (SCoh (S >>[ P ] T)
                                   (As >>=′ (κ S P T ,, S⋆))
                                   (L >>l[ P ] M ,, S⋆)) ⟩
      < susp-tm (stm-to-term (SCoh (S >>[ P ] T)
                                   (As >>=′ (κ S P T ,, S⋆))
                                   (L >>l[ P ] M ,, S⋆))) >tm ∎

ins-sub : SubCond InsertionSet
ins-sub Δ σ [ Insert Γ S As L P T M p ]
  = ∈r-≃ [ Insert Δ S As (_[ σ ]stm ∘ L) P T (_[ σ ]stm ∘ M) lem ] γ
  where
    open Reasoning stm-setoid
    lem : L ⌊ P ⌋p [ σ ]stm
          ≃stm
          canonical-comp′ (ih P) T >>= ((_[ σ ]stm ∘ M) ,, S⋆)
    lem = begin
      < L ⌊ P ⌋p [ σ ]stm >stm
        ≈⟨ stm-sub-≃ p σ ⟩
      < (canonical-comp′ (ih P) T >>= (M ,, S⋆)) [ σ ]stm >stm
        ≈⟨ stm-sub->>= (canonical-comp′ (ih P) T) (M ,, S⋆) σ ⟩
      < canonical-comp′ (ih P) T >>= ((M ,, S⋆) [ σ ]l) >stm ∎

    l1 : SCoh (S >>[ P ] T)
              (As >>=′ (κ S P T ,, S⋆))
              ((λ x → (L x) [ σ ]stm) >>l[ P ] (λ x → (M x) [ σ ]stm) ,, S⋆)
         ≃stm
         SCoh (S >>[ P ] T)
               (As >>=′ (κ S P T ,, S⋆))
               (L >>l[ P ] M ,, S⋆) [ σ ]stm
    l1 = begin
      < SCoh (S >>[ P ] T)
             (As >>=′ (κ S P T ,, S⋆))
             ((_[ σ ]stm ∘ L) >>l[ P ] (_[ σ ]stm ∘ M) ,, S⋆) >stm
        ≈˘⟨ SCoh≃ (S >>[ P ] T) refl≃sty (label-from-insertion-map (_[ σ ]stm) L P M) refl≃sty ⟩
      < SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) ((L >>l[ P ] M ,, S⋆) [ σ ]l) >stm
        ≈˘⟨ stm-sub-SCoh (S >>[ P ] T)
                        (As >>=′ (κ S P T ,, S⋆))
                        (L >>l[ P ] M ,, S⋆)
                        σ ⟩
      < SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆) [ σ ]stm >stm ∎

    γ : Insertion Δ S As (λ x → L x [ σ ]stm) P T (λ x → M x [ σ ]stm) ≃r
         sub-rule (Insertion Γ S As L P T M) Δ σ
    γ .ctxeq = refl≃c
    γ .lhseq = sym≃tm (stm-sub-SCoh S As (L ,, S⋆) σ .get)
    γ .rhseq = l1 .get

open Tame

ins-tame : Tame InsertionSet
ins-tame .lift-cond = ins-lift
ins-tame .susp-cond = ins-susp
ins-tame .sub-cond = ins-sub
