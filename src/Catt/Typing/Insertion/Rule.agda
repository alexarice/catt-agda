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

data InsertionIdx : Set where
  Insert : (Γ : Ctx m)
         → (S : Tree n)
         → (As : STy (someTree S))
         → (L : Label (Other m) S)
         → (P : Branch S l)
         → (T : Tree n′)
         → .⦃ _ : has-trunk-height l T ⦄
         → (M : Label (Other m) T)
         → (p : L ⌊ P ⌋p ≃stm canonical-comp′ (ih P) T >>= (M ,, S⋆))
         → InsertionIdx

InsertionSet : RuleSet
InsertionSet .proj₁ = InsertionIdx
InsertionSet .proj₂ (Insert Γ S As L P T M p) = Insertion Γ S As L P T M

ins-lift : LiftCond InsertionSet
ins-lift (Insert Γ S As L P T M p) A .proj₁
  = Insert (Γ , A) S As (lift-stm ∘ L) P T (lift-stm ∘ M) lem
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
ins-lift (Insert Γ S As L P T M p) A .proj₂ .ctxeq = refl≃c
ins-lift (Insert Γ S As L P T M p) A .proj₂ .lhseq = sym≃tm (lift-stm-to-term (SCoh S As (L ,, S⋆)))
ins-lift (Insert Γ S As L P T M p) A .proj₂ .rhseq = begin
  < lift-tm (stm-to-term (SCoh (S >>[ P ] T)
                               (As >>=′ (κ S P T ,, S⋆))
                               (L >>l[ P ] M ,, S⋆))) >tm
    ≈˘⟨ lift-stm-to-term (SCoh (S >>[ P ] T)
                               (As >>=′ (κ S P T ,, S⋆))
                               (L >>l[ P ] M ,, S⋆)) ⟩
  < stm-to-term (SCoh (S >>[ P ] T)
                      (As >>=′ (κ S P T ,, S⋆))
                      (lift-label (L >>l[ P ] M ,, S⋆))) >tm
    ≈⟨ SCoh≃ (S >>[ P ] T)
             (refl≃sty {As = As >>=′ (κ S P T ,, S⋆)})
             (label-from-insertion-map lift-stm L P M)
             (refl≃sty {As = S⋆}) .get ⟩
  < stm-to-term (SCoh (S >>[ P ] T)
                      (As >>=′ (κ S P T ,, S⋆))
                      (lift-stm ∘ L >>l[ P ] lift-stm ∘ M ,, S⋆)) >tm ∎
  where
    open Reasoning tm-setoid

ins-susp : SuspCond InsertionSet
ins-susp (Insert Γ S As L P T M p) .proj₁ = Insert (susp-ctx Γ)
                                                   (Susp S)
                                                   (susp-sty As)
                                                   (susp-label-full L)
                                                   (BExt P)
                                                   (Susp T)
                                                   ⦃ inst ⦄
                                                   (susp-label-full M)
                                                   lem
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
ins-susp (Insert Γ S As L P T M p) .proj₂ .ctxeq = refl≃c
ins-susp (Insert Γ S As L P T M p) .proj₂ .lhseq = begin
  < susp-tm (stm-to-term (SCoh S As (L ,, S⋆))) >tm
    ≈˘⟨ susp-stm-to-term (SCoh S As (L ,, S⋆)) ⟩
  < stm-to-term (susp-stm (SCoh S As (L ,, S⋆))) >tm
    ≈⟨ SCoh-unrestrict S As (susp-label (L ,, S⋆)) .get ⟩
  < stm-to-term (SCoh (Susp S) (susp-sty As) (susp-label-full L ,, S⋆))
   >tm ∎
  where
    open Reasoning tm-setoid
ins-susp (Insert {l = l} Γ S As L P T M p) .proj₂ .rhseq = begin
  < susp-tm (stm-to-term (SCoh (S >>[ P ] T)
                               (As >>=′ (κ S P T ,, S⋆))
                               (L >>l[ P ] M ,, S⋆))) >tm
    ≈˘⟨ susp-stm-to-term (SCoh (S >>[ P ] T)
                               (As >>=′ (κ S P T ,, S⋆))
                               (L >>l[ P ] M ,, S⋆)) ⟩
  < stm-to-term (susp-stm (SCoh (S >>[ P ] T)
                                (As >>=′ (κ S P T ,, S⋆))
                                (L >>l[ P ] M ,, S⋆))) >tm
    ≈⟨ lem .get ⟩
  < stm-to-term (SCoh (Susp ((S >>[ P ] T) ⦃ _ ⦄))
                      (susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ⦃ _ ⦄ ,, S⋆))
                      ((susp-label-full L >>l[ BExt P ] susp-label-full M) ⦃ inst ⦄ ,, S⋆)) >tm ∎
  where
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

    lem : susp-stm (SCoh (S >>[ P ] T)
                         (As >>=′ (κ S P T ,, S⋆))
                         (L >>l[ P ] M ,, S⋆))
          ≃stm
          SCoh (Susp (S >>[ P ] T))
               (susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ⦃ inst ⦄ ,, S⋆))
               ((susp-label-full L >>l[ BExt P ] susp-label-full M) ⦃ inst ⦄ ,, S⋆)
    lem = begin
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

ins-sub : SubCond InsertionSet
ins-sub (Insert Γ S As L P T M p) Δ σ .proj₁
  = Insert Δ S As (_[ σ ]stm ∘ L) P T (_[ σ ]stm ∘ M) lem
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

ins-sub (Insert Γ S As L P T M p) Δ σ .proj₂ .ctxeq = refl≃c
ins-sub (Insert Γ S As L P T M p) Δ σ .proj₂ .lhseq = stm-sub-SCoh S As (L ,, S⋆) σ .get
ins-sub (Insert Γ S As L P T M p) Δ σ .proj₂ .rhseq = lem .get
  where
    open Reasoning stm-setoid
    lem : SCoh (S >>[ P ] T)
               (As >>=′ (κ S P T ,, S⋆))
               (L >>l[ P ] M ,, S⋆) [ σ ]stm
          ≃stm
          SCoh (S >>[ P ] T)
               (As >>=′ (κ S P T ,, S⋆))
               ((λ x → (L x) [ σ ]stm) >>l[ P ] (λ x → (M x) [ σ ]stm) ,, S⋆)
    lem = begin
      < SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆) [ σ ]stm >stm
        ≈⟨ stm-sub-SCoh (S >>[ P ] T)
                        (As >>=′ (κ S P T ,, S⋆))
                        (L >>l[ P ] M ,, S⋆)
                        σ ⟩
      < SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) ((L >>l[ P ] M ,, S⋆) [ σ ]l) >stm
        ≈⟨ SCoh≃ (S >>[ P ] T) refl≃sty (label-from-insertion-map (_[ σ ]stm) L P M) refl≃sty ⟩
      < SCoh (S >>[ P ] T)
             (As >>=′ (κ S P T ,, S⋆))
             ((_[ σ ]stm ∘ L) >>l[ P ] (_[ σ ]stm ∘ M) ,, S⋆)
       >stm ∎

open Tame

ins-tame : Tame InsertionSet
ins-tame .lift-cond = ins-lift
ins-tame .susp-cond = ins-susp
ins-tame .sub-cond = ins-sub
