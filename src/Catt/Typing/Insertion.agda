open import Catt.Typing.Base

module Catt.Typing.Insertion {index : Set} (rule : index → Rule) where

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
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Canonical
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties

open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule
open import Catt.Tree.Structured.Typing rule

open import Catt.Typing.Insertion.Base public

HasInsertion : Set
HasInsertion = ∀ {m n l n′}
             → {Γ : Ctx m}
             → {X : MaybeTree m}
             → {S : Tree n}
             → (As : STy (someTree S))
             → (L : Label X S)
             → (P : Branch S l)
             → {T : Tree n′}
             → .⦃ _ : has-trunk-height l T ⦄
             → (M : Label X T)
             → L ⌊ P ⌋p ≃stm (canonical-comp′ (ih P) T >>= (M ,, S⋆))
             → {Cs : STy X}
             → Typing-STm Γ (SCoh S As (L ,, S⋆)) Cs
             → (SCoh S As (L ,, S⋆))
               ≈[ Γ ]stm
               SCoh (insertion-tree S P T) (As >>=′ (κ S P T ,, S⋆)) (label-from-insertion S P T L M ,, S⋆)

module Conditions (ins : HasInsertion) where
  open import Catt.Typing.Rule rule

  lift-rule : (P : Branch S l)
            → .⦃ _ : has-trunk-height l T ⦄
            → (pf : L ⌊ P ⌋p ≃stm canonical-comp′ (ih P) T >>= (M ,, S⋆))
            → LiftRule (Insertion Γ S As L P T M)
  lift-rule {S = S} {T = T} {L = L} {M = M} {Γ = Γ} {As = As} P pf {A = A} {C = C} tty = begin
    lift-tm (stm-to-term (SCoh S As (L ,, S⋆)))
      ≈˘⟨ reflexive≈tm (lift-stm-to-term (SCoh S As (L ,, S⋆))) ⟩
    stm-to-term (SCoh S As (lift-label (L ,, S⋆)))
      ≈⟨ lem .get ⟩
    stm-to-term (SCoh (insertion-tree S P T)
                      (As >>=′ (κ S P T ,, S⋆))
                      (lift-label (label-from-insertion S P T L M ,, S⋆)))
      ≈⟨ reflexive≈tm (lift-stm-to-term (SCoh (insertion-tree S P T)
                                              (As >>=′ (κ S P T ,, S⋆))
                                              (label-from-insertion S P T L M ,, S⋆))) ⟩
    lift-tm (stm-to-term (SCoh (insertion-tree S P T)
                               (As >>=′ (κ S P T ,, S⋆))
                               (label-from-insertion S P T L M ,, S⋆))) ∎
    where
      l1 : lift-stm (L ⌊ P ⌋p)
           ≃stm
           canonical-comp′ (ih P) T >>= lift-label (M ,, S⋆)
      l1 = begin
        < lift-stm (L ⌊ P ⌋p) >stm
          ≈⟨ lift-stm-≃ pf ⟩
        < lift-stm (canonical-comp′ (ih P) T >>= (M ,, S⋆)) >stm
          ≈˘⟨ >>=-lift (canonical-comp′ (ih P) T) (M ,, S⋆) ⟩
        < canonical-comp′ (ih P) T >>= lift-label (M ,, S⋆) >stm ∎
        where
          open Reasoning stm-setoid

      lem : SCoh S As (lift-label (L ,, S⋆))
            ≈[ Γ , A ]stm
            SCoh (insertion-tree S P T)
                 (As >>=′ (κ S P T ,, S⋆))
                 (lift-label (label-from-insertion S P T L M ,, S⋆))
      lem = begin
        SCoh S As (lift-label (L ,, S⋆))
          ≈⟨ ins As (lift-stm ∘ L) P (lift-stm ∘ M) l1
                 [ (transport-typing-full tty
                                          (sym≃tm (lift-stm-to-term (SCoh S As (L ,, S⋆))))
                                          (sym≃ty (to-sty-to-type (lift-ty C)))) ] ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (κ S P T ,, S⋆))
             (label-from-insertion S P T (lift-stm ∘ L) (lift-stm ∘ M) ,, S⋆)
          ≈˘⟨ reflexive≈stm (SCoh≃ (insertion-tree S P T) refl≃sty (label-from-insertion-map lift-stm S P T L M) refl≃sty) ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (κ S P T ,, S⋆))
             (lift-label (label-from-insertion S P T L M ,, S⋆)) ∎
        where
          open Reasoning stm-setoid-≈
      open Reasoning (tm-setoid-≈ _)

  susp-rule : (P : Branch S l)
            → .⦃ _ : has-trunk-height l T ⦄
            → (pf : L ⌊ P ⌋p ≃stm canonical-comp′ (ih P) T >>= (M ,, S⋆))
            → SuspRule (Insertion Γ S As L P T M)
  susp-rule {S = S} {l = l} {T = T} {L = L} {M = M} {Γ = Γ} {As = As} P pf {C = C} tty = begin
    susp-tm (stm-to-term (SCoh S As (L ,, S⋆)))
      ≈˘⟨ reflexive≈tm (susp-stm-to-term (SCoh S As (L ,, S⋆))) ⟩
    stm-to-term (susp-stm (SCoh S As (L ,, S⋆)))
      ≈⟨ lem .get ⟩
    stm-to-term (susp-stm (SCoh (insertion-tree S P T)
                                (As >>=′ (κ S P T ,, S⋆))
                                (label-from-insertion S P T L M ,, S⋆)))
      ≈⟨ reflexive≈tm (susp-stm-to-term (SCoh (insertion-tree S P T)
                                              (As >>=′ (κ S P T ,, S⋆))
                                              (label-from-insertion S P T L M ,, S⋆))) ⟩
    susp-tm (stm-to-term (SCoh (insertion-tree S P T)
                               (As >>=′ (κ S P T ,, S⋆))
                               (label-from-insertion S P T L M ,, S⋆))) ∎
    where
      instance .x : has-trunk-height (suc l) (Susp T)
      x = inst

      l1 : susp-label-full L (PExt ⌊ P ⌋p)
           ≃stm
           SExt (canonical-comp′ (ih P) T) >>= (susp-label-full M ,, S⋆)
      l1 = begin
        < susp-stm (L ⌊ P ⌋p) >stm
          ≈⟨ susp-stm-≃ pf ⟩
        < susp-stm (canonical-comp′ (ih P) T >>= (M ,, S⋆)) >stm
          ≈⟨ susp-stm-functorial (canonical-comp′ (ih P) T) M ⟩
        < SExt (canonical-comp′ (ih P) T) >>= (susp-label-full M ,, S⋆) >stm ∎
        where open Reasoning stm-setoid

      l4 : κ (Susp S) (BExt P) (Susp T) ≃l
              susp-label-full (κ S P T)
      l4 .get PHere = refl≃stm
      l4 .get (PExt Z) = refl≃stm
      l4 .get (PShift PHere) = refl≃stm

      l2 : susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ,, S⋆)
           ≃sty
           susp-sty (As >>=′ (κ S P T ,, S⋆))
      l2 = begin
        < susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ,, S⋆) >sty
          ≈⟨ >>=′-≃ (refl≃sty {A = susp-sty As}) l4 refl≃sty ⟩
        < susp-sty As >>=′ (susp-label-full (κ S P T) ,, S⋆) >sty
          ≈˘⟨ susp-sty-functorial As (κ S P T) ⟩
        < susp-sty (As >>=′ (κ S P T ,, S⋆)) >sty ∎
        where
          open Reasoning sty-setoid

      l3 : ap (label-from-insertion (Susp S) (BExt P) (Susp T) ⦃ _ ⦄ (susp-label-full L) (susp-label-full M) ,, S⋆)
           ≃l
           ap (susp-label-full (label-from-insertion S P T L M) ,, S⋆)
      l3 .get PHere = refl≃stm
      l3 .get (PExt Z) = sym≃stm (label-from-insertion-map susp-stm S P T L M .get Z)
      l3 .get (PShift PHere) = refl≃stm

      lem : susp-stm (SCoh S As (L ,, S⋆))
            ≈[ susp-ctx Γ ]stm
            susp-stm (SCoh (insertion-tree S P T)
                           (As >>=′ (κ S P T ,, S⋆))
                           (label-from-insertion S P T L M ,, S⋆))
      lem = begin
        SCoh S As (susp-label (L ,, S⋆))
          ≈⟨ reflexive≈stm (SCoh-unrestrict S As (susp-label (L ,, S⋆))) ⟩
        SCoh (Susp S) (susp-sty As) (susp-label-full L ,, S⋆)
          ≈⟨ ins (susp-sty As)
                 (susp-label-full L)
                 (BExt P)
                 (susp-label-full M)
                 l1
                 [ (transport-typing-full tty
                                          (trans≃tm (sym≃tm (susp-stm-to-term (SCoh S As (L ,, S⋆))))
                                                    (SCoh-unrestrict S As (susp-label (L ,, S⋆)) .get) )
                                          (sym≃ty (to-sty-to-type (susp-ty C)))) ] ⟩
        SCoh (Susp (insertion-tree S P T ⦃ _ ⦄))
             (susp-sty As >>=′ (κ (Susp S) (BExt P) (Susp T) ⦃ _ ⦄ ,, S⋆))
             (label-from-insertion (Susp S) (BExt P) (Susp T) ⦃ it ⦄ (susp-label-full L) (susp-label-full M) ,, S⋆)
          ≈⟨ reflexive≈stm (SCoh≃ (Susp (insertion-tree S P T ⦃ it ⦄)) l2 l3 refl≃sty) ⟩
        SCoh (Susp (insertion-tree S P T))
             (susp-sty (As >>=′ (κ S P T ,, S⋆)))
             (susp-label-full (label-from-insertion S P T L M) ,, S⋆)
          ≈˘⟨ reflexive≈stm (SCoh-unrestrict (insertion-tree S P T)
                                             (As >>=′ (κ S P T ,, S⋆))
                                             (susp-label (label-from-insertion S P T L M ,, S⋆))) ⟩
        SCoh (insertion-tree S P T) (As >>=′ (κ S P T ,, S⋆)) (susp-label (label-from-insertion S P T L M ,, S⋆)) ∎
        where
          open Reasoning stm-setoid-≈

      open Reasoning (tm-setoid-≈ _)

  sub-rule : (P : Branch S l)
           → .⦃ _ : has-trunk-height l T ⦄
           → (pf : L ⌊ P ⌋p ≃stm canonical-comp′ (ih P) T >>= (M ,, S⋆))
           → SubRule (Insertion Γ S As L P T M)
  sub-rule {S = S} {l = l} {T = T} {L = L} {M = M} {Γ = Γ} {As = As} P pf {σ = σ} {Δ = Δ} {C = C} σty tty = lem .get
    where
      l1 : L ⌊ P ⌋p [ σ ]stm
           ≃stm
           canonical-comp′ (ih P) T >>= ((M ,, S⋆) [ σ ]l)
      l1 = begin
        < L ⌊ P ⌋p [ σ ]stm >stm
          ≈⟨ stm-sub-≃ pf σ ⟩
        < (canonical-comp′ (ih P) T >>= (M ,, S⋆)) [ σ ]stm >stm
          ≈⟨ stm-sub->>= (canonical-comp′ (ih P) T) (M ,, S⋆) σ ⟩
        < canonical-comp′ (ih P) T >>= ((M ,, S⋆) [ σ ]l) >stm ∎
        where
          open Reasoning stm-setoid

      lem : SCoh S As (L ,, S⋆) [ σ ]stm
            ≈[ Δ ]stm
            SCoh (insertion-tree S P T)
                 (As >>=′ (κ S P T ,, S⋆))
                 (label-from-insertion S P T L M ,, S⋆) [ σ ]stm
      lem = begin
        SCoh S As (L ,, S⋆) [ σ ]stm
          ≈⟨ reflexive≈stm (stm-sub-SCoh S As (L ,, S⋆) σ) ⟩
        SCoh S As ((L ,, S⋆) [ σ ]l)
          ≈⟨ ins As
                 (_[ σ ]stm ∘ L)
                 P
                 (_[ σ ]stm ∘ M)
                 l1
                 [ (transport-typing-full tty (stm-sub-SCoh S As (L ,, S⋆) σ .get) (sym≃ty (to-sty-to-type (C [ σ ]ty)))) ] ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (κ S P T ,, S⋆))
             (label-from-insertion S P T (λ x → (L x) [ σ ]stm) (λ x → (M x) [ σ ]stm) ,, S⋆)
          ≈˘⟨ reflexive≈stm (SCoh≃ (insertion-tree S P T)
                           refl≃sty
                           (label-from-insertion-map (λ x → x [ σ ]stm) S P T L M)
                           refl≃sty) ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (κ S P T ,, S⋆))
             ((label-from-insertion S P T L M ,, S⋆) [ σ ]l)
          ≈˘⟨ reflexive≈stm (stm-sub-SCoh (insertion-tree S P T)
                                          (As >>=′ (κ S P T ,, S⋆))
                                          (label-from-insertion S P T L M ,, S⋆) σ) ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (κ S P T ,, S⋆))
             (label-from-insertion S P T L M ,, S⋆) [ σ ]stm ∎
        where
          open Reasoning stm-setoid-≈
