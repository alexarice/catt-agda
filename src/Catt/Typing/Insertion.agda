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
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Unbiased
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
             → (S : Tree n)
             → (As : STy (someTree S))
             → (L : Label X S)
             → (P : BranchingPoint S l)
             → (T : Tree n′)
             → .⦃ _ : has-linear-height l T ⦄
             → (M : Label X T)
             → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆))
             → {Bs : STy X}
             → Typing-STm Γ (SCoh S As (L ,, S⋆)) Bs
             → (SCoh S As (L ,, S⋆)) ≈[ Γ ]stm SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)

HasSUAInsertion : Set
HasSUAInsertion = ∀ {m n l n′}
                → {Γ : Ctx m}
                → {X : MaybeTree m}
                → {S : Tree n}
                → {As : STy (someTree S)}
                → {L : Label X S}
                → (P : BranchingPoint S l)
                → {T : Tree n′}
                → .⦃ _ : has-linear-height l T ⦄
                → {M : Label X T}
                → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆))
                → IsCompOrIdent (height-of-branching P) T
                → {Bs : STy X}
                → Typing-STm Γ (SCoh S As (L ,, S⋆)) Bs
                → (SCoh S As (L ,, S⋆)) ≈[ Γ ]stm SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)

module Conditions (ins : HasSUAInsertion) where
  open import Catt.Typing.Rule rule

  lift-rule : (P : BranchingPoint S l)
            → .⦃ _ : has-linear-height l T ⦄
            → (pf : L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆)))
            → (p : IsCompOrIdent (height-of-branching P) T)
            → LiftRule (Insertion Γ S As L P T M)
  lift-rule {S = S} {T = T} {L = L} {M = M} {Γ = Γ} {As = As} P pf p {A = A} {C = C} tty = begin
    lift-tm (stm-to-term (SCoh S As (L ,, S⋆)))
      ≈˘⟨ reflexive≈tm (lift-stm-to-term (SCoh S As (L ,, S⋆))) ⟩
    stm-to-term (SCoh S As (lift-label (L ,, S⋆)))
      ≈⟨ lem .get ⟩
    stm-to-term (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (lift-label (sub-from-insertion-label S P T L M ,, S⋆)))
      ≈⟨ reflexive≈tm (lift-stm-to-term (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆))) ⟩
    lift-tm (stm-to-term (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆))) ∎
    where
      pf-lift : lift-stm (L (branching-path-to-path P)) ≃stm
                 (unbiased-comp′ (height-of-branching P) T >>= lift-label (M ,, S⋆))
      pf-lift = begin
        < lift-stm (L (branching-path-to-path P)) >stm
          ≈⟨ lift-stm-≃ pf ⟩
        < lift-stm (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆)) >stm
          ≈˘⟨ >>=-lift (unbiased-comp′ (height-of-branching P) T) (M ,, S⋆) ⟩
        < unbiased-comp′ (height-of-branching P) T >>= lift-label (M ,, S⋆) >stm ∎
        where
          open Reasoning stm-setoid

      lem : stm-eq (Γ , A) (SCoh S As (lift-label (L ,, S⋆))) (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (lift-label (sub-from-insertion-label S P T L M ,, S⋆)))
      lem = begin
        SCoh S As (lift-label (L ,, S⋆))
          ≈⟨ ins P pf-lift p [ (transport-typing-full tty (sym≃tm (lift-stm-to-term (SCoh S As (L ,, S⋆)))) (sym≃ty (to-sty-to-type (lift-ty C)))) ] ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (exterior-sub-label S P T ,, S⋆))
             (sub-from-insertion-label S P T (lift-stm ∘ L) (lift-stm ∘ M) ,, S⋆)
          ≈˘⟨ reflexive≈stm (SCoh≃ (insertion-tree S P T) refl≃sty (sub-from-insertion-label-map lift-stm S P T L M) refl≃sty) ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (exterior-sub-label S P T ,, S⋆))
             (lift-label (sub-from-insertion-label S P T L M ,, S⋆)) ∎
        where
          open Reasoning stm-setoid-≈
      open Reasoning (tm-setoid-≈ _)

  IsCompOrIdent-susp : (n : ℕ) → .⦃ NonZero n ⦄ → (T : Tree m) → IsCompOrIdent n T → IsCompOrIdent (suc n) (susp-tree T)
  IsCompOrIdent-susp n T (IsComp x) = IsComp (cong suc x)
  IsCompOrIdent-susp (suc n) T (IsIdent x) = IsIdent (Join≃ x Sing≃)

  susp-rule : (P : BranchingPoint S l)
            → .⦃ _ : has-linear-height l T ⦄
            → (pf : L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆)))
            → (p : IsCompOrIdent (height-of-branching P) T)
            → SuspRule (Insertion Γ S As L P T M)
  susp-rule {S = S} {T = T} {L = L} {M = M} {Γ = Γ} {As = As} P pf p {C = C} tty = begin
    susp-tm (stm-to-term (SCoh S As (L ,, S⋆)))
      ≈˘⟨ reflexive≈tm (susp-stm-to-term (SCoh S As (L ,, S⋆))) ⟩
    stm-to-term (susp-stm (SCoh S As (L ,, S⋆)))
      ≈⟨ lem .get ⟩
    stm-to-term (susp-stm (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)))
      ≈⟨ reflexive≈tm (susp-stm-to-term (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆))) ⟩
    susp-tm (stm-to-term (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆))) ∎
    where
      l1 : susp-label-full L (PExt (branching-path-to-path P)) ≃stm
             (unbiased-comp′ (suc (height-of-branching P)) (susp-tree T) >>=
              (susp-label-full M ,, S⋆))
      l1 = begin
        < susp-stm (L (branching-path-to-path P)) >stm
          ≈⟨ susp-stm-≃ pf ⟩
        < susp-stm (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆)) >stm
          ≈⟨ susp-stm-functorial (unbiased-comp′ (height-of-branching P) T) M ⟩
        < susp-stm (unbiased-comp′ (height-of-branching P) T) >>= (susp-label-full M ,, S⋆) >stm ∎
        where open Reasoning stm-setoid

      l4 : exterior-sub-label (susp-tree S) (BPExt P) (susp-tree T) ≃l
              susp-label-full (exterior-sub-label S P T)
      l4 .get PHere = refl≃stm
      l4 .get (PExt Z) = refl≃stm
      l4 .get (PShift PHere) = refl≃stm

      l2 : susp-sty As >>=′ (exterior-sub-label (susp-tree S) (BPExt P) (susp-tree T) ,, S⋆)
             ≃sty susp-sty (As >>=′ (exterior-sub-label S P T ,, S⋆))
      l2 = begin
        < susp-sty As >>=′ (exterior-sub-label (susp-tree S) (BPExt P) (susp-tree T) ,, S⋆) >sty
          ≈⟨ >>=′-≃ (refl≃sty {A = susp-sty As}) l4 refl≃sty ⟩
        < susp-sty As >>=′ (susp-label-full (exterior-sub-label S P T) ,, S⋆) >sty
          ≈˘⟨ susp-sty-functorial As (exterior-sub-label S P T) ⟩
        < susp-sty (As >>=′ (exterior-sub-label S P T ,, S⋆)) >sty ∎
        where
          open Reasoning sty-setoid

      l3 : ap
             (sub-from-insertion-label (susp-tree S) (BPExt P) (susp-tree T)
              (susp-label-full L) (susp-label-full M)
              ,, S⋆)
             ≃l ap (susp-label-full (sub-from-insertion-label S P T L M) ,, S⋆)
      l3 .get PHere = refl≃stm
      l3 .get (PExt Z) = sym≃stm (sub-from-insertion-label-map susp-stm S P T L M .get Z)
      l3 .get (PShift PHere) = refl≃stm

      lem : stm-eq (susp-ctx Γ) (susp-stm (SCoh S As (L ,, S⋆))) (susp-stm (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)))
      lem = begin
        SCoh S As (susp-label (L ,, S⋆))
          ≈⟨ reflexive≈stm (SCoh-unrestrict S As (susp-label (L ,, S⋆))) ⟩
        SCoh (susp-tree S) (susp-sty As) (susp-label-full L ,, S⋆)
          ≈⟨ ins (BPExt P)
                 l1
                 (IsCompOrIdent-susp (suc (height-of-branching′ P)) T p)
                 [ (transport-typing-full tty
                                          (trans≃tm (sym≃tm (susp-stm-to-term (SCoh S As (L ,, S⋆))))
                                                    (SCoh-unrestrict S As (susp-label (L ,, S⋆)) .get))
                                          (sym≃ty (to-sty-to-type (susp-ty C)))) ] ⟩
        SCoh (susp-tree (insertion-tree S P T))
             (susp-sty As >>=′ (exterior-sub-label (Join S Sing) (BPExt P) (susp-tree T) ,, S⋆))
             (sub-from-insertion-label (Join S Sing) (BPExt P) (susp-tree T) (susp-label-full L) (susp-label-full M) ,, S⋆)
          ≈⟨ reflexive≈stm (SCoh≃ (susp-tree (insertion-tree S P T)) l2 l3 refl≃sty) ⟩
        SCoh (susp-tree (insertion-tree S P T))
             (susp-sty (As >>=′ (exterior-sub-label S P T ,, S⋆)))
             (susp-label-full (sub-from-insertion-label S P T L M) ,, S⋆)
          ≈˘⟨ reflexive≈stm (SCoh-unrestrict (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (susp-label (sub-from-insertion-label S P T L M ,, S⋆))) ⟩
        SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (susp-label (sub-from-insertion-label S P T L M ,, S⋆)) ∎
        where
          open Reasoning stm-setoid-≈


      open Reasoning (tm-setoid-≈ _)

  sub-rule : (P : BranchingPoint S l)
            → .⦃ _ : has-linear-height l T ⦄
            → (pf : L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆)))
            → (p : IsCompOrIdent (height-of-branching P) T)
            → SubRule (Insertion Γ S As L P T M)
  sub-rule {S = S} {T = T} {L = L} {M = M} {Γ = Γ} {As = As} P pf p {σ = σ} {Δ = Δ} {C = C} σty tty = lem .get
    where
      l1 : ap ((L ,, S⋆) [ σ ]l) (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆) [ σ ]l)
      l1 = begin
        < L (branching-path-to-path P) [ σ ]stm >stm
          ≈⟨ stm-sub-≃ pf σ ⟩
        < (unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆)) [ σ ]stm >stm
          ≈⟨ stm-sub->>= (unbiased-comp′ (height-of-branching P) T) (M ,, S⋆) σ ⟩
        < unbiased-comp′ (height-of-branching P) T >>= (M ,, S⋆) [ σ ]l >stm ∎
        where
          open Reasoning stm-setoid

      lem : stm-eq Δ (SCoh S As (L ,, S⋆) [ σ ]stm) (SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆) [ σ ]stm)
      lem = begin
        SCoh S As (L ,, S⋆) [ σ ]stm
          ≈⟨ reflexive≈stm (stm-sub-SCoh S As (L ,, S⋆) σ) ⟩
        SCoh S As ((L ,, S⋆) [ σ ]l)
          ≈⟨ ins P l1 p [ (transport-typing-full tty (stm-sub-SCoh S As (L ,, S⋆) σ .get) (sym≃ty (to-sty-to-type (C [ σ ]ty)))) ] ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (exterior-sub-label S P T ,, S⋆))
             (sub-from-insertion-label S P T (λ x → (L x) [ σ ]stm) (λ x → (M x) [ σ ]stm) ,, S⋆)
          ≈˘⟨ reflexive≈stm (SCoh≃ (insertion-tree S P T)
                           refl≃sty
                           (sub-from-insertion-label-map (λ x → x [ σ ]stm) S P T L M)
                           refl≃sty) ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (exterior-sub-label S P T ,, S⋆))
             ((sub-from-insertion-label S P T L M ,, S⋆) [ σ ]l)
          ≈˘⟨ reflexive≈stm (stm-sub-SCoh (insertion-tree S P T) (As >>=′ (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆) σ) ⟩
        SCoh (insertion-tree S P T)
             (As >>=′ (exterior-sub-label S P T ,, S⋆))
             (sub-from-insertion-label S P T L M ,, S⋆) [ σ ]stm ∎
        where
          open Reasoning stm-setoid-≈
