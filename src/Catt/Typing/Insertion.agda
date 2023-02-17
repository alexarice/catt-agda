open import Catt.Typing.Base

module Catt.Typing.Insertion {index : Set} (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Path
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Suspension


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
             → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆)
             → Typing-STy (tree-to-ctx S) As
             → Typing-Label Γ (L ,, S⋆)
             → (SCoh S As (L ,, S⋆)) ≈[ Γ ]stm SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)

data IsCompOrIdent {m} (n : ℕ) (T : Tree m) : Set where
  IsComp : n ≡ tree-dim T → IsCompOrIdent n T
  IsIdent : T ≃ n-disc (pred n) → IsCompOrIdent n T

HasSUAInsertion : Set
HasSUAInsertion = ∀ {m n l n′}
             → {Γ : Ctx m}
             → {X : MaybeTree m}
             → (S : Tree n)
             → (As : STy (someTree S))
             → (L : Label X S)
             → (P : BranchingPoint S l)
             → (T : Tree n′)
             → .⦃ _ : has-linear-height l T ⦄
             → (M : Label X T)
             → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆)
             → IsCompOrIdent (height-of-branching P) T
             → Typing-STy (tree-to-ctx S) As
             → Typing-Label Γ (L ,, S⋆)
             → (SCoh S As (L ,, S⋆)) ≈[ Γ ]stm SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)

module Conditions (ins : HasSUAInsertion) where

  lift-rule : ∀ {m n l n′}
             → {Γ : Ctx m}
             → (S : Tree n)
             → (As : STy (someTree S))
             → (L : Label (Other m) S)
             → (P : BranchingPoint S l)
             → (T : Tree n′)
             → .⦃ _ : has-linear-height l T ⦄
             → (M : Label (Other m) T)
             → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆)
             → IsCompOrIdent (height-of-branching P) T
             → Typing-STy (tree-to-ctx S) As
             → {A : Ty m}
             → Typing-Label (Γ , A) (lift-label (L ,, S⋆))
             → lift-stm (SCoh S As (L ,, S⋆)) ≈[ Γ , A ]stm lift-stm (SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆))
  lift-rule S As L P T M p q AsTy Lty = begin
    SCoh S As (lift-label (L ,, S⋆))
      ≈⟨ ins S As (ap (lift-label (L ,, S⋆))) P T (ap (lift-label (M ,, S⋆))) lem q AsTy Lty ⟩
    SCoh (insertion-tree S P T)
      (label-on-sty As (exterior-sub-label S P T ,, S⋆))
      (sub-from-insertion-label S P T (ap (lift-label (L ,, S⋆)))
       (ap (lift-label (M ,, S⋆)))
       ,, S⋆)
      ≈˘⟨ reflexive≈stm (≃SCoh (insertion-tree S P T) refl≃sty (sub-from-insertion-label-map lift-stm S P T L M) refl≃sty) ⟩
    SCoh (insertion-tree S P T)
       (label-on-sty As (exterior-sub-label S P T ,, S⋆))
       (lift-label (sub-from-insertion-label S P T L M ,, S⋆)) ∎
    where
      lem : (ap (lift-label (L ,, S⋆)) (branching-path-to-path P) ≃stm
               (unbiased-comp′ (height-of-branching P) T >>=
                lift-label (M ,, S⋆)))
      lem = begin
        < lift-stm (L (branching-path-to-path P)) >stm
          ≈⟨ lift-stm-≃ p ⟩
        < lift-stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆) >stm
          ≈˘⟨ extend-lift (unbiased-comp′ (height-of-branching P) T) (M ,, S⋆) ⟩
        < unbiased-comp′ (height-of-branching P) T >>= lift-label (M ,, S⋆) >stm ∎
        where
          open Reasoning stm-setoid

      open Reasoning stm-setoid-≈

  IsCompOrIdent-susp : (n : ℕ) → .⦃ NonZero n ⦄ → (T : Tree m) → IsCompOrIdent n T → IsCompOrIdent (suc n) (suspTree T)
  IsCompOrIdent-susp n T (IsComp x) = IsComp (cong suc x)
  IsCompOrIdent-susp (suc n) T (IsIdent x) = IsIdent (Join≃ x Sing≃)

  susp-rule : ∀ {m n l n′}
             → {Γ : Ctx m}
             → {X : MaybeTree m}
             → (S : Tree n)
             → (As : STy (someTree S))
             → (L : Label X S)
             → (P : BranchingPoint S l)
             → (T : Tree n′)
             → .⦃ _ : has-linear-height l T ⦄
             → (M : Label X T)
             → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆)
             → IsCompOrIdent (height-of-branching P) T
             → Typing-STy (tree-to-ctx (suspTree S)) (susp-sty As)
             → Typing-Label (susp-ctx Γ) (susp-label-full L ,, S⋆)
             → susp-stm (SCoh S As (L ,, S⋆)) ≈[ susp-ctx Γ ]stm susp-stm (SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆))
  susp-rule S As L P T M p q Asty Lty = begin
    susp-stm (SCoh S As (L ,, S⋆))
      ≈⟨ reflexive≈stm (susp-stm-SCoh S As (L ,, S⋆)) ⟩
    SCoh S As (susp-label (L ,, S⋆))
      ≈⟨ reflexive≈stm (SCoh-unrestrict S As (susp-label (L ,, S⋆))) ⟩
    SCoh (suspTree S) (susp-sty As)
      (susp-label-full L ,, S⋆)
      ≈⟨ ins (suspTree S) (susp-sty As) (susp-label-full L) (BPExt P) (suspTree T) (susp-label-full M) l1 (IsCompOrIdent-susp (height-of-branching P) T q) Asty Lty ⟩
    SCoh (insertion-tree (suspTree S) (BPExt P) (suspTree T))
      (label-on-sty (susp-sty As)
       (exterior-sub-label (suspTree S) (BPExt P) (suspTree T) ,, S⋆))
      (sub-from-insertion-label (suspTree S) (BPExt P) (suspTree T)
       (susp-label-full L) (susp-label-full M)
       ,, S⋆)
      ≈⟨ reflexive≈stm (≃SCoh (suspTree (insertion-tree S P T)) l2 l3 refl≃sty) ⟩
    SCoh (suspTree (insertion-tree S P T))
      (susp-sty (label-on-sty As (exterior-sub-label S P T ,, S⋆)))
       (susp-label-full (sub-from-insertion-label S P T L M) ,, S⋆)
      ≈˘⟨ reflexive≈stm (SCoh-unrestrict (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (susp-label (sub-from-insertion-label S P T L M ,, S⋆))) ⟩
    SCoh (insertion-tree S P T)
      (label-on-sty As (exterior-sub-label S P T ,, S⋆))
      (susp-label (sub-from-insertion-label S P T L M ,, S⋆))
      ≈˘⟨ reflexive≈stm (susp-stm-SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)) ⟩
    susp-stm
       (SCoh (insertion-tree S P T)
        (label-on-sty As (exterior-sub-label S P T ,, S⋆))
        (sub-from-insertion-label S P T L M ,, S⋆)) ∎
    where
      l1 : susp-label-full L (PExt (branching-path-to-path P)) ≃stm
             (unbiased-comp′ (suc (height-of-branching P)) (suspTree T) >>=
              susp-label-full M ,, S⋆)
      l1 = begin
        < susp-stm (L (branching-path-to-path P)) >stm
          ≈⟨ susp-stm-≃ p ⟩
        < susp-stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆) >stm
          ≈⟨ extend-susp-label-full (unbiased-comp′ (height-of-branching P) T) M ⟩
        < susp-stm (unbiased-comp′ (height-of-branching P) T) >>= susp-label-full M ,, S⋆ >stm ∎
        where open Reasoning stm-setoid

      lem : exterior-sub-label (suspTree S) (BPExt P) (suspTree T) ≃l
              susp-label-full (exterior-sub-label S P T)
      lem .get PHere = refl≃stm
      lem .get (PExt Z) = refl≃stm
      lem .get (PShift PHere) = refl≃stm

      l2 : label-on-sty (susp-sty As) (exterior-sub-label (suspTree S) (BPExt P) (suspTree T) ,, S⋆)
             ≃sty susp-sty (label-on-sty As (exterior-sub-label S P T ,, S⋆))
      l2 = begin
        < label-on-sty (susp-sty As) (exterior-sub-label (suspTree S) (BPExt P) (suspTree T) ,, S⋆) >sty
          ≈⟨ label-on-sty-≃ (refl≃sty {A = susp-sty As}) lem refl≃sty ⟩
        < label-on-sty (susp-sty As) (susp-label-full (exterior-sub-label S P T) ,, S⋆) >sty
          ≈˘⟨ susp-label-full-on-sty As (exterior-sub-label S P T) ⟩
        < susp-sty (label-on-sty As (exterior-sub-label S P T ,, S⋆)) >sty ∎
        where
          open Reasoning sty-setoid

      l3 : ap
             (sub-from-insertion-label (suspTree S) (BPExt P) (suspTree T)
              (susp-label-full L) (susp-label-full M)
              ,, S⋆)
             ≃l ap (susp-label-full (sub-from-insertion-label S P T L M) ,, S⋆)
      l3 .get PHere = refl≃stm
      l3 .get (PExt Z) = sym≃stm (sub-from-insertion-label-map susp-stm S P T L M .get Z)
      l3 .get (PShift PHere) = refl≃stm

      open Reasoning stm-setoid-≈

  sub-rule : ∀ {m n l n′}
             → {Γ : Ctx l}
             → {Δ : Ctx m}
             → {X : MaybeTree m}
             → (S : Tree n)
             → (As : STy (someTree S))
             → (L : Label X S)
             → (P : BranchingPoint S l)
             → (T : Tree n′)
             → .⦃ _ : has-linear-height l T ⦄
             → (M : Label X T)
             → L (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆)
             → IsCompOrIdent (height-of-branching P) T
             → (σ : Sub m l ⋆)
             → Typing-STy (tree-to-ctx S) As
             → Typing-Label Γ (label-sub (L ,, S⋆) σ)
             → stm-sub (SCoh S As (L ,, S⋆)) σ ≈[ Γ ]stm stm-sub (SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)) σ
  sub-rule S As L P T M p q σ Asty Lty = begin
    stm-sub (SCoh S As (L ,, S⋆)) σ
      ≈⟨ reflexive≈stm (stm-sub-SCoh S As (L ,, S⋆) σ) ⟩
    SCoh S As (label-sub (L ,, S⋆) σ)
      ≈⟨ ins S As (ap (label-sub (L ,, S⋆) σ)) P T (ap (label-sub (M ,, S⋆) σ)) lem q Asty Lty ⟩
    SCoh (insertion-tree S P T)
      (label-on-sty As (exterior-sub-label S P T ,, S⋆))
      (sub-from-insertion-label S P T (ap (label-sub (L ,, S⋆) σ))
       (ap (label-sub (M ,, S⋆) σ)) ,, S⋆)
      ≈˘⟨ reflexive≈stm (≃SCoh (insertion-tree S P T) refl≃sty (sub-from-insertion-label-map (λ a → stm-sub a σ) S P T L M) refl≃sty) ⟩
    SCoh (insertion-tree S P T)
      (label-on-sty As (exterior-sub-label S P T ,, S⋆))
      (label-sub (sub-from-insertion-label S P T L M ,, S⋆) σ)
      ≈˘⟨ reflexive≈stm (stm-sub-SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆) σ) ⟩
    stm-sub
       (SCoh (insertion-tree S P T)
        (label-on-sty As (exterior-sub-label S P T ,, S⋆))
        (sub-from-insertion-label S P T L M ,, S⋆)) σ ∎
    where
      lem : proj₁ (label-sub (L ,, S⋆) σ) (branching-path-to-path P) ≃stm (unbiased-comp′ (height-of-branching P) T >>=
                                                                            proj₁ (label-sub (M ,, S⋆) σ) ,, S⋆)
      lem = begin
        < stm-sub (L (branching-path-to-path P)) σ >stm
          ≈⟨ stm-sub-≃ p σ ⟩
        < stm-sub (unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆) σ >stm
          ≈⟨ stm-sub-extend (unbiased-comp′ (height-of-branching P) T) (M ,, S⋆) σ ⟩
        < unbiased-comp′ (height-of-branching P) T >>= label-sub (M ,, S⋆) σ >stm ∎
        where
          open Reasoning stm-setoid
      open Reasoning stm-setoid-≈
