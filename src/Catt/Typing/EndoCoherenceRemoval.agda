open import Catt.Typing.Base

module Catt.Typing.EndoCoherenceRemoval {index : Set} (rule : index → Rule) where

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
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Path
open import Catt.Suspension

HasEndoCoherenceRemoval : Set
HasEndoCoherenceRemoval = ∀ {m n}
                        → {Γ : Ctx m}
                        → {X : MaybeTree m}
                        → (S : Tree n)
                        → (s : STm (someTree S))
                        → (As : STy (someTree S))
                        → (L : Label X S)
                        → Typing-STm (tree-to-ctx S) s As
                        → Typing-STy (tree-to-ctx S) As
                        → Typing-Label Γ (L ,, S⋆)
                        → SCoh S (SArr s As s) (L ,, S⋆) ≈[ Γ ]stm (identity-stm (sty-dim As) >>= label-wt-comp (label-from-linear-tree (n-disc (sty-dim As)) ⦃ n-disc-is-linear (sty-dim As) ⦄ s As (≤-reflexive (tree-dim-n-disc (sty-dim As))) ,, S⋆) (L ,, S⋆))

module Conditions (ecr : HasEndoCoherenceRemoval) where

  lift-rule : ∀ {m n}
            → {Γ : Ctx m}
            → {A : Ty m}
            → (S : Tree n)
            → (s : STm (someTree S))
            → (As : STy (someTree S))
            → (L : Label (Other m) S)
            → Typing-STm (tree-to-ctx S) s As
            → Typing-STy (tree-to-ctx S) As
            → Typing-Label (Γ , A) (lift-label (L ,, S⋆))
            → lift-stm (SCoh S (SArr s As s) (L ,, S⋆)) ≈[ Γ , A ]stm lift-stm ((identity-stm (sty-dim As) >>= label-wt-comp (label-from-linear-tree (n-disc (sty-dim As)) ⦃ n-disc-is-linear (sty-dim As) ⦄ s As (≤-reflexive (tree-dim-n-disc (sty-dim As))) ,, S⋆) (L ,, S⋆)))
  lift-rule S s As L sty Asty Lty = begin
    SCoh S (SArr s As s) (lift-label (L ,, S⋆))
      ≈⟨ ecr S s As (ap (lift-label (L ,, S⋆))) sty Asty Lty ⟩
    (identity-stm (sty-dim As) >>=
      label-wt-comp
      (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
      (lift-label (L ,, S⋆)))
      ≈⟨ reflexive≈stm (extend-≃ (refl≃stm {a = identity-stm (sty-dim As)})
                       (label-comp-lift (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _) (L ,, S⋆))
                       refl≃sty) ⟩
    (identity-stm (sty-dim As) >>=
      lift-label
      (label-wt-comp
       (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
       (L ,, S⋆)))
      ≈⟨ reflexive≈stm (extend-lift (identity-stm (sty-dim As)) _) ⟩
    (lift-stm
       (identity-stm (sty-dim As) >>=
        label-wt-comp
        (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
        (L ,, S⋆))) ∎
    where
      open Reasoning stm-setoid-≈

  susp-rule : ∀ {m n}
            → {Γ : Ctx m}
            → {X : MaybeTree m}
            → (S : Tree n)
            → (s : STm (someTree S))
            → (As : STy (someTree S))
            → (L : Label (Other m) S)
            → Typing-STm (tree-to-ctx (suspTree S)) (susp-stm s) (susp-sty As)
            → Typing-STy (tree-to-ctx (suspTree S)) (susp-sty As)
            → Typing-Label (suspCtx Γ) (susp-label-full L ,, S⋆)
            → susp-stm (SCoh S (SArr s As s) (L ,, S⋆)) ≈[ suspCtx Γ ]stm susp-stm ((identity-stm (sty-dim As) >>= label-wt-comp (label-from-linear-tree (n-disc (sty-dim As)) ⦃ n-disc-is-linear (sty-dim As) ⦄ s As (≤-reflexive (tree-dim-n-disc (sty-dim As))) ,, S⋆) (L ,, S⋆)))
  susp-rule S s As L sty Asty Lty = begin
    susp-stm (SCoh S (SArr s As s) (L ,, S⋆))
      ≈⟨ reflexive≈stm (susp-stm-SCoh S (SArr s As s) (L ,, S⋆)) ⟩
    SCoh S (SArr s As s) (susp-label (L ,, S⋆))
      ≈⟨ reflexive≈stm (SCoh-unrestrict S (SArr s As s) (susp-label (L ,, S⋆))) ⟩
    SCoh (suspTree S) (susp-sty (SArr s As s)) (susp-label-full L ,, S⋆)
      ≈⟨ ecr (suspTree S) (susp-stm s) (susp-sty As) (susp-label-full L) sty Asty Lty ⟩
    (identity-stm (sty-dim (susp-sty As)) >>=
      label-wt-comp
      (label-from-linear-tree (n-disc (sty-dim (susp-sty As))) ⦃ _ ⦄
       (susp-stm s) (susp-sty As) _
       ,, S⋆)
      (susp-label-full L ,, S⋆))
      ≈˘⟨ reflexive≈stm (extend-assoc (identity-stm (sty-dim (susp-sty As))) (label-from-linear-tree (n-disc (sty-dim (susp-sty As))) ⦃ _ ⦄
       (susp-stm s) (susp-sty As) _ ,, S⋆) (susp-label-full L ,, S⋆)) ⟩
    (identity-stm (sty-dim (susp-sty As)) >>= label-from-linear-tree (n-disc (sty-dim (susp-sty As))) ⦃ _ ⦄
       (susp-stm s) (susp-sty As) (≤-reflexive (tree-dim-n-disc (sty-dim (susp-sty As)))) ,, S⋆ >>= susp-label-full L ,, S⋆)
      ≈⟨ reflexive≈stm (extend-≃ lem refl≃l refl≃sty) ⟩
    (susp-stm
      (identity-stm (sty-dim As) >>=
       label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
      >>= susp-label-full L ,, S⋆)
      ≈˘⟨ reflexive≈stm (extend-susp-label-full (identity-stm (sty-dim As) >>=
       label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆) L) ⟩
    susp-stm
      (identity-stm (sty-dim As) >>=
       label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As (≤-reflexive (tree-dim-n-disc (sty-dim As))) ,, S⋆
       >>= L ,, S⋆)
      ≈⟨ reflexive≈stm (susp-stm-≃ (extend-assoc (identity-stm (sty-dim As)) (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆) (L ,, S⋆))) ⟩
    susp-stm
      (identity-stm (sty-dim As) >>=
       label-wt-comp
       (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
       (L ,, S⋆)) ∎
    where
      lem2 : (p : sty-dim (susp-sty As) ≡ m)
           → (identity-stm (sty-dim (susp-sty As)) >>= label-from-linear-tree (n-disc (sty-dim (susp-sty As))) ⦃ n-disc-is-linear (sty-dim (susp-sty As)) ⦄
                                                       (susp-stm s) (susp-sty As) (≤-reflexive (tree-dim-n-disc (sty-dim (susp-sty As)))) ,, S⋆)
           ≡ (identity-stm m >>= label-from-linear-tree (n-disc m) ⦃ n-disc-is-linear m ⦄
                                                       (susp-stm s) (susp-sty As) (≤-reflexive (trans (tree-dim-n-disc m) (sym p))) ,, S⋆)
      lem2 refl = refl

      lem : (identity-stm (sty-dim (susp-sty As)) >>= label-from-linear-tree (n-disc (sty-dim (susp-sty As))) ⦃ _ ⦄
       (susp-stm s) (susp-sty As) _ ,, S⋆) ≃stm susp-stm
         (identity-stm (sty-dim As) >>=
         label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
      lem = begin
        < identity-stm (sty-dim (susp-sty As))
          >>= label-from-linear-tree (n-disc (sty-dim (susp-sty As))) ⦃ _ ⦄
                                     (susp-stm s) (susp-sty As) _ ,, S⋆ >stm
          ≈⟨ reflexive≃stm (lem2 (susp-sty-dim As)) ⟩
        < identity-stm (suc (sty-dim As)) >>= label-from-linear-tree (n-disc (suc (sty-dim As))) ⦃ n-disc-is-linear (suc (sty-dim As)) ⦄ (susp-stm s) (susp-sty As) (≤-reflexive (trans (cong suc (tree-dim-n-disc (sty-dim As))) (sym (susp-sty-dim As)))) ,, S⋆ >stm
          ≈⟨ extend-≃ (refl≃stm {a = identity-stm (suc (sty-dim As))}) (label-from-linear-tree-susp-full (n-disc (sty-dim As)) ⦃ _ ⦄ s As (tree-dim-n-disc (sty-dim As))) refl≃sty ⟩
        < susp-stm (identity-stm (sty-dim As)) >>= susp-label-full (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _) ,, S⋆ >stm
          ≈˘⟨ extend-susp-label-full (identity-stm (sty-dim As)) (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _) ⟩
        < susp-stm
         (identity-stm (sty-dim As) >>=
         label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆) >stm ∎
        where
          open Reasoning stm-setoid
      open Reasoning stm-setoid-≈

  sub-rule : ∀ {m n l}
           → {Γ : Ctx l}
           → {Δ : Ctx m}
           → {X : MaybeTree m}
           → (S : Tree n)
           → (s : STm (someTree S))
           → (As : STy (someTree S))
           → (L : Label (Other m) S)
           → (σ : Sub m l ⋆)
           → Typing-STm (tree-to-ctx S) s As
           → Typing-STy (tree-to-ctx S) As
           → Typing-Label Γ (label-sub (L ,, S⋆) σ)
           → stm-sub (SCoh S (SArr s As s) (L ,, S⋆)) σ ≈[ Γ ]stm stm-sub ((identity-stm (sty-dim As) >>= label-wt-comp (label-from-linear-tree (n-disc (sty-dim As)) ⦃ n-disc-is-linear (sty-dim As) ⦄ s As (≤-reflexive (tree-dim-n-disc (sty-dim As))) ,, S⋆) (L ,, S⋆))) σ
  sub-rule S s As L σ sty Asty Lty = begin
    stm-sub (SCoh S (SArr s As s) (L ,, S⋆)) σ
      ≈⟨ reflexive≈stm (stm-sub-SCoh S (SArr s As s) (L ,, S⋆) σ) ⟩
    SCoh S (SArr s As s) (label-sub (L ,, S⋆) σ)
      ≈⟨ ecr S s As (ap (label-sub (L ,, S⋆) σ)) sty Asty Lty ⟩
    (identity-stm (sty-dim As) >>=
      label-wt-comp
      (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
      (label-sub (L ,, S⋆) σ))
      ≈˘⟨ reflexive≈stm (extend-≃ (refl≃stm {a = identity-stm (sty-dim As)}) (label-sub-comp (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _) (L ,, S⋆) σ) refl≃sty) ⟩
    (identity-stm (sty-dim As) >>=
      label-sub
      (label-wt-comp
       (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
       (L ,, S⋆))
      σ)
      ≈˘⟨ reflexive≈stm (stm-sub-extend (identity-stm (sty-dim As)) _ σ) ⟩
    stm-sub
       (identity-stm (sty-dim As) >>=
        label-wt-comp
        (label-from-linear-tree (n-disc (sty-dim As)) ⦃ _ ⦄ s As _ ,, S⋆)
        (L ,, S⋆))
       σ ∎
    where
      open Reasoning stm-setoid-≈
