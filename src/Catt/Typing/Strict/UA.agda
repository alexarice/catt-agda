module Catt.Typing.Strict.UA where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Discs
open import Catt.Tree
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Unbiased
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Typing.Base

import Catt.Typing.Insertion.Base

data Index : Set where
  DR : .⦃ NonZero n ⦄ → (Γ : Ctx m) → (σ : Sub (disc-size n) m ⋆) → Index
  ECR : (Γ : Ctx m) → (Δ : Ctx (suc n)) → (s : Tm (suc n)) → (A : Ty (suc n)) → (σ : Sub (suc n) m ⋆) → Index
  Insert : (Γ : Ctx m)
         → (S : Tree n)
         → (As : STy (someTree S))
         → (L : Label (Other m) S)
         → (P : BranchingPoint S l)
         → (T : Tree n′)
         → .⦃ _ : has-linear-height l T ⦄
         → (M : Label (Other m) T)
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
  SUA-Rules (Insert Γ S As L P T M pf p) = Insertion Γ S As L P T M

open import Catt.Typing SUA-Rules public
open import Catt.Typing.DiscRemoval SUA-Rules as D
open import Catt.Typing.EndoCoherenceRemoval SUA-Rules as E
open import Catt.Typing.Insertion SUA-Rules as I
open import Catt.Typing.Properties.Base SUA-Rules

open import Catt.Typing.Rule SUA-Rules

hasDiscRemoval : HasDiscRemoval
hasDiscRemoval tty = Rule≈ (DR _ _) tty

hasEndoCoherenceRemoval : HasEndoCoherenceRemoval
hasEndoCoherenceRemoval tty = Rule≈ (ECR _ _ _ _ _) tty

hasInsertion : HasSUAInsertion
hasInsertion {S = S} {As = As} {L = L} P {T = T} {M = M} pf p [ tty ] = [ begin
  stm-to-term (SCoh S As (L ,, S⋆))
    ≈˘⟨ reflexive≈tm (stm-to-other-prop (SCoh S As (L ,, S⋆)) .get) ⟩
  stm-to-term (SCoh S As (label-to-other L ,, S⋆))
    ≈⟨ Rule≈ (Insert _ S As (label-to-other L) P T (label-to-other M) lem p) (transport-typing tty (sym≃tm (stm-to-other-prop (SCoh S As (L ,, S⋆)) .get))) ⟩
  stm-to-term (SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) ((sub-from-insertion-label S P T (label-to-other L) (label-to-other M)) ,, S⋆))
    ≈˘⟨ reflexive≈tm (≃SCoh (insertion-tree S P T) (refl≃sty {A = label-on-sty As (exterior-sub-label S P T ,, S⋆)}) (sub-from-insertion-label-map stm-to-other S P T L M) (refl≃sty {A = S⋆}) .get) ⟩
  stm-to-term
    (SCoh (insertion-tree S P T)
     (label-on-sty As (exterior-sub-label S P T ,, S⋆))
     (label-to-other (sub-from-insertion-label S P T L M) ,, S⋆))
    ≈⟨ reflexive≈tm (stm-to-other-prop (SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)) .get) ⟩
  stm-to-term (SCoh (insertion-tree S P T) (label-on-sty As (exterior-sub-label S P T ,, S⋆)) (sub-from-insertion-label S P T L M ,, S⋆)) ∎ ]
  where
    lem : label-to-other L (branching-path-to-path P) ≃stm
           (unbiased-comp′ (height-of-branching P) T >>=
            label-to-other M ,, S⋆)
    lem = begin
      < label-to-other L (branching-path-to-path P) >stm
        ≈⟨ ap-≃ (label-to-other-prop L) refl≃p ⟩
      < L (branching-path-to-path P) >stm
        ≈⟨ pf ⟩
      < unbiased-comp′ (height-of-branching P) T >>= M ,, S⋆ >stm
        ≈˘⟨ extend-≃ (refl≃stm {a = unbiased-comp′ (height-of-branching P) T}) (label-to-other-prop M) [ (refl≃ty {A = ⋆}) ] ⟩
      < unbiased-comp′ (height-of-branching P) T >>= label-to-other M ,, S⋆ >stm ∎
      where
        open Reasoning stm-setoid

    open Reasoning (tm-setoid-≈ _)

sua-lift-rule : (i : Index) → LiftRule (SUA-Rules i)
sua-lift-rule (DR Γ σ) = lift-rule
  where
    open D.Conditions hasDiscRemoval
sua-lift-rule (ECR Γ Δ s A σ) = lift-rule
  where
    open E.Conditions hasEndoCoherenceRemoval
sua-lift-rule (Insert Γ S As L P T M pf p) = lift-rule P pf p
  where
    open I.Conditions hasInsertion

sua-susp-rule : (i : Index) → SuspRule (SUA-Rules i)
sua-susp-rule (DR Γ σ) = susp-rule
  where
    open D.Conditions hasDiscRemoval
sua-susp-rule (ECR Γ Δ s A σ) = susp-rule
  where
    open E.Conditions hasEndoCoherenceRemoval
sua-susp-rule (Insert Γ S As L P T M pf p) = susp-rule P pf p
  where
    open I.Conditions hasInsertion

sua-sub-rule : (i : Index) → SubRule (SUA-Rules i)
sua-sub-rule (DR Γ σ) = sub-rule
  where
    open D.Conditions hasDiscRemoval
sua-sub-rule (ECR Γ Δ s A σ) = sub-rule
  where
    open E.Conditions hasEndoCoherenceRemoval
sua-sub-rule (Insert Γ S As L P T M pf p) = sub-rule P pf p
  where
    open I.Conditions hasInsertion
