module Catt.Typing.Strict.UA where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Discs
open import Catt.Tree
open import Catt.Tree.Path.Properties
open import Catt.Tree.Canonical
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
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
         → (P : Branch S l)
         → (T : Tree n′)
         → .⦃ _ : has-trunk-height l T ⦄
         → (M : Label (Other m) T)
         → L ⌊ P ⌋p ≃stm canonical-comp′ (ih P) T >>= (M ,, S⋆)
         → Index

module _ where
  open import Catt.Typing.DiscRemoval.Base
  open import Catt.Typing.EndoCoherenceRemoval.Base
  open Catt.Typing.Insertion.Base

  SUA-Rules : Index → Rule
  SUA-Rules (DR Γ σ) = DiscRemoval Γ σ
  SUA-Rules (ECR Γ Δ s A σ) = EndoCoherenceRemoval Γ Δ s A σ
  SUA-Rules (Insert Γ S As L P T M p) = Insertion Γ S As L P T M

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

hasInsertion : HasInsertion
hasInsertion {l = l} {S = S} As L P {T = T} M p [ tty ] = [ begin
  stm-to-term (SCoh S As (L ,, S⋆))
    ≈˘⟨ reflexive≈tm (stm-to-other-prop (SCoh S As (L ,, S⋆)) .get) ⟩
  stm-to-term (SCoh S As (label-to-other L ,, S⋆))
    ≈⟨ Rule≈ (Insert _ S As (label-to-other L) P T (label-to-other M) lem)
             (transport-typing tty (sym≃tm (stm-to-other-prop (SCoh S As (L ,, S⋆)) .get))) ⟩
  stm-to-term (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (label-to-other L >>l[ P ] label-to-other M ,, S⋆))
    ≈˘⟨ reflexive≈tm (SCoh≃ (S >>[ P ] T)
                            (refl≃sty {A = As >>=′ (κ S P T ,, S⋆)})
                            (label-from-insertion-map stm-to-other L P M)
                            (refl≃sty {A = S⋆}) .get) ⟩
  stm-to-term (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (label-to-other (L >>l[ P ] M) ,, S⋆))
    ≈⟨ reflexive≈tm (stm-to-other-prop (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆)) .get) ⟩
  stm-to-term (SCoh (S >>[ P ] T) (As >>=′ (κ S P T ,, S⋆)) (L >>l[ P ] M ,, S⋆)) ∎ ]
  where
    lem : label-to-other L ⌊ P ⌋p
          ≃stm
          canonical-comp′ (ih P) T >>= (label-to-other M ,, S⋆)
    lem = begin
      < label-to-other L ⌊ P ⌋p >stm
        ≈⟨ ap-≃ (label-to-other-prop L) refl≃p ⟩
      < L ⌊ P ⌋p >stm
        ≈⟨ p ⟩
      < canonical-comp′ (ih P) T >>= (M ,, S⋆) >stm
        ≈˘⟨ >>=-≃ (refl≃stm {a = canonical-comp′ (ih P) T}) (label-to-other-prop M) (sty-to-other-prop S⋆) ⟩
      < canonical-comp′ (ih P) T >>= (label-to-other M ,, S⋆) >stm ∎
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
sua-lift-rule (Insert Γ S As L P T M p) = lift-rule P p
  where
    open I.Conditions hasInsertion

sua-susp-rule : (i : Index) → SuspRule (SUA-Rules i)
sua-susp-rule (DR Γ σ) = susp-rule
  where
    open D.Conditions hasDiscRemoval
sua-susp-rule (ECR Γ Δ s A σ) = susp-rule
  where
    open E.Conditions hasEndoCoherenceRemoval
sua-susp-rule (Insert Γ S As L P T M p) = susp-rule P p
  where
    open I.Conditions hasInsertion

sua-sub-rule : (i : Index) → SubRule (SUA-Rules i)
sua-sub-rule (DR Γ σ) = sub-rule
  where
    open D.Conditions hasDiscRemoval
sua-sub-rule (ECR Γ Δ s A σ) = sub-rule
  where
    open E.Conditions hasEndoCoherenceRemoval
sua-sub-rule (Insert Γ S As L P T M p) = sub-rule P p
  where
    open I.Conditions hasInsertion
