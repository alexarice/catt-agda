open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Label.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Path
open import Catt.Suspension
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing index rule lift-rule

data Typing-Label : (Γ : Ctx m) → Label m S → (A : Ty m) → Set where
  TySing : Typing-Tm Γ t A → Typing-Label Γ (LSing t) A
  TyJoin : Typing-Tm Γ t A → Typing-Label Γ L (t ─⟨ A ⟩⟶ first-label M) → Typing-Label Γ M A → Typing-Label Γ (LJoin t L M) A

first-label-Ty : Typing-Label Γ L A → Typing-Tm Γ (first-label L) A
first-label-Ty (TySing tty) = tty
first-label-Ty (TyJoin tty Lty Mty) = tty

label-typing-to-sub : Typing-Label Γ L A → Typing-Ty Γ A → Typing-Sub (tree-to-ctx (label-to-tree L)) Γ (label-to-sub L A)
label-typing-to-sub (TySing tty) Aty = TyExt (TyNull Aty) tty
label-typing-to-sub {A = A} (TyJoin {t = t} {L = L} {M = M} tty Lty Mty) Aty
  = sub-from-connect-Ty (unrestrictTy (label-typing-to-sub Lty (TyArr tty Aty (first-label-Ty Mty)))) getSndTy (label-typing-to-sub Mty Aty) (reflexive≈tm lem)
  where
    open Reasoning tm-setoid
    lem : getSnd [ unrestrict (label-to-sub L (t ─⟨ A ⟩⟶ first-label M)) ]tm
          ≃tm Var (fromℕ _) [ label-to-sub M A ]tm
    lem = begin
      < getSnd [ unrestrict (label-to-sub L (t ─⟨ A ⟩⟶ first-label M)) ]tm >tm
        ≈⟨ unrestrict-snd (label-to-sub L (t ─⟨ A ⟩⟶ first-label M)) ⟩
      < first-label M >tm
        ≈⟨ first-label-prop M A ⟩
      < Var (fromℕ _) [ label-to-sub M A ]tm >tm ∎

label-typing-conv : Typing-Label Γ L A → A ≈[ Γ ]ty B → Typing-Label Γ L B
label-typing-conv (TySing tty) p = TySing (TyConv tty p)
label-typing-conv (TyJoin tty Lty Mty) p = TyJoin (TyConv tty p) (label-typing-conv Lty (Arr≈ refl≈tm p refl≈tm)) (label-typing-conv Mty p)

label-comp-Ty : Typing-Label Γ L A → Typing-Sub Γ Δ σ → Typing-Label Δ (L [ σ ]l) (A [ σ ]ty)
label-comp-Ty (TySing tty) σty = TySing (apply-sub-tm-typing tty σty)
label-comp-Ty {σ = σ} (TyJoin {M = M} tty Lty Mty) σty
  = TyJoin (apply-sub-tm-typing tty σty) (label-typing-conv (label-comp-Ty Lty σty) (reflexive≈ty (Arr≃ refl≃tm refl≃ty (sym≃tm (first-label-comp M σ))))) (label-comp-Ty Mty σty)

suspLabelTy : Typing-Label Γ L A → Typing-Label (suspCtx Γ) (suspLabel L) (suspTy A)
suspLabelTy (TySing tty) = TySing (suspTmTy tty)
suspLabelTy (TyJoin {M = M} tty Lty Mty) =
  TyJoin (suspTmTy tty)
         (label-typing-conv (suspLabelTy Lty) (reflexive≈ty (Arr≃ refl≃tm refl≃ty (sym≃tm (first-label-susp M)))))
         (suspLabelTy Mty)

id-label-Ty : (S : Tree n) → Typing-Label (tree-to-ctx S) (id-label S) ⋆
id-label-Ty Sing = TySing (TyVar 0F)
id-label-Ty (Join S T)
  = TyJoin (transport-typing (apply-sub-tm-typing getFstTy (connect-susp-inc-left-Ty (tree-to-ctx T))) (connect-inc-left-fst-var getSnd _))
           (label-typing-conv (label-comp-Ty (suspLabelTy (id-label-Ty S)) (connect-susp-inc-left-Ty (tree-to-ctx T))) (reflexive≈ty (Arr≃ (connect-inc-left-fst-var getSnd _) refl≃ty lem)))
           (label-comp-Ty (id-label-Ty T) (connect-susp-inc-right-Ty (tree-to-ctx S)))
  where
    open Reasoning tm-setoid
    lem : getSnd [ connect-susp-inc-left _ _ ]tm
          ≃tm first-label (id-label T [ connect-susp-inc-right _ _ ]l)
    lem = begin
      < getSnd [ connect-susp-inc-left _ _ ]tm >tm
        ≈⟨ connect-inc-fst-var getSnd _ ⟩
      < Var (fromℕ _) [ connect-susp-inc-right _ _ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (id-first-label T) refl≃s ⟩
      < first-label (id-label T) [ connect-susp-inc-right _ _ ]tm >tm
        ≈˘⟨ first-label-comp (id-label T) (connect-susp-inc-right _ _) ⟩
      < first-label (id-label T [ connect-susp-inc-right _ _ ]l) >tm ∎

to-label-Ty : (S : Tree n) → Typing-Sub (tree-to-ctx S) Δ σ → Typing-Label Δ (to-label S σ) (sub-type σ)
to-label-Ty S σty = label-comp-Ty (id-label-Ty S) σty

label-maximal-equality : Typing-Label Γ L A → Typing-Label Γ M B → Same-Leaves L M → label-to-sub L A ≈[ Γ ]s label-to-sub M B
label-maximal-equality (TySing sty) (TySing tty) f = Ext≈ (Null≈ (Ty-unique-≃ (f PHere) sty tty)) (reflexive≈tm (f PHere))
label-maximal-equality (TyJoin {M = LSing x} sty Lty Mty) (TyJoin {M = LSing x₁} tty Lty′ Mty′) f = unrestrictEq (label-maximal-equality Lty Lty′ (Same-Leaves-proj₁ f))
label-maximal-equality (TyJoin {M = LJoin x M M₁} sty Lty Mty) (TyJoin {M = LJoin x₁ M′ M′₁} tty Lty′ Mty′) f = sub-from-connect-≈ (unrestrictEq (label-maximal-equality Lty Lty′ (Same-Leaves-proj₁ f))) (label-maximal-equality Mty Mty′ (Same-Leaves-proj₂ f))

sub-maximal-equality : Typing-Sub (tree-to-ctx S) Γ σ → Typing-Sub (tree-to-ctx S) Γ τ → (∀ (P : Path S) → .⦃ is-Maximal P ⦄ → path-to-var P [ σ ]tm ≃tm path-to-var P [ τ ]tm) → σ ≈[ Γ ]s τ
sub-maximal-equality {S = S} {Γ = Γ} {σ = σ} {τ = τ} σty τty f = begin
  < σ >s′
    ≈˘⟨ reflexive≈s (sub-to-label-to-sub S σ) ⟩
  < label-to-sub (to-label S σ) (sub-type σ) >s′
    ≈⟨ label-maximal-equality (to-label-Ty S σty) (to-label-Ty S τty) lem ⟩
  < label-to-sub (to-label S τ) (sub-type τ) >s′
    ≈⟨ reflexive≈s (sub-to-label-to-sub S τ) ⟩
  < τ >s′ ∎
  where
    lem : (P : Path S) → .⦃ is-Maximal P ⦄ → (to-label S σ ‼l P) ≃tm (to-label S τ ‼l P)
    lem P = begin
      < to-label S σ ‼l P >tm
        ≈⟨ ‼l-prop-2 σ P ⟩
      < path-to-var P [ σ ]tm >tm
        ≈⟨ f P ⟩
      < path-to-var P [ τ ]tm >tm
        ≈˘⟨ ‼l-prop-2 τ P ⟩
      < to-label S τ ‼l P >tm ∎
      where
        open Reasoning tm-setoid

    open Reasoning (sub-setoid-≈ (suc (tree-size S)) Γ)
