open import Catt.Typing.Rule
open import Catt.Dyck.Pruning.Ops

module Catt.Typing.Pruning.Typed (ops : Op)
                                 (standard-op : StandardOp ops)
                                 (pruning-op : PruningOp ops)
                                 (rules : RuleSet)
                                 (lift-cond : LiftCond rules)
                                 (sub-cond : SubCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Discs
open import Catt.Dyck
open import Catt.Dyck.Pasting
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Properties
open import Catt.Support
open import Catt.Support.Properties

open import Catt.Typing.Pruning.Rule

open import Catt.Typing ops rules
open import Catt.Dyck.Pruning.Typing ops standard-op rules lift-cond sub-cond
open import Catt.Typing.Properties.Base ops rules
open import Catt.Typing.Properties.Substitution ops rules lift-cond sub-cond
open import Catt.Globular.Typing ops rules

open import Catt.Typing.Weak ops

pruning-conv : ConvCond′ ops rules PruningSet
pruning-conv [ Prune Γ dy ⋆ p σ B t pf ] {A = C} tty = ⊥-elim (NonZero-⊥ z≤n ⦃ coh-nonZero tty ⦄)
pruning-conv [ Prune Γ dy A@(src ─⟨ _ ⟩⟶ tgt) p σ B t pf ] {A = C} tty
  = TyConv (TyCoh ⦃ dyck-to-pd (dy // p) ⦄
                  (subst₂ (ops ⌊ dy // p ⌋d ⦃ dyck-to-pd (dy // p) ⦄)
                          (supp-lem src)
                          (supp-lem tgt)
                          (pruning-op dy p (SuppTm ⌊ dy ⌋d src) (SuppTm ⌊ dy ⌋d tgt) (coh-supp tty)))
                  (apply-sub-ty-typing Aty (π-Ty p))
                  (prune-sub-Ty p σty pf))
           lem
  where
    Aty : Typing-Ty ⌊ dy ⌋d A
    Aty = coh-ty-ty tty

    σty : Typing-Sub ⌊ dy ⌋d _ σ
    σty = coh-sub-ty tty

    lem : (A [ π p ]ty) [ σ //s p ]ty ≈[ Γ ]ty C
    lem = begin
      (A [ π p ]ty) [ σ //s p ]ty
        ≈˘⟨ reflexive≈ty (assoc-ty (π p) (σ //s p) A) ⟩
      A [ π p ● (σ //s p) ]ty
        ≈˘⟨ apply-sub-eq-ty A (prune-Eq p σty pf) ⟩
      A [ σ ]ty
        ≈⟨ tm-to-ty-prop tty ⟩
      C ∎
      where
        open Reasoning (ty-setoid-≈ Γ)

    supp-lem : (s : Tm _)
             → TransportVarSet (SuppTm ⌊ dy ⌋d s) (π p)
               ≡
               SuppTm ⌊ dy // p ⌋d (s [ π p ]tm)
    supp-lem s = begin
      TransportVarSet (SuppTm ⌊ dy ⌋d s) (π p)
        ≡˘⟨ TransportVarSet-DC (FVTm s) (W.π-Ty p) ⟩
      DC ⌊ dy // p ⌋d (TransportVarSet (FVTm s) (π p))
        ≡⟨ cong (DC ⌊ dy // p ⌋d) (TransportVarSet-tm s (π p)) ⟩
      SuppTm ⌊ dy // p ⌋d (s [ π p ]tm) ∎
      where
        open ≡-Reasoning
        open import Catt.Typing.Properties.Support ops Weak-Rules weak-supp
        import Catt.Dyck.Pruning.Typing ops standard-op Weak-Rules weak-lift weak-sub as W
