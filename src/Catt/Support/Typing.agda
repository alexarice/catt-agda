open import Catt.Typing.Rule

module Catt.Support.Typing (rules : RuleSet) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Suspension.Support
open import Catt.Support
open import Catt.Support.Properties

open import Catt.Typing.Rule.Properties

rulesWithSupp : RuleSet
rulesWithSupp r = rules r × SuppTm tgtCtx lhs ≡ SuppTm tgtCtx rhs
  where
    open Rule r

rulesWithSupp⊆ : rulesWithSupp ⊆r rules
rulesWithSupp⊆ [ p ,, _ ] = [ p ]

module _ where
  open import Catt.Typing rulesWithSupp
  open ≡-Reasoning

  rulesWithSupp-supp : SupportCond rulesWithSupp
  rulesWithSupp-supp [ p ,, supp ] tty = supp

  rulesWithSupp-lift : LiftCond rules → LiftCond rulesWithSupp
  rulesWithSupp-lift p A [ x ,, supp ] .get .proj₁ = p A [ x ] .get
  rulesWithSupp-lift p {r = r} A [ x ,, supp ] .get .proj₂ = begin
    SuppTm (tgtCtx , A) (lift-tm lhs)
      ≡⟨ cong (DC _) (supp-lift-tm lhs) ⟩
    ewf (SuppTm tgtCtx lhs)
      ≡⟨ cong ewf supp ⟩
    ewf (SuppTm tgtCtx rhs)
      ≡˘⟨ cong (DC _) (supp-lift-tm rhs) ⟩
    SuppTm (tgtCtx , A) (lift-tm rhs) ∎
    where
      open Rule r

  rulesWithSupp-susp : SuspCond rules → SuspCond rulesWithSupp
  rulesWithSupp-susp p [ x ,, supp ] .get .proj₁ = p [ x ] .get
  rulesWithSupp-susp p {r = r} [ x ,, supp ] .get .proj₂ = begin
    SuppTm (susp-ctx tgtCtx) (susp-tm lhs)
      ≡⟨ suspSuppTm′ tgtCtx lhs ⟩
    suspSupp (SuppTm tgtCtx lhs)
      ≡⟨ cong suspSupp supp ⟩
    suspSupp (SuppTm tgtCtx rhs)
      ≡˘⟨ suspSuppTm′ tgtCtx rhs ⟩
    SuppTm (susp-ctx tgtCtx) (susp-tm rhs) ∎
    where
      open Rule r

  rulesWithSupp-sub : SubCond rules → SubCond rulesWithSupp
  rulesWithSupp-sub p Γ σty [ x ,, supp ] .get .proj₁ = p Γ (Typing-Sub-⊆ rulesWithSupp⊆ σty) [ x ] .get
  rulesWithSupp-sub p {r = r} Γ {σ = σ} σty [ x ,, supp ] .get .proj₂ = begin
    SuppTm Γ (lhs [ σ ]tm)
      ≡˘⟨ cong (DC Γ) (TransportVarSet-tm lhs σ) ⟩
    DC Γ (TransportVarSet (FVTm lhs) σ)
      ≡⟨ TransportVarSet-DC (FVTm lhs) σty ⟩
    TransportVarSet (SuppTm tgtCtx lhs) σ
      ≡⟨ cong (λ - → TransportVarSet - σ) supp ⟩
    TransportVarSet (SuppTm tgtCtx rhs) σ
      ≡˘⟨ TransportVarSet-DC (FVTm rhs) σty ⟩
    DC Γ (TransportVarSet (FVTm rhs) σ)
      ≡⟨ cong (DC Γ) (TransportVarSet-tm rhs σ) ⟩
    SuppTm Γ (rhs [ σ ]tm) ∎
    where
      open Rule r
      open import Catt.Typing.Properties.Support rulesWithSupp rulesWithSupp-supp

  open Tame

  rulesWithSupp-tame : Tame rules → Tame rulesWithSupp
  rulesWithSupp-tame p .lift-cond = rulesWithSupp-lift (p .lift-cond)
  rulesWithSupp-tame p .susp-cond = rulesWithSupp-susp (p .susp-cond)
  rulesWithSupp-tame p .sub-cond = rulesWithSupp-sub (p .sub-cond)

module _ (supp-cond : SupportCond′ rulesWithSupp rules) where
  open import Catt.Typing

  SupportCond-≈tm : _≈[_]tm_ rules s Γ t → _≈[_]tm_ rulesWithSupp s Γ t
  SupportCond-≈ty : _≈[_]ty_ rules A Γ B → _≈[_]ty_ rulesWithSupp A Γ B
  SupportCond-≈s : _≈[_]s_ rules σ Γ τ → _≈[_]s_ rulesWithSupp σ Γ τ
  SupportCond-Tm : Typing-Tm rules Γ t A → Typing-Tm rulesWithSupp Γ t A
  SupportCond-Ty : Typing-Ty rules Γ A → Typing-Ty rulesWithSupp Γ A
  SupportCond-Sub : Typing-Sub rules Γ Δ σ → Typing-Sub rulesWithSupp Γ Δ σ

  SupportCond-≈tm (Var≈ x) = Var≈ x
  SupportCond-≈tm (Sym≈ p) = Sym≈ (SupportCond-≈tm p)
  SupportCond-≈tm (Trans≈ p q) = Trans≈ (SupportCond-≈tm p) (SupportCond-≈tm q)
  SupportCond-≈tm (Coh≈ p q) = Coh≈ (SupportCond-≈ty p) (SupportCond-≈s q)
  SupportCond-≈tm (Rule≈ r [ p ] tty) = Rule≈ r [ p ,, supp-cond [ p ] (SupportCond-Tm tty) ] (SupportCond-Tm tty)

  SupportCond-≈ty Star≈ = Star≈
  SupportCond-≈ty (Arr≈ p q r) = Arr≈ (SupportCond-≈tm p) (SupportCond-≈ty q) (SupportCond-≈tm r)

  SupportCond-≈s (Null≈ x) = Null≈ (SupportCond-≈ty x)
  SupportCond-≈s (Ext≈ p x) = Ext≈ (SupportCond-≈s p) (SupportCond-≈tm x)

  SupportCond-Tm (TyConv tty p) = TyConv (SupportCond-Tm tty) (SupportCond-≈ty p)
  SupportCond-Tm (TyVar i) = TyVar i
  SupportCond-Tm (TyCoh Aty σty) = TyCoh (SupportCond-Ty Aty) (SupportCond-Sub σty)

  SupportCond-Ty TyStar = TyStar
  SupportCond-Ty (TyArr sty Aty tty) = TyArr (SupportCond-Tm sty) (SupportCond-Ty Aty) (SupportCond-Tm tty)

  SupportCond-Sub (TyNull Aty) = TyNull (SupportCond-Ty Aty)
  SupportCond-Sub (TyExt σty tty) = TyExt (SupportCond-Sub σty) (SupportCond-Tm tty)

  SupportCond-prop : SupportCond rules
  SupportCond-prop q tty = supp-cond q (SupportCond-Tm tty)
