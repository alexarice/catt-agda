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
