open import Catt.Typing.Rule

module Catt.Support.Typing (ops : Op) (rules : RuleSet) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Suspension.Support
open import Catt.Support
open import Catt.Support.Properties

open import Catt.Typing.Rule.Properties ops

rulesWithSupp : RuleSet
rulesWithSupp r = rules r × SuppTm tgtCtx lhs ≡ SuppTm tgtCtx rhs
  where
    open Rule r

rulesWithSupp⊆ : rulesWithSupp ⊆r rules
rulesWithSupp⊆ [ p ,, _ ] = [ p ]

module _ where
  open import Catt.Typing ops rulesWithSupp
  open ≡-Reasoning

  rulesWithSupp-supp : SupportCond ops rulesWithSupp
  rulesWithSupp-supp [ p ,, supp ] tty = supp

  rulesWithSupp-wk : WkCond rules → WkCond rulesWithSupp
  rulesWithSupp-wk p A [ x ,, supp ] .get .proj₁ = p A [ x ] .get
  rulesWithSupp-wk p {r = r} A [ x ,, supp ] .get .proj₂ = begin
    SuppTm (tgtCtx , A) (wk-tm lhs)
      ≡⟨ cong (DC _) (supp-wk-tm lhs) ⟩
    ewf (SuppTm tgtCtx lhs)
      ≡⟨ cong ewf supp ⟩
    ewf (SuppTm tgtCtx rhs)
      ≡˘⟨ cong (DC _) (supp-wk-tm rhs) ⟩
    SuppTm (tgtCtx , A) (wk-tm rhs) ∎
    where
      open Rule r

  rulesWithSupp-susp : SuspCond rules → SuspCond rulesWithSupp
  rulesWithSupp-susp p [ x ,, supp ] .get .proj₁ = p [ x ] .get
  rulesWithSupp-susp p {r = r} [ x ,, supp ] .get .proj₂ = begin
    SuppTm (susp-ctx tgtCtx) (susp-tm lhs)
      ≡⟨ susp-SuppTm′ tgtCtx lhs ⟩
    susp-supp (SuppTm tgtCtx lhs)
      ≡⟨ cong susp-supp supp ⟩
    susp-supp (SuppTm tgtCtx rhs)
      ≡˘⟨ susp-SuppTm′ tgtCtx rhs ⟩
    SuppTm (susp-ctx tgtCtx) (susp-tm rhs) ∎
    where
      open Rule r

  rulesWithSupp-sub : SubCond ops rules → SubCond ops rulesWithSupp
  rulesWithSupp-sub p Γ σty [ x ,, supp ] .get .proj₁ = p Γ (Typing-Sub-⊆ rulesWithSupp⊆ σty) [ x ] .get
  rulesWithSupp-sub p {r = r} Γ {σ = σ} σty [ x ,, supp ] .get .proj₂ = begin
    SuppTm Γ (lhs [ σ ]tm)
      ≡˘⟨ cong (DC Γ) (vs-sub-tm lhs σ) ⟩
    DC Γ (FVTm lhs [ σ ]vs)
      ≡⟨ vs-sub-DC (FVTm lhs) σty ⟩
    SuppTm tgtCtx lhs [ σ ]vs
      ≡⟨ cong (_[ σ ]vs) supp ⟩
    SuppTm tgtCtx rhs [ σ ]vs
      ≡˘⟨ vs-sub-DC (FVTm rhs) σty ⟩
    DC Γ (FVTm rhs [ σ ]vs)
      ≡⟨ cong (DC Γ) (vs-sub-tm rhs σ) ⟩
    SuppTm Γ (rhs [ σ ]tm) ∎
    where
      open Rule r
      open import Catt.Typing.Properties.Support ops rulesWithSupp rulesWithSupp-supp

  open Tame

  rulesWithSupp-tame : Tame ops rules → Tame ops rulesWithSupp
  rulesWithSupp-tame p .tame-op = p .tame-op
  rulesWithSupp-tame p .wk-cond = rulesWithSupp-wk (p .wk-cond)
  rulesWithSupp-tame p .susp-cond = rulesWithSupp-susp (p .susp-cond)
  rulesWithSupp-tame p .sub-cond = rulesWithSupp-sub (p .sub-cond)

module _ (supp-cond : SupportCond′ ops rulesWithSupp rules) where
  open import Catt.Typing

  SupportCond-≈tm : _≈[_]tm_ ops rules s Γ t → _≈[_]tm_ ops rulesWithSupp s Γ t
  SupportCond-≈ty : _≈[_]ty_ ops rules A Γ B → _≈[_]ty_ ops rulesWithSupp A Γ B
  SupportCond-≈s : _≈[_]s_ ops rules σ Γ τ → _≈[_]s_ ops rulesWithSupp σ Γ τ
  SupportCond-Tm : Typing-Tm ops rules Γ t A → Typing-Tm ops rulesWithSupp Γ t A
  SupportCond-Ty : Typing-Ty ops rules Γ A → Typing-Ty ops rulesWithSupp Γ A
  SupportCond-Sub : Typing-Sub ops rules Γ Δ σ → Typing-Sub ops rulesWithSupp Γ Δ σ

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
  SupportCond-Tm (TyCoh supp Aty σty) = TyCoh supp (SupportCond-Ty Aty) (SupportCond-Sub σty)

  SupportCond-Ty TyStar = TyStar
  SupportCond-Ty (TyArr sty Aty tty) = TyArr (SupportCond-Tm sty) (SupportCond-Ty Aty) (SupportCond-Tm tty)

  SupportCond-Sub (TyNull Aty) = TyNull (SupportCond-Ty Aty)
  SupportCond-Sub (TyExt σty tty) = TyExt (SupportCond-Sub σty) (SupportCond-Tm tty)

  SupportCond-prop : SupportCond ops rules
  SupportCond-prop q tty = supp-cond q (SupportCond-Tm tty)
