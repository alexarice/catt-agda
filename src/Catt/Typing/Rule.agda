module Catt.Typing.Rule where

open import Catt.Prelude
open import Data.Sum
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Suspension

record Rule : Set where
  field
    len : ℕ
    tgtCtx : Ctx len
    lhs : Tm len
    rhs : Tm len

open Rule

RuleSet : Set₁
RuleSet = Σ[ idx ∈ Set ] (idx → Rule)

record _≃r_ (r₁ r₂ : Rule) : Set where
  field
    ctxeq : r₁ .tgtCtx ≃c r₂ .tgtCtx
    lhseq : r₁ .lhs ≃tm r₂ .lhs
    rhseq : r₁ .rhs ≃tm r₂ .rhs

_∈r_ : Rule → RuleSet → Set
r ∈r (idx ,, rule) = Σ[ i ∈ idx ] r ≃r rule i

open Rule
open _≃r_ public

refl≃r : ∀ {r} → r ≃r r
refl≃r .ctxeq = refl≃c
refl≃r .lhseq = refl≃tm
refl≃r .rhseq = refl≃tm

sym≃r : ∀ {r r′} → r ≃r r′ → r′ ≃r r
sym≃r p .ctxeq = sym≃c (p .ctxeq)
sym≃r p .lhseq = sym≃tm (p .lhseq)
sym≃r p .rhseq = sym≃tm (p .rhseq)

trans≃r : ∀ {r r′ r″} → r ≃r r′ → r′ ≃r r″ → r ≃r r″
trans≃r p q .ctxeq = trans≃c (p .ctxeq) (q .ctxeq)
trans≃r p q .lhseq = trans≃tm (p .lhseq) (q .lhseq)
trans≃r p q .rhseq = trans≃tm (p .rhseq) (q .rhseq)

infix 60 _∪r_
_∪r_ : RuleSet → RuleSet → RuleSet
(idx₁ ,, rule₁) ∪r (idx₂ ,, rule₂) = (idx₁ ⊎ idx₂) ,, [ rule₁ , rule₂ ]′

∈r-≃ : ∀ {r₁ r₂} → r₁ ≃r r₂ → {rs : RuleSet} → r₁ ∈r rs → r₂ ∈r rs
∈r-≃ p (i ,, q) = i ,, trans≃r (sym≃r p) q

∪r-∈-1 : (r : Rule) → (rs rs′ : RuleSet) → r ∈r rs → r ∈r rs ∪r rs′
∪r-∈-1 r rs rs′ (i ,, p) = (inj₁ i) ,, p

∪r-∈-2 : (r : Rule) → (rs rs′ : RuleSet) → r ∈r rs′ → r ∈r rs ∪r rs′
∪r-∈-2 r rs rs′ (i ,, p) = (inj₂ i) ,, p

rule-cond : (rs : RuleSet) → (P : Rule → Set) → Set
rule-cond rs@(idx ,, rule) P = (i : idx) → P (rule i)

rule-cond-prop : {r : Rule} → (rs : RuleSet) → (P : Rule → Set) → rule-cond rs P → r ∈r rs → P r
rule-cond-prop rs P p (i ,, record { ctxeq = ctxeq ; lhseq = lhseq ; rhseq = rhseq }) with ≃c-preserve-length ctxeq
... | refl with ≃c-to-≡ ctxeq | ≃tm-to-≡ lhseq | ≃tm-to-≡ rhseq
... | refl | refl | refl = p i

lift-rule : (r : Rule) → Ty (r .len) → Rule
lift-rule r A .len = suc (r .len)
lift-rule r A .tgtCtx = r .tgtCtx , A
lift-rule r A .lhs = lift-tm (r .lhs)
lift-rule r A .rhs = lift-tm (r .rhs)

private
  lift : RuleSet → Rule → Set
  lift rs r = (A : Ty (r .len)) → lift-rule r A ∈r rs

LiftCond : RuleSet → Set
LiftCond rs = rule-cond rs (lift rs)

LiftCond-prop : ∀ {rs r} → LiftCond rs → r ∈r rs → lift rs r
LiftCond-prop {rs} = rule-cond-prop rs (lift rs)

LiftCond-∪ : ∀ {rs rs′} → LiftCond rs → LiftCond rs′ → LiftCond (rs ∪r rs′)
LiftCond-∪ {rs@(idx₁ ,, rule₁)} {rs′@(idx₂ ,, rule₂)} p q (inj₁ i) A = ∪r-∈-1 (lift-rule (rule₁ i) A) rs rs′ (p i A)
LiftCond-∪ {rs@(idx₁ ,, rule₁)} {rs′@(idx₂ ,, rule₂)} p q (inj₂ i) A = ∪r-∈-2 (lift-rule (rule₂ i) A) rs rs′ (q i A)

susp-rule : (r : Rule) → Rule
susp-rule r .len = 2+ (r .len)
susp-rule r .tgtCtx = susp-ctx (r .tgtCtx)
susp-rule r .lhs = susp-tm (r .lhs)
susp-rule r .rhs = susp-tm (r .rhs)

private
  susp : RuleSet → Rule → Set
  susp rs r = susp-rule r ∈r rs

SuspCond : RuleSet → Set
SuspCond rs = rule-cond rs (susp rs)

SuspCond-prop : ∀ {rs r} → SuspCond rs → r ∈r rs → susp rs r
SuspCond-prop {rs} = rule-cond-prop rs (susp rs)

SuspCond-∪ : ∀ {rs rs′} → SuspCond rs → SuspCond rs′ → SuspCond (rs ∪r rs′)
SuspCond-∪ {rs@(idx₁ ,, rule₁)} {rs′@(idx₂ ,, rule₂)} p q (inj₁ i) = ∪r-∈-1 (susp-rule (rule₁ i)) rs rs′ (p i)
SuspCond-∪ {rs@(idx₁ ,, rule₁)} {rs′@(idx₂ ,, rule₂)} p q (inj₂ i) = ∪r-∈-2 (susp-rule (rule₂ i)) rs rs′ (q i)

sub-rule : (r : Rule) → Ctx n → Sub (r .len) n ⋆ → Rule
sub-rule r Γ σ .len = _
sub-rule r Γ σ .tgtCtx = Γ
sub-rule r Γ σ .lhs = r .lhs [ σ ]tm
sub-rule r Γ σ .rhs = r .rhs [ σ ]tm

private
  sub : RuleSet → Rule → Set
  sub rs r = ∀ {n} → (Γ : Ctx n) → (σ : Sub (r .len) n ⋆) → sub-rule r Γ σ ∈r rs

SubCond : RuleSet → Set
SubCond rs = rule-cond rs (sub rs)

SubCond-prop : ∀ {rs r} → SubCond rs → r ∈r rs → sub rs r
SubCond-prop {rs} = rule-cond-prop rs (sub rs)

SubCond-∪ : ∀ {rs rs′} → SubCond rs → SubCond rs′ → SubCond (rs ∪r rs′)
SubCond-∪ {rs@(idx₁ ,, rule₁)} {rs′@(idx₂ ,, rule₂)} p q (inj₁ i) Γ σ = ∪r-∈-1 (sub-rule (rule₁ i) Γ σ) rs rs′ (p i Γ σ)
SubCond-∪ {rs@(idx₁ ,, rule₁)} {rs′@(idx₂ ,, rule₂)} p q (inj₂ i) Γ σ = ∪r-∈-2 (sub-rule (rule₂ i) Γ σ) rs rs′ (q i Γ σ)

record Tame (rs : RuleSet) : Set where
  field
    lift-cond : LiftCond rs
    susp-cond : SuspCond rs
    sub-cond : SubCond rs

open Tame

Tame-∪ : ∀ {rs rs′} → Tame rs → Tame rs′ → Tame (rs ∪r rs′)
Tame-∪ p q .lift-cond = LiftCond-∪ (p .lift-cond) (q .lift-cond)
Tame-∪ p q .susp-cond = SuspCond-∪ (p .susp-cond) (q .susp-cond)
Tame-∪ p q .sub-cond = SubCond-∪ (p .sub-cond) (q .sub-cond)

{-
open import Catt.Support

module _ (r : Rule) where
  open import Catt.Typing rule
  open Rule r

  LiftRule : Set
  LiftRule = (A : Ty len)
           → Σ[ i ∈ index ] rule i .Rule.tgtCtx ≃c tgtCtx , A
                          × rule i .Rule.lhs ≃tm lift-tm lhs
                          × rule i .Rule.rhs ≃tm lift-tm rhs  -- {A : Ty len}
           -- → {C : Ty len}
           -- → Typing-Tm (tgtCtx , A) (lift-tm lhs) (lift-ty C)
           -- → (lift-tm lhs) ≈[ tgtCtx , A ]tm (lift-tm rhs)

  SuspRule : Set
  SuspRule = {C : Ty len}
           → Typing-Tm (susp-ctx tgtCtx) (susp-tm lhs) (susp-ty C)
           → susp-tm lhs ≈[ susp-ctx tgtCtx ]tm susp-tm rhs

  SubRule : Set
  SubRule = ∀ {n}
          → {σ : Sub len n ⋆}
          → {Δ : Ctx n}
          → {C : Ty len}
          → Typing-Sub tgtCtx Δ σ
          → Typing-Tm Δ (lhs [ σ ]tm) (C [ σ ]ty)
          → lhs [ σ ]tm ≈[ Δ ]tm rhs [ σ ]tm

  ConvRule : Set
  ConvRule = {A : Ty len}
           → Typing-Tm tgtCtx lhs A
           → Typing-Tm tgtCtx rhs A

  SupportRule : Set
  SupportRule = {A : Ty len}
              → (tty : Typing-Tm tgtCtx lhs A)
              → SuppTm tgtCtx lhs ≡ SuppTm tgtCtx rhs
-}
