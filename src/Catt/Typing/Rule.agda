module Catt.Typing.Rule where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Catt.Suspension.Support
open import Catt.Pasting
open import Catt.Support

open import Catt.Ops public
open import Catt.Typing.Base public

open Rule

record _≃r_ (r₁ r₂ : Rule) : Set where
  field
    ctxeq : r₁ .tgtCtx ≃c r₂ .tgtCtx
    lhseq : r₁ .lhs ≃tm r₂ .lhs
    rhseq : r₁ .rhs ≃tm r₂ .rhs

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

≃r-to-≡ : ∀ {r₁ r₂} → r₁ ≃r r₂ → r₁ ≡ r₂
≃r-to-≡ p with ≃c-preserve-length (p .ctxeq)
... | refl with ≃c-to-≡ (p .ctxeq) | ≃tm-to-≡ (p .lhseq) | ≃tm-to-≡ (p .rhseq)
... | refl | refl | refl = refl

infixr 60 _∪r_
_∪r_ : RuleSet → RuleSet → RuleSet
rules₁ ∪r rules₂ = λ r → r ∈r rules₁ ⊎ r ∈r rules₂

∈r-≃ : ∀ {r₁ r₂ rs} → r₁ ∈r rs → r₁ ≃r r₂ → r₂ ∈r rs
∈r-≃ {rs = rs} p q = subst (_∈r rs) (≃r-to-≡ q) p

_⊆r_ : RuleSet → RuleSet → Set
rs ⊆r rs′ = ∀ {r} → r ∈r rs → r ∈r rs′

⊆r-refl : ∀ {rs} → rs ⊆r rs
⊆r-refl x = x

⊆r-trans : ∀ {rs rs′ rs″} → rs ⊆r rs′ → rs′ ⊆r rs″ → rs ⊆r rs″
⊆r-trans p q x = q (p x)

⊆r-∪-1 : ∀ {rs rs′} → rs ⊆r rs ∪r rs′
⊆r-∪-1 x = [ inj₁ x ]

⊆r-∪-2 : ∀ {rs rs′} → rs′ ⊆r rs ∪r rs′
⊆r-∪-2 x = [ inj₂ x ]

-- Conditions

SuspOp : Op → Set
SuspOp ops = ∀ {n} (Γ : Ctx n) .⦃ _ : Γ ⊢pd ⦄ (xs ys : VarSet n)
           → ops Γ xs ys
           → ops (susp-ctx Γ) (suspSupp xs) (suspSupp ys)

StandardOp : Op → Set
StandardOp ops = ∀ {n} (Γ : Ctx n) .⦃ _ : Γ ⊢pd ⦄ (d : ℕ) (p : suc d ≥ ctx-dim Γ)
               → ops Γ (pd-bd-supp d Γ false) (pd-bd-supp d Γ true)

wk-rule : (r : Rule) → Ty (r .len) → Rule
wk-rule r A .len = suc (r .len)
wk-rule r A .tgtCtx = r .tgtCtx , A
wk-rule r A .lhs = wk-tm (r .lhs)
wk-rule r A .rhs = wk-tm (r .rhs)

record TameOp (ops : Op) : Set where
  field
    susp-op : SuspOp ops
    standard-op : StandardOp ops

WkCond : RuleSet → Set
WkCond rs = ∀ {r} A → r ∈r rs → wk-rule r A ∈r rs

WkCond-∪ : ∀ {rs rs′} → WkCond rs → WkCond rs′ → WkCond (rs ∪r rs′)
WkCond-∪ p q A [ i ] = [ map⊎ (p A) (q A) i ]

susp-rule : (r : Rule) → Rule
susp-rule r .len = 2+ (r .len)
susp-rule r .tgtCtx = susp-ctx (r .tgtCtx)
susp-rule r .lhs = susp-tm (r .lhs)
susp-rule r .rhs = susp-tm (r .rhs)

SuspCond : RuleSet → Set
SuspCond rs = ∀ {r} → r ∈r rs → susp-rule r ∈r rs

SuspCond-∪ : ∀ {rs rs′} → SuspCond rs → SuspCond rs′ → SuspCond (rs ∪r rs′)
SuspCond-∪ p q [ i ] = [ map⊎ p q i ]

sub-rule : (r : Rule) → Ctx n → Sub (r .len) n ⋆ → Rule
sub-rule r Γ σ .len = _
sub-rule r Γ σ .tgtCtx = Γ
sub-rule r Γ σ .lhs = r .lhs [ σ ]tm
sub-rule r Γ σ .rhs = r .rhs [ σ ]tm

module _ (ops : Op) where
  module Conditions (rules : RuleSet) where
    open import Catt.Typing ops rules

    SubCond′ : RuleSet → Set
    SubCond′ rs = ∀ {r n} (Γ : Ctx n) {σ : Sub (r .len) n ⋆} → Typing-Sub (r .tgtCtx) Γ σ → r ∈r rs → sub-rule r Γ σ ∈r rs

    ConvCondRule : Rule → Set
    ConvCondRule r = {A : Ty (r .len)}
                   → Typing-Tm (r .tgtCtx) (r .lhs) A
                   → Typing-Tm (r .tgtCtx) (r .rhs) A

    ConvCond′ : RuleSet → Set
    ConvCond′ rs = ∀ {r} → r ∈r rs → ConvCondRule r

    SupportCondRule : Rule → Set
    SupportCondRule r = {A : Ty (r .len)}
                      → (tty : Typing-Tm (r .tgtCtx) (r .lhs) A)
                      → SuppTm (r .tgtCtx) (r .lhs) ≡ SuppTm (r .tgtCtx) (r .rhs)

    SupportCond′ : RuleSet → Set
    SupportCond′ rs = ∀ {r} → r ∈r rs → SupportCondRule r

  module _ {rules : RuleSet} where
    open Conditions rules

    SubCond-∪ : ∀ {rs rs′} → SubCond′ rs → SubCond′ rs′ → SubCond′ (rs ∪r rs′)
    SubCond-∪ p q Γ σ [ i ] = [ map⊎ (p Γ σ) (q Γ σ) i ]

    ConvCond-∪ : ∀ {rs rs′} → ConvCond′ rs → ConvCond′ rs′ → ConvCond′ (rs ∪r rs′)
    ConvCond-∪ p q [ inj₁ x ] = p x
    ConvCond-∪ p q [ inj₂ y ] = q y

    SupportCond-∪ : ∀ {rs rs′} → SupportCond′ rs → SupportCond′ rs′ → SupportCond′ (rs ∪r rs′)
    SupportCond-∪ p q [ inj₁ x ] = p x
    SupportCond-∪ p q [ inj₂ y ] = q y

  open Conditions public





  SubCond : RuleSet → Set
  SubCond rs = SubCond′ rs rs

  ConvCond : RuleSet → Set
  ConvCond rs = ConvCond′ rs rs

  SupportCond : RuleSet → Set
  SupportCond rs = SupportCond′ rs rs

  record Tame (rs : RuleSet) : Set where
    field
      tame-op : TameOp ops
      wk-cond : WkCond rs
      susp-cond : SuspCond rs
      sub-cond : SubCond rs

    open TameOp tame-op public

  open Tame
