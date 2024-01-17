open import Catt.Typing.Rule

module Catt.Typing.Rule.Typed (rules : RuleSet) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Support

open import Catt.Typing rules

module _ (r : Rule) where
  open Rule r

  ConvCondRule : Set
  ConvCondRule = {A : Ty len}
               → Typing-Tm tgtCtx lhs A
               → Typing-Tm tgtCtx rhs A

  SupportCondRule : Set
  SupportCondRule = {A : Ty len}
                  → (tty : Typing-Tm tgtCtx lhs A)
                  → SuppTm tgtCtx lhs ≡ SuppTm tgtCtx rhs


ConvCond : RuleSet → Set
ConvCond rs = ∀ {r} → r ∈r rs → ConvCondRule r

ConvCond-∪ : ∀ {rs rs′} → ConvCond rs → ConvCond rs′ → ConvCond (rs ∪r rs′)
ConvCond-∪ p q [ inj₁ x ] = p x
ConvCond-∪ p q [ inj₂ y ] = q y

SupportCond : RuleSet → Set
SupportCond rs = ∀ {r} → r ∈r rs → SupportCondRule r

SupportCond-∪ : ∀ {rs rs′} → SupportCond rs → SupportCond rs′ → SupportCond (rs ∪r rs′)
SupportCond-∪ p q [ inj₁ x ] = p x
SupportCond-∪ p q [ inj₂ y ] = q y
