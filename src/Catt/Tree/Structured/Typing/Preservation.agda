open import Catt.Typing.Rule

module Catt.Tree.Structured.Typing.Preservation (ops : Op)
                                                (rules : RuleSet)
                                                (tame : Tame ops rules)
                                                (supp-cond : SupportCond ops rules)
                                                (pres-cond : PresCond ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular

open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Typing.Properties.Preservation ops rules sub-cond supp-cond pres-cond
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame

stm-preservation : a ≈[ Γ ]stm b → Typing-STm Γ a As → Typing-STm Γ b As
stm-preservation [ p ] [ aty ] = [ term-preservation p aty ]

stm-full-preservation : a ≈[ Γ ]stm b → As ≈[ Γ ]sty Bs → Typing-STm Γ a As → Typing-STm Γ b Bs
stm-full-preservation [ p ] [ q ] [ aty ] = [ full-term-pres p q aty ]

sty-preservation : As ≈[ Γ ]sty Bs → Typing-STy Γ As → Typing-STy Γ Bs
sty-preservation [ p ] [ Asty ] = [ type-preservation p Asty ]

label-preservation : {L M : Label-WT X S} → ap L ≈[ Γ ]l ap M → lty L ≈[ Γ ]sty lty M → Typing-Label Γ L → Typing-Label Γ M
label-preservation [ p ] q (TySing x) = TySing (stm-full-preservation (p PHere) q x)
label-preservation [ p ] q (TyJoin x LTy LTy′)
  = TyJoin (stm-full-preservation (p PHere) q x)
           (label-preservation [ p ∘ PExt ] (≈SArr (p PHere) q (p (PShift PHere))) LTy)
           (label-preservation [ p ∘ PShift ] q LTy′)

STy-unique-≈ : a ≈[ Γ ]stm b → Typing-STm Γ a As → Typing-STm Γ b Bs → As ≈[ Γ ]sty Bs
STy-unique-≈ p aty bty = STy-unique (stm-preservation p aty) bty

label-max-equality-prop : {L M : Label-WT X S} → ap L ≈[ Γ ]lm ap M → Typing-Label Γ L → Typing-Label Γ M → ap L ≈[ Γ ]l ap M
label-max-equality-type-prop : {L M : Label-WT X S} → ap L ≈[ Γ ]lm ap M → Typing-Label Γ L → Typing-Label Γ M → lty L ≈[ Γ ]sty lty M

label-max-equality-prop {S = Sing} [ p ] Lty Mty .get PHere = p PHere
label-max-equality-prop {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get PHere
  = sty-src-≈ (label-max-equality-type-prop [ (λ Q → p (PExt Q) ⦃ inst ⦄) ] Lty Mty)
label-max-equality-prop {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PExt P)
  = label-max-equality-prop [ (λ Q → p (PExt Q) ⦃ inst ⦄) ] Lty Mty .get P
label-max-equality-prop {S = Join S Sing} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PShift PHere)
  = sty-tgt-≈ (label-max-equality-type-prop [ (λ Q → p (PExt Q) ⦃ inst ⦄) ] Lty Mty)
label-max-equality-prop {S = Join S T@(Join _ _)} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PShift P)
  = label-max-equality-prop [ (λ Q → p (PShift Q) ⦃ build ⦃ maximal-join-not-here Q ⦄ ⦄) ] Lty′ Mty′ .get P

label-max-equality-type-prop {S = Sing} [ p ] (TySing x) (TySing y)
  = STy-unique-≈ (p PHere) x y
label-max-equality-type-prop {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′)
  = sty-base-≈ (label-max-equality-type-prop [ (λ Q → p (PExt Q) ⦃ inst ⦄) ] Lty Mty)

label-equality-type-prop : {L M : Label-WT X S} → ap L ≈[ Γ ]l ap M → Typing-Label Γ L → Typing-Label Γ M → lty L ≈[ Γ ]sty lty M
label-equality-type-prop [ p ] Lty Mty = label-max-equality-type-prop [ (λ P → p P) ] Lty Mty
