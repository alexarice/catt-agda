open import Catt.Typing.Rule

module Catt.Typing.Strict.DR (ops : Op) (tameOp : TameOp ops) where

open import Catt.Prelude
open import Catt.Syntax

import Catt.Typing.DiscRemoval.Rule as DR

open DR renaming (DiscRemovalSet to DR-Rules) using (dr-wk;dr-susp) public

dr-sub : SubCond ops DR-Rules
dr-sub = DR.dr-sub

open import Catt.Typing ops DR-Rules
open import Catt.Typing.DiscRemoval ops DR-Rules

hasDiscRemovalRule : HasDiscRemovalRule
hasDiscRemovalRule = ⊆r-refl

hasDiscRemoval : HasDiscRemoval
hasDiscRemoval = dr-from-rule hasDiscRemovalRule

dr-tame : Tame ops DR-Rules
dr-tame .Tame.tame-op = tameOp
dr-tame .Tame.wk-cond = dr-wk
dr-tame .Tame.susp-cond = dr-susp
dr-tame .Tame.sub-cond = dr-sub

open TameOp tameOp

open import Catt.Typing.DiscRemoval.Typed ops standard-op DR-Rules dr-wk as DRT

open DRT using (dr-pres) public

module _ where
  open import Catt.Support.Typing ops DR-Rules
  import Catt.Typing.DiscRemoval.Support ops standard-op rulesWithSupp (rulesWithSupp-wk dr-wk) rulesWithSupp-supp as DRS

  dr-supp′ : SupportCond′ ops rulesWithSupp DR-Rules
  dr-supp′ = DRS.dr-supp

  dr-supp : SupportCond ops DR-Rules
  dr-supp = SupportCond-prop dr-supp′
