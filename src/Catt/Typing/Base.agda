{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Typing.Base where

open import Catt.Syntax
open import Data.Nat
open import Data.Fin

record Rule : Set₁ where
  field
    Args : Set
    tctCount : ℕ
    eqtCount : ℕ

  tctIndex = Fin tctCount
  eqtIndex = Fin eqtCount

  field
    tgtHeight : tctIndex → (a : Args) → ℕ
    tctLen : (i : tctIndex) → (a : Args) → ℕ
    tct : (i : tctIndex) → (a : Args) → Tm (tctLen i a)
    tctTy : (i : tctIndex) → (a : Args) → Ty (tctLen i a) (tgtHeight i a)
    tctCtx : (i : tctIndex) → (a : Args) → Ctx (tctLen i a)
    eqtLen : (i : eqtIndex) → (a : Args) → ℕ
    eqtlhs : (i : eqtIndex) → (a : Args) → Tm (eqtLen i a)
    eqtrhs : (i : eqtIndex) → (a : Args) → Tm (eqtLen i a)
    len : (a : Args) → ℕ
    lhs : (a : Args) → Tm (len a)
    rhs : (a : Args) → Tm (len a)

open Rule public
