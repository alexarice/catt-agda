{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Typing.Base where

open import Catt.Syntax
open import Data.Nat

record Rule : Set₁ where
  field
    Args : Set
    tctIndex : Set
    tgtdims : tctIndex → (a : Args) → ℕ
    tctLen : (i : tctIndex) → (a : Args) → ℕ
    tctCtx : (i : tctIndex) → (a : Args) → Ctx (tctLen i a)
    tct : (i : tctIndex) → (a : Args) → Tm (tctCtx i a)
    tctTy : (i : tctIndex) → (a : Args) → Ty (tctCtx i a) (tgtdims i a)
    eqtIndex : Set
    eqtlhsLen : (i : eqtIndex) → (a : Args) → ℕ
    eqtlhsCtx : (i : eqtIndex) → (a : Args) → Ctx (eqtlhsLen i a)
    eqtlhs : (i : eqtIndex) → (a : Args) → Tm (eqtlhsCtx i a)
    eqtrhsLen : (i : eqtIndex) → (a : Args) → ℕ
    eqtrhsCtx : (i : eqtIndex) → (a : Args) → Ctx (eqtrhsLen i a)
    eqtrhs : (i : eqtIndex) → (a : Args) → Tm (eqtrhsCtx i a)
    lhsLen : (a : Args) → ℕ
    lhsCtx : (a : Args) → Ctx (lhsLen a)
    rhsLen : (a : Args) → ℕ
    rhsCtx : (a : Args) → Ctx (rhsLen a)
    lhs : (a : Args) → Tm (lhsCtx a)
    rhs : (a : Args) → Tm (rhsCtx a)

open Rule public
