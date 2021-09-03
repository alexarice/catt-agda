{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax.Bundles where

open import Catt.Syntax
open import Data.Nat

record TY : Set where
  constructor <_>ty
  field
    {ty-ctx} : Ctx
    ty : Ty ty-ctx

open TY public

record TM : Set where
  constructor <_>tm
  field
    {tm-ctx} : Ctx
    tm : Tm tm-ctx

open TM public

record SUB : Set where
  constructor <_>s
  field
    {s-ctx-1} : Ctx
    {s-ctx-2} : Ctx
    {s-ty} : Ty s-ctx-2
    sub : Sub s-ctx-1 s-ctx-2 s-ty

open SUB public
