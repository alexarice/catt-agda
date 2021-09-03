{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax.Bundles where

open import Catt.Syntax
open import Data.Nat

record CTX : Set where
  constructor <_>c
  field
    {ctx-n} : ℕ
    ctx : Ctx ctx-n

open CTX public

record TY : Set where
  constructor <_>ty
  field
    {ty-ctx-n} : ℕ
    {ty-ctx} : Ctx ty-ctx-n
    {ty-d} : ℕ
    ty : Ty ty-ctx ty-d

open TY public

record TM : Set where
  constructor <_>tm
  field
    {tm-ctx-n} : ℕ
    {tm-ctx} : Ctx tm-ctx-n
    tm : Tm tm-ctx

open TM public

record SUB : Set where
  constructor <_>s
  field
    {s-ctx-1-n} : ℕ
    {s-ctx-1} : Ctx s-ctx-1-n
    {s-ctx-2-n} : ℕ
    {s-ctx-2} : Ctx s-ctx-2-n
    sub : Sub s-ctx-1 s-ctx-2

open SUB public