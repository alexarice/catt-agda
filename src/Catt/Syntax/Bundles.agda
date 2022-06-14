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
    ty : Ty ty-ctx-n

open TY public

record TM : Set where
  constructor <_>tm
  field
    {tm-ctx-n} : ℕ
    tm : Tm tm-ctx-n

open TM public

record SUB : Set where
  constructor <_>s
  field
    {s-ctx-1-n} : ℕ
    {s-ctx-2-n} : ℕ
    {s-ty} : Ty s-ctx-2-n
    sub : Sub s-ctx-1-n s-ctx-2-n s-ty

open SUB public

record SUB′ (m : ℕ) : Set where
  constructor <_>s′
  field
    {s-n′} : ℕ
    {s-ty′} : Ty m
    sub′ : Sub s-n′ m s-ty′

open SUB′ public
