{-# OPTIONS --without-K --safe #-}

module Catt.Simpson.SplitForm.ToTerm where

open import Catt.Base
open import Data.Nat
open import Catt.Simpson.SplitForm
open import Catt.Examples.Composition
open import Data.Product renaming (_,_ to _,,_)

private
  variable
    n dim : ℕ

toTerm : SplitForm n dim → TermAndType n dim
toTerm (Base x A) = x ,, A
toTerm (Comp sf sf′) = 2-compose (toTerm sf) (toTerm sf′)
toTerm (WhiskerL dim′ x sf sf′) = {!!}
toTerm (WhiskerR dim′ x sf sf′) = {!!}
