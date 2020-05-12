{-# OPTIONS --without-K --safe #-}

module Catt.Categorical where

open import Catt.Syntax
open import Catt.FreeVars
open import Catt.Typing
open import Catt.Bundles
open import Data.Nat
open import Data.Fin

id-sub : (n : ℕ) → Substitution n n
id-sub n x = Var x

typed-id-sub : (Γ : TypedCtx) → TypedSub Γ Γ
typed-id-sub Γ .sub = id-sub (size Γ)
typed-id-sub Γ .typing-sub = {!!}
