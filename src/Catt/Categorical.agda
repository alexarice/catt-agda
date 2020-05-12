{-# OPTIONS --without-K --safe #-}

module Catt.Categorical where

open import Catt.Syntax
open import Catt.FreeVars
open import Catt.Typing
open import Catt.Bundles
open import Data.Nat
open import Data.Fin

private
  variable
    n m : ℕ

id-sub : (n : ℕ) → Sub n n
id-sub = {!!}

id-sub-typing : (Γ : Ctx n) → Γ ⊢ id-sub n :: Γ
id-sub-typing {zero} Γ = TypeSubEmpty (id-sub zero)
id-sub-typing {suc n} Γ = {!TypeSubStep ? ? ?!}

typed-id-sub : (Γ : TypedCtx) → TypedSub Γ Γ
typed-id-sub Γ .sub = id-sub (size Γ)
typed-id-sub Γ .typing-sub = {!!}
