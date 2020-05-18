{-# OPTIONS --without-K --safe #-}

module Catt.Vec.Functional where

open import Data.Nat
open import Catt.Fin
open import Data.Product using (_,_; _×_)
open import Level using (Level)

private
  variable
    n m : ℕ
    a b c : Level
    A : ℕ → Set a
    B : ℕ → Set b
    C : Set c

record VectorD (A : ℕ → Set a) (n : ℕ) : Set a where
  field
    get : (f : Fin n) → A (toℕ f)

open VectorD public

Vector : (C : Set c) → ℕ → Set c
Vector C n = VectorD (λ _ → C) n

[] : VectorD A zero
[] .get ()

add : VectorD A n → A n → VectorD A (suc n)
add xs x .get (fromℕ _) = x
add xs x .get (inject f) = get xs f

last : VectorD A (suc n) → A n
last xs = get xs (fromℕ _)

front : VectorD A (suc n) → VectorD A n
front xs .get f = get xs (inject f)

unadd : VectorD A (suc n) → VectorD A n × A n
unadd xs = front xs , last xs

map : ((n : ℕ) → A n → B n) → VectorD A n → VectorD B n
map f xs .get g = f (toℕ g) (get xs g)

foldl : ((n : ℕ) → C → A n → C) → C → VectorD A n → C
foldl {n = zero} f e xs = e
foldl {n = suc n} f e xs = f n (foldl f e (front xs)) (last xs)
