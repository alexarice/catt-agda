{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Dyck where

open import Catt.Syntax
open import Data.Nat
open import Catt.Globular
open import Data.Bool
open import Data.Fin using (Fin; zero; suc)

data Dyck : ℕ → ℕ → Set where
  End : Dyck 0 0
  ⇑ : Dyck n d → Dyck (suc n) (suc d)
  ⇓ : Dyck n (suc d) → Dyck n d

variable
  dy ey fy : Dyck n d

dyck-to-ctx : Dyck n d → Ctx (suc (n * 2))
dyck-pre-type : Dyck n d → Ty (n * 2)
dyck-type : Dyck n d → Ty (suc (n * 2))
dyck-term : Dyck n d → Tm (suc (n * 2))

dyck-to-ctx End = ∅ , ⋆
dyck-to-ctx (⇑ d) = dyck-to-ctx d , dyck-type d , dyck-pre-type (⇑ d)
dyck-to-ctx (⇓ d) = dyck-to-ctx d

dyck-pre-type End = ⋆
dyck-pre-type (⇑ d) = (liftTerm (dyck-term d)) ─⟨ (liftType (dyck-type d)) ⟩⟶ 0V
dyck-pre-type (⇓ d) = ty-base (dyck-pre-type d)

dyck-type dy = liftType (dyck-pre-type dy)

dyck-term End = 0V
dyck-term (⇑ d) = 0V
dyck-term (⇓ d) = ty-tgt (dyck-type d)

data Peak : ∀ {n} {d} → Dyck (suc n) d → Set where
  ⇕pk : (dy : Dyck n d) → Peak (⇓ (⇑ dy))
  ⇑pk : (p : Peak dy) → Peak (⇑ dy)
  ⇓pk : (p : Peak dy) → Peak (⇓ dy)

peak-term : {dy : Dyck (suc n) d} → Peak dy → Tm (3 + (n * 2))
peak-term (⇕pk dy) = 0V
peak-term (⇑pk p) = liftTerm (liftTerm (peak-term p))
peak-term (⇓pk p) = peak-term p

susp-dyck : Dyck n d → Dyck (suc n) (suc d)
susp-dyck End = ⇑ End
susp-dyck (⇑ d) = ⇑ (susp-dyck d)
susp-dyck (⇓ d) = ⇓ (susp-dyck d)

connect-dyck : Dyck n 0 → Dyck m d → Dyck (m + n) d
connect-dyck d End = d
connect-dyck d (⇑ e) = ⇑ (connect-dyck d e)
connect-dyck d (⇓ e) = ⇓ (connect-dyck d e)

trim : Dyck (suc n) (suc d) → Dyck n d
trim (⇑ dy) = dy
trim (⇓ dy) = ⇓ (trim dy)

dyck-bd-len : (n : ℕ) → (dy : Dyck m d) → ℕ
dyck-bd : (n : ℕ) → (dy : Dyck m d) → Dyck (dyck-bd-len n dy) d

dyck-bd-len {m = zero} n dy = 0
dyck-bd-len {m = suc m} n (⇑ dy) = suc (dyck-bd-len (suc n) dy)
dyck-bd-len {m = suc m} zero (⇓ dy) = dyck-bd-len zero (trim dy)
dyck-bd-len {m = suc m} (suc n) (⇓ dy) = dyck-bd-len n dy

dyck-bd {m = zero} n dy = dy
dyck-bd {m = suc m} n (⇑ dy) = ⇑ (dyck-bd (suc n) dy)
dyck-bd {m = suc m} zero (⇓ dy) = dyck-bd zero (trim dy)
dyck-bd {m = suc m} (suc n) (⇓ dy) = ⇓ (dyck-bd n dy)

dyck-inc : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → Sub (suc (dyck-bd-len n dy * 2)) (suc (m * 2)) ⋆
dyck-inc {m = zero} n dy b = idSub
dyck-inc {m = suc m} n (⇑ dy) b = ⟨ ⟨ (liftSub (liftSub (dyck-inc (suc n) dy b))) , 1V ⟩ , 0V ⟩
dyck-inc {m = suc m} zero (⇓ dy) false = liftSub (liftSub (dyck-inc zero (trim dy) false))
dyck-inc {m = suc m} zero (⇓ dy) true = replaceSub (liftSub (liftSub (dyck-inc zero (trim dy) true))) 1V
dyck-inc {m = suc m} (suc n) (⇓ dy) b = dyck-inc n dy b

--

dyck-bd-len-1 : (n : ℕ) → (dy : Dyck m d) → ℕ
dyck-bd-len-2 : (n : ℕ) → (dy : Dyck m (n + d)) → ℕ
dyck-bd-1 : (n : ℕ) → (dy : Dyck m d) → Dyck (dyck-bd-len-1 n dy) d
dyck-bd-2 : (n : ℕ) → (dy : Dyck m (n + d)) → Dyck (dyck-bd-len-2 n dy) d

dyck-bd-len-1 n End = zero
dyck-bd-len-1 n (⇑ dy) = suc (dyck-bd-len-1 (suc n) dy)
dyck-bd-len-1 zero (⇓ dy) = dyck-bd-len-2 1 dy
dyck-bd-len-1 (suc n) (⇓ dy) = dyck-bd-len-1 n dy

dyck-bd-len-2 {d = d} zero dy = dyck-bd-len-1 0 dy
dyck-bd-len-2 (suc n) (⇑ dy) = dyck-bd-len-2 n dy
dyck-bd-len-2 (suc n) (⇓ dy) = dyck-bd-len-2 (suc (suc n)) dy

dyck-bd-1 n End = End
dyck-bd-1 n (⇑ dy) = ⇑ (dyck-bd-1 (suc n) dy)
dyck-bd-1 zero (⇓ dy) = dyck-bd-2 1 dy
dyck-bd-1 (suc n) (⇓ dy) = ⇓ (dyck-bd-1 n dy)

dyck-bd-2 {d = d} zero dy = dyck-bd-1 0 dy
dyck-bd-2 (suc n) (⇑ dy) = dyck-bd-2 n dy
dyck-bd-2 (suc n) (⇓ dy) = dyck-bd-2 (suc (suc n)) dy



dyck-inc-1 : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → Sub (suc (dyck-bd-len-1 n dy * 2)) (suc (m * 2)) ⋆
dyck-inc-2 : (n : ℕ) → (dy : Dyck m (n + d)) → (b : Bool) → Sub (suc (dyck-bd-len-2 n dy * 2)) (suc (m * 2)) ⋆

dyck-inc-1 n End b = idSub
dyck-inc-1 n (⇑ dy) b = ⟨ ⟨ (liftSub (liftSub (dyck-inc-1 (suc n) dy b))) , 1V ⟩ , 0V ⟩
dyck-inc-1 zero (⇓ dy) false = dyck-inc-2 1 dy false
dyck-inc-1 {zero} zero (⇓ dy) true = dyck-inc-2 1 dy true
dyck-inc-1 {suc n} zero (⇓ dy) true = replaceSub (dyck-inc-2 1 dy true) (dyck-term (⇓ dy))
dyck-inc-1 (suc n) (⇓ dy) b = dyck-inc-1 n dy b

dyck-inc-2 zero dy b = dyck-inc-1 zero dy b
dyck-inc-2 (suc n) (⇑ dy) b = liftSub (liftSub (dyck-inc-2 n dy b))
dyck-inc-2 (suc n) (⇓ dy) b = dyck-inc-2 (suc (suc n)) dy b
