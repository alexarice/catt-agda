{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Dyck where

open import Catt.Syntax
open import Data.Nat
open import Data.Integer using (ℤ;+_;-[1+_])
open import Catt.Globular
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

data Dyck : ℕ → Set

dyck-excess : Dyck n → ℕ

data Dyck where
  End : Dyck 0
  ⇑ : Dyck n → Dyck (suc n)
  ⇓ : (dy : Dyck n) → .⦃ NonZero′ (dyck-excess dy) ⦄ → Dyck n

dyck-excess End = 0
dyck-excess (⇑ dy) = suc (dyck-excess dy)
dyck-excess (⇓ dy) = pred (dyck-excess dy)

variable
  dy ey fy : Dyck n

dyck-to-ctx : Dyck n → Ctx (suc (n * 2))
dyck-pre-type : Dyck n → Ty (n * 2)
dyck-type : Dyck n → Ty (suc (n * 2))
dyck-term : Dyck n → Tm (suc (n * 2))

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

data Peak : ∀ {n} → Dyck (suc n) → Set where
  ⇕pk : (dy : Dyck n) → Peak (⇓ (⇑ dy))
  ⇑pk : (p : Peak dy) → Peak (⇑ dy)
  ⇓pk : (p : Peak dy) → .⦃ _ : NonZero′ (dyck-excess dy) ⦄ → Peak (⇓ dy)

peak-term : {dy : Dyck (suc n)} → Peak dy → Tm (3 + (n * 2))
peak-term (⇕pk dy) = 0V
peak-term (⇑pk p) = liftTerm (liftTerm (peak-term p))
peak-term (⇓pk p) = peak-term p

susp-dyck : Dyck n → Dyck (suc n)
susp-dyck-excess : (dy : Dyck n) → dyck-excess (susp-dyck dy) ≡ suc (dyck-excess dy)

susp-dyck End = ⇑ End
susp-dyck (⇑ d) = ⇑ (susp-dyck d)
susp-dyck (⇓ d) = ⇓ (susp-dyck d) ⦃ NonZero′-subst (sym (susp-dyck-excess d)) it ⦄

susp-dyck-excess End = refl
susp-dyck-excess (⇑ dy) = cong suc (susp-dyck-excess dy)
susp-dyck-excess (⇓ dy) = begin
  pred (dyck-excess (susp-dyck dy))
    ≡⟨ cong pred (susp-dyck-excess dy) ⟩
  dyck-excess dy
    ≡˘⟨ suc-pred (dyck-excess dy) ⟩
  suc (pred (dyck-excess dy)) ∎
  where
    open ≡-Reasoning

connect-dyck : (dy : Dyck n) → .⦃ IsZero (dyck-excess dy) ⦄ → Dyck m → Dyck (m + n)
connect-dyck-excess : (dy : Dyck n) → .⦃ _ : IsZero (dyck-excess dy) ⦄ → (ey : Dyck m) → dyck-excess (connect-dyck dy ey) ≡ dyck-excess ey

connect-dyck d End = d
connect-dyck d (⇑ e) = ⇑ (connect-dyck d e)
connect-dyck d (⇓ e) = ⇓ (connect-dyck d e) ⦃ NonZero′-subst (sym (connect-dyck-excess d e)) it ⦄

connect-dyck-excess dy End = extract-is-zero (dyck-excess (connect-dyck dy End))
connect-dyck-excess dy (⇑ ey) = cong suc (connect-dyck-excess dy ey)
connect-dyck-excess dy (⇓ ey) = cong pred (connect-dyck-excess dy ey)

dyck-bd-len : (d : ℕ) → (dy : Dyck n) → ℕ
dyck-bd : (d : ℕ) → (dy : Dyck n) → Dyck (dyck-bd-len d dy)

dyck-bd-len d End = zero
dyck-bd-len d (⇑ dy) = {!!}
dyck-bd-len d (⇓ dy) = {!!}

dyck-bd d End = End
dyck-bd d (⇑ dy) = {!!}
dyck-bd d (⇓ dy) = {!!}

-- trim : Dyck (suc n) (suc d) → Dyck n d
-- trim (⇑ dy) = dy
-- trim (⇓ dy) = ⇓ (trim dy)

-- dyck-bd-len : (n : ℕ) → (dy : Dyck m d) → ℕ
-- dyck-bd-dim : (n : ℕ) → (dy : Dyck m d) → ℕ
-- dyck-bd : (n : ℕ) → (dy : Dyck m d) → Dyck (dyck-bd-len n dy) (dyck-bd-len n dy)

-- dyck-bd-len n dy = {!!}

-- dyck-bd-dim n dy = {!!}

-- dyck-bd n End = End
-- dyck-bd n (⇑ dy) = {!!}
-- dyck-bd n (⇓ dy) = {!!}

-- dyck-bd-len : (n : ℕ) → (dy : Dyck m d) → ℕ
-- dyck-bd : (n : ℕ) → (dy : Dyck m d) → Dyck (dyck-bd-len n dy) d

-- dyck-bd-len n dy = {!!}

-- dyck-bd n End = End
-- dyck-bd n (⇑ dy) = {!!}
-- dyck-bd n (⇓ dy) = {!!}

-- dyck-bd-len {m = zero} n dy = 0
-- dyck-bd-len {m = suc m} n (⇑ dy) = suc (dyck-bd-len (suc n) dy)
-- dyck-bd-len {m = suc m} zero (⇓ dy) = dyck-bd-len zero (trim dy)
-- dyck-bd-len {m = suc m} (suc n) (⇓ dy) = dyck-bd-len n dy

-- dyck-bd {m = zero} n dy = dy
-- dyck-bd {m = suc m} n (⇑ dy) = ⇑ (dyck-bd (suc n) dy)
-- dyck-bd {m = suc m} zero (⇓ dy) = dyck-bd zero (trim dy)
-- dyck-bd {m = suc m} (suc n) (⇓ dy) = ⇓ (dyck-bd n dy)

-- dyck-inc : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → Sub (suc (dyck-bd-len n dy * 2)) (suc (m * 2)) ⋆
-- dyck-inc {m = zero} n dy b = idSub
-- dyck-inc {m = suc m} n (⇑ dy) b = ⟨ ⟨ (liftSub (liftSub (dyck-inc (suc n) dy b))) , 1V ⟩ , 0V ⟩
-- dyck-inc {m = suc m} zero (⇓ dy) false = liftSub (liftSub (dyck-inc zero (trim dy) false))
-- dyck-inc {m = suc m} zero (⇓ dy) true = replaceSub (liftSub (liftSub (dyck-inc zero (trim dy) true))) 1V
-- dyck-inc {m = suc m} (suc n) (⇓ dy) b = dyck-inc n dy b

-- -- --

-- dyck-bd-len-1 : (n : ℕ) → (dy : Dyck m d) → ℕ
-- dyck-bd-len-2 : (n : ℕ) → (dy : Dyck m (n + d)) → ℕ
-- dyck-bd-1 : (n : ℕ) → (dy : Dyck m d) → Dyck (dyck-bd-len-1 n dy) d
-- dyck-bd-2 : (n : ℕ) → (dy : Dyck m (n + d)) → Dyck (dyck-bd-len-2 n dy) d

-- dyck-bd-len-1 n End = zero
-- dyck-bd-len-1 n (⇑ dy) = suc (dyck-bd-len-1 (suc n) dy)
-- dyck-bd-len-1 zero (⇓ dy) = dyck-bd-len-2 1 dy
-- dyck-bd-len-1 (suc n) (⇓ dy) = dyck-bd-len-1 n dy

-- dyck-bd-len-2 {d = d} zero dy = dyck-bd-len-1 0 dy
-- dyck-bd-len-2 (suc n) (⇑ dy) = dyck-bd-len-2 n dy
-- dyck-bd-len-2 (suc n) (⇓ dy) = dyck-bd-len-2 (suc (suc n)) dy

-- dyck-bd-1 n End = End
-- dyck-bd-1 n (⇑ dy) = ⇑ (dyck-bd-1 (suc n) dy)
-- dyck-bd-1 zero (⇓ dy) = dyck-bd-2 1 dy
-- dyck-bd-1 (suc n) (⇓ dy) = ⇓ (dyck-bd-1 n dy)

-- dyck-bd-2 {d = d} zero dy = dyck-bd-1 0 dy
-- dyck-bd-2 (suc n) (⇑ dy) = dyck-bd-2 n dy
-- dyck-bd-2 (suc n) (⇓ dy) = dyck-bd-2 (suc (suc n)) dy



-- dyck-inc-1 : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → Sub (suc (dyck-bd-len-1 n dy * 2)) (suc (m * 2)) ⋆
-- dyck-inc-2 : (n : ℕ) → (dy : Dyck m (n + d)) → (b : Bool) → Sub (suc (dyck-bd-len-2 n dy * 2)) (suc (m * 2)) ⋆

-- dyck-inc-1 n End b = idSub
-- dyck-inc-1 n (⇑ dy) b = ⟨ ⟨ (liftSub (liftSub (dyck-inc-1 (suc n) dy b))) , 1V ⟩ , 0V ⟩
-- dyck-inc-1 zero (⇓ dy) false = dyck-inc-2 1 dy false
-- dyck-inc-1 {zero} zero (⇓ dy) true = dyck-inc-2 1 dy true
-- dyck-inc-1 {suc n} zero (⇓ dy) true = replaceSub (dyck-inc-2 1 dy true) (dyck-term (⇓ dy))
-- dyck-inc-1 (suc n) (⇓ dy) b = dyck-inc-1 n dy b

-- dyck-inc-2 zero dy b = dyck-inc-1 zero dy b
-- dyck-inc-2 (suc n) (⇑ dy) b = liftSub (liftSub (dyck-inc-2 n dy b))
-- dyck-inc-2 (suc n) (⇓ dy) b = dyck-inc-2 (suc (suc n)) dy b
