{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Dyck.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin;suc;zero)
open import Catt.Dyck
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Variables
open import Catt.Syntax.SyntacticEquality
open import Data.Fin using (zero)
open import Relation.Nullary
open import Data.Bool using (Bool;true;false)
open import Data.Empty
open import Data.Unit using (⊤; tt)
import Relation.Binary.Reasoning.Setoid as Reasoning

data _≃d_ : Dyck n d → Dyck n′ d′ → Set where
  End≃ : End ≃d End
  ⇑≃ : dy ≃d ey → ⇑ dy ≃d ⇑ ey
  ⇓≃ : dy ≃d ey → ⇓ dy ≃d ⇓ ey

refl≃d : dy ≃d dy
refl≃d {dy = End} = End≃
refl≃d {dy = ⇑ dy} = ⇑≃ refl≃d
refl≃d {dy = ⇓ dy} = ⇓≃ refl≃d

sym≃d : dy ≃d ey → ey ≃d dy
sym≃d End≃ = End≃
sym≃d (⇑≃ p) = ⇑≃ (sym≃d p)
sym≃d (⇓≃ p) = ⇓≃ (sym≃d p)

trans≃d : dy ≃d ey → ey ≃d fy → dy ≃d fy
trans≃d End≃ End≃ = End≃
trans≃d (⇑≃ p) (⇑≃ q) = ⇑≃ (trans≃d p q)
trans≃d (⇓≃ p) (⇓≃ q) = ⇓≃ (trans≃d p q)

reflexive≃d : dy ≡ ey → dy ≃d ey
reflexive≃d refl = refl≃d

≃d-to-≡ : dy ≃d ey → dy ≡ ey
≃d-to-≡ End≃ = refl
≃d-to-≡ (⇑≃ p) = cong ⇑ (≃d-to-≡ p)
≃d-to-≡ (⇓≃ p) = cong ⇓ (≃d-to-≡ p)

record DYCK : Set where
  constructor <_>d
  field
    {dyck-n} : ℕ
    {dyck-d} : ℕ
    dyck : Dyck dyck-n dyck-d

open DYCK public

dyck-setoid : Setoid _ _
dyck-setoid = record { Carrier = DYCK
                     ; _≈_ = λ x y → dyck x ≃d dyck y
                     ; isEquivalence = record { refl = refl≃d
                                              ; sym = sym≃d
                                              ; trans = trans≃d
                                              }
                     }


connect-dyck-≃ : {gy : Dyck n d} → dy ≃d ey → fy ≃d gy → connect-dyck dy fy ≃d connect-dyck ey gy
connect-dyck-≃ p End≃ = p
connect-dyck-≃ p (⇑≃ q) = ⇑≃ (connect-dyck-≃ p q)
connect-dyck-≃ p (⇓≃ q) = ⇓≃ (connect-dyck-≃ p q)

susp-dyck-≃ : dy ≃d ey → susp-dyck dy ≃d susp-dyck ey
susp-dyck-≃ End≃ = refl≃d
susp-dyck-≃ (⇑≃ p) = ⇑≃ (susp-dyck-≃ p)
susp-dyck-≃ (⇓≃ p) = ⇓≃ (susp-dyck-≃ p)

dyck-type-dim : (dy : Dyck n d) → ty-dim (dyck-type dy) ≡ d
dyck-type-dim End = refl
dyck-type-dim (⇑ dy) = cong suc (trans (lift-ty-dim (liftType (dyck-type dy))) (trans (lift-ty-dim (dyck-type dy)) (dyck-type-dim dy)))
dyck-type-dim (⇓ dy) = trans (cong ty-dim (sym (≃ty-to-≡ (ty-base-lift (dyck-pre-type dy))))) (trans (ty-dim-ty-base (dyck-type dy)) (cong pred (dyck-type-dim dy)))

dyck-zero-lem : ¬ (Dyck zero (suc d))
dyck-zero-lem (⇓ dy) = dyck-zero-lem dy

-- dyck-type-inc : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → dyck-type (dyck-bd n dy) [ dyck-inc n dy b ]ty ≃ty dyck-type dy
-- dyck-term-inc : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → dyck-term (dyck-bd (suc n) dy) [ dyck-inc (suc n) dy b ]tm ≃tm dyck-term dy


-- dyck-type-trim : (dy : Dyck (suc n) (suc d)) → liftType (liftType (dyck-type (trim dy))) ≃ty ty-base (dyck-type dy)
-- dyck-type-trim (⇑ dy) = refl≃ty
-- dyck-type-trim (⇓ dy) = begin
--   < liftType (liftType (liftType (ty-base (dyck-pre-type (trim dy))))) >ty
--     ≈˘⟨ lift-ty-≃ (lift-ty-≃ (ty-base-lift (dyck-pre-type (trim dy)))) ⟩
--   < liftType (liftType (ty-base (dyck-type (trim dy)))) >ty
--     ≈˘⟨ lift-ty-≃ (ty-base-lift (dyck-type (trim dy))) ⟩
--   < liftType (ty-base (liftType (dyck-type (trim dy)))) >ty
--     ≈˘⟨ ty-base-lift (liftType (dyck-type (trim dy))) ⟩
--   < ty-base (liftType (liftType (dyck-type (trim dy)))) >ty
--     ≈⟨ ty-base-≃ (dyck-type-trim dy) ⟩
--   < ty-base (ty-base (dyck-type dy)) >ty
--     ≈⟨ ty-base-≃ (ty-base-lift (dyck-pre-type dy)) ⟩
--   < ty-base (liftType (ty-base (dyck-pre-type dy))) >ty ∎
--   where
--     open Reasoning ty-setoid

-- dyck-type-trim : (dy : Dyck (suc n) (suc d)) → (b : Bool) → dyck-type (trim dy) [ dyck-inc-proj b ]ty ≃ty liftType (ty-base (dyck-pre-type dy))
-- dyck-type-trim (⇑ dy) false = begin
--   < dyck-type dy [ liftSub (liftSub idSub) ]ty >ty
--     ≈⟨ apply-lifted-sub-ty-≃ (dyck-type dy) (liftSub idSub) ⟩
--   < liftType (dyck-type dy [ liftSub idSub ]ty) >ty
--     ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type dy) idSub) ⟩
--   < liftType (liftType (dyck-type dy [ idSub ]ty)) >ty
--     ≈⟨ lift-ty-≃ (lift-ty-≃ (id-on-ty (dyck-type dy))) ⟩
--   < liftType (liftType (dyck-type dy)) >ty ∎
--   where
--     open Reasoning ty-setoid
-- dyck-type-trim (⇑ dy) true = begin
--   < dyck-type dy [ ⟨ liftSub (liftSub (liftSub idSub)) , 1V ⟩ ]ty >ty
--     ≈⟨ lift-sub-comp-lem-ty (liftSub (liftSub (liftSub idSub))) (dyck-pre-type dy) ⟩
--   < dyck-pre-type dy [ liftSub (liftSub (liftSub idSub)) ]ty >ty
--     ≈⟨ apply-lifted-sub-ty-≃ (dyck-pre-type dy) (liftSub (liftSub idSub)) ⟩
--   < liftType (dyck-pre-type dy [ liftSub (liftSub idSub) ]ty) >ty
--     ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-pre-type dy) (liftSub idSub)) ⟩
--   < liftType (liftType (dyck-pre-type dy [ liftSub idSub ]ty)) >ty
--     ≈⟨ lift-ty-≃ (lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-pre-type dy) idSub)) ⟩
--   < liftType (liftType (liftType (dyck-pre-type dy [ idSub ]ty))) >ty
--     ≈⟨ lift-ty-≃ (lift-ty-≃ (lift-ty-≃ (id-on-ty (dyck-pre-type dy)))) ⟩
--   < liftType (liftType (dyck-type dy)) >ty ∎
--   where
--     open Reasoning ty-setoid
-- dyck-type-trim (⇓ dy) b = begin
--   < liftType (ty-base (dyck-pre-type (trim dy))) [ dyck-inc-proj b ]ty >ty
--     ≈˘⟨ sub-action-≃-ty (ty-base-lift (dyck-pre-type (trim dy))) refl≃s ⟩
--   < ty-base (dyck-type (trim dy)) [ dyck-inc-proj b ]ty >ty
--     ≈⟨ ty-base-sub (dyck-type (trim dy)) (dyck-inc-proj b) ⟩
--   < ty-base (dyck-type (trim dy) [ dyck-inc-proj b ]ty) >ty
--     ≈⟨ ty-base-≃ (dyck-type-trim dy b) ⟩
--   < ty-base (liftType (ty-base (dyck-pre-type dy))) >ty
--     ≈⟨ ty-base-lift (ty-base (dyck-pre-type dy)) ⟩
--   < liftType (ty-base (ty-base (dyck-pre-type dy))) >ty ∎
--   where
--     open Reasoning ty-setoid


-- dyck-type-inc {m = zero} n End b = Star≃ refl
-- dyck-type-inc {m = zero} n (⇓ dy) b = ⊥-elim (dyck-zero-lem dy)
-- dyck-type-inc {m = suc m} n (⇑ dy) b = Arr≃ l1 l2 refl≃tm
--   where
--     l1 : (liftTerm (liftTerm (dyck-term (dyck-bd (suc n) dy))) [
--             dyck-inc n (⇑ dy) b ]tm)
--            ≃tm liftTerm (liftTerm (dyck-term dy))
--     l1 = begin
--       < liftTerm (liftTerm (dyck-term (dyck-bd (suc n) dy))) [ dyck-inc n (⇑ dy) b ]tm >tm
--         ≈⟨ lift-sub-comp-lem-tm ⟨ liftSub (liftSub (dyck-inc (suc n) dy b)) , 1V ⟩ (liftTerm (dyck-term (dyck-bd (suc n) dy))) ⟩
--       < liftTerm (dyck-term (dyck-bd (suc n) dy)) [ ⟨ liftSub (liftSub (dyck-inc (suc n) dy b)) , 1V ⟩ ]tm >tm
--         ≈⟨ lift-sub-comp-lem-tm (liftSub (liftSub (dyck-inc (suc n) dy b))) (dyck-term (dyck-bd (suc n) dy)) ⟩
--       < dyck-term (dyck-bd (suc n) dy) [ liftSub (liftSub (dyck-inc (suc n) dy b)) ]tm >tm
--         ≈⟨ apply-lifted-sub-tm-≃ (dyck-term (dyck-bd (suc n) dy)) (liftSub (dyck-inc (suc n) dy b)) ⟩
--       < liftTerm (dyck-term (dyck-bd (suc n) dy) [ liftSub (dyck-inc (suc n) dy b) ]tm) >tm
--         ≈⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ (dyck-term (dyck-bd (suc n) dy)) (dyck-inc (suc n) dy b)) ⟩
--       < liftTerm (liftTerm (dyck-term (dyck-bd (suc n) dy) [ dyck-inc (suc n) dy b ]tm)) >tm
--         ≈⟨ lift-tm-≃ (lift-tm-≃ (dyck-term-inc n dy b)) ⟩
--       < liftTerm (liftTerm (dyck-term dy)) >tm ∎
--       where
--         open Reasoning tm-setoid

--     l2 : (liftType (liftType (dyck-type (dyck-bd (suc n) dy))) [
--             dyck-inc n (⇑ dy) b ]ty)
--            ≃ty liftType (liftType (dyck-type dy))
--     l2 = begin
--       < liftType (liftType (dyck-type (dyck-bd (suc n) dy))) [ dyck-inc n (⇑ dy) b ]ty >ty
--         ≈⟨ lift-sub-comp-lem-ty ⟨ liftSub (liftSub (dyck-inc (suc n) dy b)) , 1V ⟩ (liftType (dyck-type (dyck-bd (suc n) dy))) ⟩
--       < liftType (dyck-type (dyck-bd (suc n) dy)) [ ⟨ liftSub (liftSub (dyck-inc (suc n) dy b)) , 1V ⟩ ]ty >ty
--         ≈⟨ lift-sub-comp-lem-ty (liftSub (liftSub (dyck-inc (suc n) dy b))) (dyck-type (dyck-bd (suc n) dy)) ⟩
--       < dyck-type (dyck-bd (suc n) dy) [ liftSub (liftSub (dyck-inc (suc n) dy b)) ]ty >ty
--         ≈⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd (suc n) dy)) (liftSub (dyck-inc (suc n) dy b)) ⟩
--       < liftType (dyck-type (dyck-bd (suc n) dy) [ liftSub (dyck-inc (suc n) dy b) ]ty) >ty
--         ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd (suc n) dy)) (dyck-inc (suc n) dy b)) ⟩
--       < liftType (liftType (dyck-type (dyck-bd (suc n) dy) [ dyck-inc (suc n) dy b ]ty)) >ty
--         ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc (suc n) dy b)) ⟩
--       < liftType (liftType (dyck-type dy)) >ty ∎
--       where
--         open Reasoning ty-setoid

-- dyck-type-inc {m = suc m} zero (⇓ dy) false = begin
--   < dyck-type (dyck-bd zero (trim dy)) [ liftSub (liftSub (dyck-inc zero (trim dy) false)) ]ty >ty
--     ≈⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd zero (trim dy))) (liftSub (dyck-inc zero (trim dy) false)) ⟩
--   < liftType (dyck-type (dyck-bd zero (trim dy)) [ liftSub (dyck-inc zero (trim dy) false) ]ty) >ty
--     ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd zero (trim dy))) (dyck-inc zero (trim dy) false)) ⟩
--   < liftType (liftType (dyck-type (dyck-bd zero (trim dy)) [ dyck-inc zero (trim dy) false ]ty)) >ty
--     ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc zero (trim dy) false)) ⟩
--   < liftType (liftType (dyck-type (trim dy))) >ty
--     ≈⟨ dyck-type-trim dy ⟩
--   < ty-base (dyck-type dy) >ty
--     ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
--   < liftType (ty-base (dyck-pre-type dy)) >ty ∎
--   where
--     open Reasoning ty-setoid
-- dyck-type-inc {m = suc m} zero (⇓ dy) true = begin
--   < dyck-type (dyck-bd zero (trim dy))
--     [ replaceSub (liftSub (liftSub (dyck-inc zero (trim dy) true))) 1V ]ty >ty
--     ≈˘⟨ sub-action-≃-ty refl≃ty (replaceSub-lift (liftSub (dyck-inc zero (trim dy) true)) 0V) ⟩
--   < dyck-type (dyck-bd zero (trim dy))
--     [ liftSub (replaceSub (liftSub (dyck-inc zero (trim dy) true)) (Var zero)) ]ty >ty
--     ≈⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd zero (trim dy))) (replaceSub (liftSub (dyck-inc zero (trim dy) true)) (Var zero)) ⟩
--   < liftType (dyck-type (dyck-bd zero (trim dy))
--              [ replaceSub (liftSub (dyck-inc zero (trim dy) true)) (Var zero) ]ty) >ty
--     ≈⟨ lift-ty-≃ (apply-replaceSub-lift-ty (dyck-pre-type (dyck-bd zero (trim dy))) (liftSub (dyck-inc zero (trim dy) true)) (Var zero)) ⟩
--   < liftType (dyck-type (dyck-bd zero (trim dy))
--              [ liftSub (dyck-inc zero (trim dy) true) ]ty) >ty
--     ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd zero (trim dy))) (dyck-inc zero (trim dy) true)) ⟩
--   < liftType (liftType (dyck-type (dyck-bd zero (trim dy)) [ dyck-inc zero (trim dy) true ]ty)) >ty
--     ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc zero (trim dy) true)) ⟩
--   < liftType (liftType (dyck-type (trim dy))) >ty
--     ≈⟨ dyck-type-trim dy ⟩
--   < ty-base (dyck-type dy) >ty
--     ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
--   < liftType (ty-base (dyck-pre-type dy)) >ty ∎
--   where
--     open Reasoning ty-setoid

-- dyck-type-inc {m = suc m} (suc n) (⇓ dy) b = begin
--   < liftType (ty-base (dyck-pre-type (dyck-bd n dy))) [ dyck-inc n dy b ]ty >ty
--     ≈˘⟨ sub-action-≃-ty (ty-base-lift (dyck-pre-type (dyck-bd n dy))) refl≃s ⟩
--   < ty-base (dyck-type (dyck-bd n dy)) [ dyck-inc n dy b ]ty >ty
--     ≈⟨ ty-base-sub (dyck-type (dyck-bd n dy)) (dyck-inc n dy b) ⟩
--   < ty-base (dyck-type (dyck-bd n dy) [ dyck-inc n dy b ]ty) >ty
--     ≈⟨ ty-base-≃ (dyck-type-inc n dy b) ⟩
--   < ty-base (dyck-type dy) >ty
--     ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
--   < liftType (ty-base (dyck-pre-type dy)) >ty ∎
--   where
--     open Reasoning ty-setoid

-- dyck-term-inc {m = zero} n End b = refl≃tm
-- dyck-term-inc {m = zero} n (⇓ dy) b = ⊥-elim (dyck-zero-lem dy)
-- dyck-term-inc {m = suc m} n (⇑ dy) b = refl≃tm
-- dyck-term-inc {m = suc m} n (⇓ dy) b = begin
--   < ty-tgt (dyck-type (dyck-bd n dy)) [ dyck-inc n dy b ]tm >tm
--     ≈⟨ ty-tgt-sub (dyck-type (dyck-bd n dy)) (dyck-inc n dy b) (<-transˡ 0<1+n (≤-reflexive (sym (dyck-type-dim (dyck-bd n dy))))) ⟩
--   < ty-tgt (dyck-type (dyck-bd n dy) [ dyck-inc n dy b ]ty) >tm
--     ≈⟨ ty-tgt-≃ (dyck-type-inc n dy b) ⟩
--   < ty-tgt (dyck-type dy) >tm ∎
--   where
--     open Reasoning tm-setoid

dyck-type-inc-1 : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → dyck-type (dyck-bd-1 n dy) [ dyck-inc-1 n dy b ]ty ≃ty dyck-type dy
dyck-type-inc-2 : (n : ℕ) → (dy : Dyck m (n + d)) → (b : Bool) → dyck-type (dyck-bd-2 n dy) [ dyck-inc-2 n dy b ]ty ≃ty truncate′ n (dyck-type dy)
dyck-term-inc-1 : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → dyck-term (dyck-bd-1 (suc n) dy) [ dyck-inc-1 (suc n) dy b ]tm ≃tm dyck-term dy

dyck-type-inc-1 n End b = Star≃ refl
dyck-type-inc-1 n (⇑ dy) b = Arr≃ l1 l2 refl≃tm
  where
    l1 : (liftTerm (liftTerm (dyck-term (dyck-bd-1 (suc n) dy))) [
            dyck-inc-1 n (⇑ dy) b ]tm)
           ≃tm liftTerm (liftTerm (dyck-term dy))
    l1 = begin
      < liftTerm (liftTerm (dyck-term (dyck-bd-1 (suc n) dy))) [ dyck-inc-1 n (⇑ dy) b ]tm >tm
        ≈⟨ lift-sub-comp-lem-tm ⟨ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) , 1V ⟩ (liftTerm (dyck-term (dyck-bd-1 (suc n) dy))) ⟩
      < liftTerm (dyck-term (dyck-bd-1 (suc n) dy)) [ ⟨ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) , 1V ⟩ ]tm >tm
        ≈⟨ lift-sub-comp-lem-tm (liftSub (liftSub (dyck-inc-1 (suc n) dy b))) (dyck-term (dyck-bd-1 (suc n) dy)) ⟩
      < dyck-term (dyck-bd-1 (suc n) dy) [ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) ]tm >tm
        ≈⟨ apply-lifted-sub-tm-≃ (dyck-term (dyck-bd-1 (suc n) dy)) (liftSub (dyck-inc-1 (suc n) dy b)) ⟩
      < liftTerm (dyck-term (dyck-bd-1 (suc n) dy) [ liftSub (dyck-inc-1 (suc n) dy b) ]tm) >tm
        ≈⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ (dyck-term (dyck-bd-1 (suc n) dy)) (dyck-inc-1 (suc n) dy b)) ⟩
      < liftTerm (liftTerm (dyck-term (dyck-bd-1 (suc n) dy) [ dyck-inc-1 (suc n) dy b ]tm)) >tm
        ≈⟨ lift-tm-≃ (lift-tm-≃ (dyck-term-inc-1 n dy b)) ⟩
      < liftTerm (liftTerm (dyck-term dy)) >tm ∎
      where
        open Reasoning tm-setoid

    l2 : (liftType (liftType (dyck-type (dyck-bd-1 (suc n) dy))) [
            dyck-inc-1 n (⇑ dy) b ]ty)
           ≃ty liftType (liftType (dyck-type dy))
    l2 = begin
      < liftType (liftType (dyck-type (dyck-bd-1 (suc n) dy))) [ dyck-inc-1 n (⇑ dy) b ]ty >ty
        ≈⟨ lift-sub-comp-lem-ty ⟨ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) , 1V ⟩ (liftType (dyck-type (dyck-bd-1 (suc n) dy))) ⟩
      < liftType (dyck-type (dyck-bd-1 (suc n) dy)) [ ⟨ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) , 1V ⟩ ]ty >ty
        ≈⟨ lift-sub-comp-lem-ty (liftSub (liftSub (dyck-inc-1 (suc n) dy b))) (dyck-type (dyck-bd-1 (suc n) dy)) ⟩
      < dyck-type (dyck-bd-1 (suc n) dy) [ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) ]ty >ty
        ≈⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-1 (suc n) dy)) (liftSub (dyck-inc-1 (suc n) dy b)) ⟩
      < liftType (dyck-type (dyck-bd-1 (suc n) dy) [ liftSub (dyck-inc-1 (suc n) dy b) ]ty) >ty
        ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-1 (suc n) dy)) (dyck-inc-1 (suc n) dy b)) ⟩
      < liftType (liftType (dyck-type (dyck-bd-1 (suc n) dy) [ dyck-inc-1 (suc n) dy b ]ty)) >ty
        ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc-1 (suc n) dy b)) ⟩
      < liftType (liftType (dyck-type dy)) >ty ∎
      where
        open Reasoning ty-setoid
dyck-type-inc-1 zero (⇓ dy) false = trans≃ty (dyck-type-inc-2 1 dy false) (ty-base-lift (dyck-pre-type dy))
dyck-type-inc-1 {m = zero} zero (⇓ dy) true = trans≃ty (dyck-type-inc-2 1 dy true) (ty-base-lift (dyck-pre-type dy))
dyck-type-inc-1 {m = suc m} zero (⇓ dy) true = begin
  < dyck-type (dyck-bd-2 1 dy) [ replaceSub (dyck-inc-2 1 dy true) (dyck-term (⇓ dy)) ]ty >ty
    ≈⟨ apply-replaceSub-lift-ty (dyck-pre-type (dyck-bd-2 1 dy)) (dyck-inc-2 1 dy true) (dyck-term (⇓ dy)) ⟩
  < dyck-type (dyck-bd-2 1 dy) [ dyck-inc-2 1 dy true ]ty >ty
    ≈⟨ dyck-type-inc-2 1 dy true ⟩
  < ty-base (dyck-type dy) >ty
    ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
  < liftType (ty-base (dyck-pre-type dy)) >ty ∎
  where
    open Reasoning ty-setoid
dyck-type-inc-1 (suc n) (⇓ dy) b = begin
  < liftType (ty-base (dyck-pre-type (dyck-bd-1 n dy))) [ dyck-inc-1 n dy b ]ty >ty
    ≈˘⟨ sub-action-≃-ty (ty-base-lift (dyck-pre-type (dyck-bd-1 n dy))) refl≃s ⟩
  < ty-base (dyck-type (dyck-bd-1 n dy)) [ dyck-inc-1 n dy b ]ty >ty
    ≈⟨ ty-base-sub (dyck-type (dyck-bd-1 n dy)) (dyck-inc-1 n dy b) ⟩
  < ty-base (dyck-type (dyck-bd-1 n dy) [ dyck-inc-1 n dy b ]ty) >ty
    ≈⟨ ty-base-≃ (dyck-type-inc-1 n dy b) ⟩
  < ty-base (dyck-type dy) >ty
    ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
  < liftType (ty-base (dyck-pre-type dy)) >ty ∎
  where
    open Reasoning ty-setoid
-- dyck-type-inc-1 zero (⇓ dy) false = begin
--   < dyck-type (dyck-bd-1 zero (trim dy)) [ liftSub (liftSub (dyck-inc-1 zero (trim dy) false)) ]ty >ty
--     ≈⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-1 zero (trim dy))) (liftSub (dyck-inc-1 zero (trim dy) false)) ⟩
--   < liftType (dyck-type (dyck-bd-1 zero (trim dy)) [ liftSub (dyck-inc-1 zero (trim dy) false) ]ty) >ty
--     ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-1 zero (trim dy))) (dyck-inc-1 zero (trim dy) false)) ⟩
--   < liftType (liftType (dyck-type (dyck-bd-1 zero (trim dy)) [ dyck-inc-1 zero (trim dy) false ]ty)) >ty
--     ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc-1 zero (trim dy) false)) ⟩
--   < liftType (liftType (dyck-type (trim dy))) >ty
--     ≈⟨ dyck-type-trim dy ⟩
--   < ty-base (dyck-type dy) >ty
--     ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
--   < liftType (ty-base (dyck-pre-type dy)) >ty ∎
--   where
--     open Reasoning ty-setoid
-- dyck-type-inc-1 {m = s} zero (⇓ dy) true = begin
--   < dyck-type (dyck-bd-1 zero (trim dy))
--     [ replaceSub (liftSub (liftSub (dyck-inc-1 zero (trim dy) true))) 1V ]ty >ty
--     ≈˘⟨ sub-action-≃-ty refl≃ty (replaceSub-lift (liftSub (dyck-inc-1 zero (trim dy) true)) 0V) ⟩
--   < dyck-type (dyck-bd-1 zero (trim dy))
--     [ liftSub (replaceSub (liftSub (dyck-inc-1 zero (trim dy) true)) (Var zero)) ]ty >ty
--     ≈⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-1 zero (trim dy))) (replaceSub (liftSub (dyck-inc-1 zero (trim dy) true)) (Var zero)) ⟩
--   < liftType (dyck-type (dyck-bd-1 zero (trim dy))
--              [ replaceSub (liftSub (dyck-inc-1 zero (trim dy) true)) (Var zero) ]ty) >ty
--     ≈⟨ lift-ty-≃ (apply-replaceSub-lift-ty (dyck-pre-type (dyck-bd-1 zero (trim dy))) (liftSub (dyck-inc-1 zero (trim dy) true)) (Var zero)) ⟩
--   < liftType (dyck-type (dyck-bd-1 zero (trim dy))
--              [ liftSub (dyck-inc-1 zero (trim dy) true) ]ty) >ty
--     ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-1 zero (trim dy))) (dyck-inc-1 zero (trim dy) true)) ⟩
--   < liftType (liftType (dyck-type (dyck-bd-1 zero (trim dy)) [ dyck-inc-1 zero (trim dy) true ]ty)) >ty
--     ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc-1 zero (trim dy) true)) ⟩
--   < liftType (liftType (dyck-type (trim dy))) >ty
--     ≈⟨ dyck-type-trim dy ⟩
--   < ty-base (dyck-type dy) >ty
--     ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
--   < liftType (ty-base (dyck-pre-type dy)) >ty ∎
--   where
--     open Reasoning ty-setoid

-- dyck-type-inc-1 {m = suc m} (suc n) (⇓ dy) b = begin
--   < liftType (ty-base (dyck-pre-type (dyck-bd-1 n dy))) [ dyck-inc-1 n dy b ]ty >ty
--     ≈˘⟨ sub-action-≃-ty (ty-base-lift (dyck-pre-type (dyck-bd-1 n dy))) refl≃s ⟩
--   < ty-base (dyck-type (dyck-bd-1 n dy)) [ dyck-inc-1 n dy b ]ty >ty
--     ≈⟨ ty-base-sub (dyck-type (dyck-bd-1 n dy)) (dyck-inc-1 n dy b) ⟩
--   < ty-base (dyck-type (dyck-bd-1 n dy) [ dyck-inc-1 n dy b ]ty) >ty
--     ≈⟨ ty-base-≃ (dyck-type-inc-1 n dy b) ⟩
--   < ty-base (dyck-type dy) >ty
--     ≈⟨ ty-base-lift (dyck-pre-type dy) ⟩
--   < liftType (ty-base (dyck-pre-type dy)) >ty ∎
--   where
--     open Reasoning ty-setoid

dyck-type-inc-2 zero dy b = dyck-type-inc-1 zero dy b
dyck-type-inc-2 (suc n) (⇑ dy) b = begin
  < dyck-type (dyck-bd-2 n dy) [ liftSub (liftSub (dyck-inc-2 n dy b)) ]ty >ty
    ≈⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-2 n dy)) (liftSub (dyck-inc-2 n dy b)) ⟩
  < liftType (dyck-type (dyck-bd-2 n dy) [ liftSub (dyck-inc-2 n dy b) ]ty) >ty
    ≈⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-2 n dy)) (dyck-inc-2 n dy b)) ⟩
  < liftType (liftType (dyck-type (dyck-bd-2 n dy) [ dyck-inc-2 n dy b ]ty)) >ty
    ≈⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc-2 n dy b)) ⟩
  < liftType (liftType (truncate′ n (dyck-type dy))) >ty
    ≈˘⟨ lift-ty-≃ (truncate′-lift n (dyck-type dy)) ⟩
  < liftType (truncate′ n (liftType (dyck-type dy))) >ty
    ≈˘⟨ truncate′-lift n (liftType (dyck-type dy)) ⟩
  < truncate′ n (liftType (liftType (dyck-type dy))) >ty ∎
  where
    open Reasoning ty-setoid
dyck-type-inc-2 (suc n) (⇓ dy) b = begin
  < dyck-type (dyck-bd-2 (suc (suc n)) dy) [
       dyck-inc-2 (suc (suc n)) dy b ]ty >ty
    ≈⟨ dyck-type-inc-2 (suc (suc n)) dy b ⟩
  < truncate′ (suc (suc n)) (dyck-type dy) >ty
    ≈⟨ truncate′-≃ {d = suc n} refl (ty-base-lift (dyck-pre-type dy)) ⟩
  < truncate′ (suc n) (liftType (ty-base (dyck-pre-type dy))) >ty ∎
  where
    open Reasoning ty-setoid

dyck-term-inc-1 n End b = refl≃tm
dyck-term-inc-1 n (⇑ dy) b = refl≃tm
dyck-term-inc-1 n (⇓ dy) b = begin
  < ty-tgt (dyck-type (dyck-bd-1 n dy)) [ dyck-inc-1 n dy b ]tm >tm
    ≈⟨ ty-tgt-sub (dyck-type (dyck-bd-1 n dy)) (dyck-inc-1 n dy b) (<-transˡ 0<1+n (≤-reflexive (sym (dyck-type-dim (dyck-bd-1 n dy))))) ⟩
  < ty-tgt (dyck-type (dyck-bd-1 n dy) [ dyck-inc-1 n dy b ]ty) >tm
    ≈⟨ ty-tgt-≃ (dyck-type-inc-1 n dy b) ⟩
  < ty-tgt (dyck-type dy) >tm ∎
  where
    open Reasoning tm-setoid

dyck-type-bd-2 : (n : ℕ) → (dy : Dyck m (n + d)) → dyck-type (dyck-bd-2 n dy) ≃ty dyck-to-ctx (dyck-bd-2 n dy) ‼ zero
dyck-type-bd-2 zero End = refl≃ty
dyck-type-bd-2 zero (⇑ dy) = refl≃ty
dyck-type-bd-2 zero (⇓ dy) = dyck-type-bd-2 1 dy
dyck-type-bd-2 (suc n) (⇑ dy) = dyck-type-bd-2 n dy
dyck-type-bd-2 (suc n) (⇓ dy) = dyck-type-bd-2 (suc (suc n)) dy

dyck-bd-1-≃ : (n : ℕ) → {ey : Dyck m d} → dy ≃d ey → dyck-bd-1 n dy ≃d dyck-bd-1 n ey
dyck-bd-2-≃ : (n : ℕ) → {dy : Dyck m (n + d)} → {ey : Dyck m′ (n + d′)} → dy ≃d ey → dyck-bd-2 n dy ≃d dyck-bd-2 n ey

dyck-bd-1-≃ n End≃ = End≃
dyck-bd-1-≃ n (⇑≃ p) = ⇑≃ (dyck-bd-1-≃ (suc n) p)
dyck-bd-1-≃ zero (⇓≃ p) = dyck-bd-2-≃ 1 p
dyck-bd-1-≃ (suc n) (⇓≃ p) = ⇓≃ (dyck-bd-1-≃ n p)

dyck-bd-2-≃ zero p = dyck-bd-1-≃ 0 p
dyck-bd-2-≃ (suc n) (⇑≃ p) = dyck-bd-2-≃ n p
dyck-bd-2-≃ (suc n) (⇓≃ p) = dyck-bd-2-≃ (suc (suc n)) p

dyck-cond : ℕ → ℕ → Set
dyck-cond zero zero = ⊥
dyck-cond zero (suc m) = ⊤
dyck-cond (suc n) m = ⊤

dyck-cond-suc : (n m : ℕ) → dyck-cond n (suc m)
dyck-cond-suc zero m = tt
dyck-cond-suc (suc n) m = tt

dyck-subst-⇑ : (p : d′ ≡ d) → (dy : Dyck n d) → subst (Dyck (suc n)) (sym (cong suc p)) (⇑ dy) ≃d ⇑ (subst (Dyck n) (sym p) dy)
dyck-subst-⇑ refl dy = refl≃d

dyck-subst-⇓ : (p : d′ ≡ d) → (dy : Dyck n (suc d)) → subst (Dyck n) (sym p) (⇓ dy) ≃d ⇓ (subst (Dyck n) (sym (cong suc p)) dy)
dyck-subst-⇓ refl dy = refl≃d

dyck-bd-1-glob : (n₁ n₂ : ℕ) → (dy : Dyck m d) → n₁ < n₂ → dyck-bd-1 n₁ (dyck-bd-1 n₂ dy) ≃d dyck-bd-1 n₁ dy
dyck-bd-1-2-glob : (n′ : ℕ) → (n : ℕ) → .(dyck-cond n′ n) → (dy : Dyck m (n′ + d)) → dyck-bd-2 n′ (dyck-bd-1 n dy) ≃d dyck-bd-2 n′ dy
dyck-bd-2-glob : (n′ n : ℕ) → (dy : Dyck m (suc n + (suc n′ + d))) → dyck-bd-2 (suc n′) (dyck-bd-2 (suc n) dy) ≃d dyck-bd-2 (suc n + suc n′) (subst (Dyck m) (sym (+-assoc (suc n) (suc n′) d)) dy)

dyck-bd-1-glob n₁ n₂ End p = End≃
dyck-bd-1-glob n₁ n₂ (⇑ dy) p = ⇑≃ (dyck-bd-1-glob (suc n₁) (suc n₂) dy (s≤s p))
dyck-bd-1-glob zero (suc n₂) (⇓ dy) p = dyck-bd-1-2-glob 1 n₂ tt dy
dyck-bd-1-glob (suc n₁) (suc n₂) (⇓ dy) (s≤s p) = ⇓≃ (dyck-bd-1-glob n₁ n₂ dy p)

dyck-bd-1-2-glob zero (suc n) c dy = dyck-bd-1-glob 0 (suc n) dy (s≤s z≤n)
dyck-bd-1-2-glob (suc n′) n c (⇑ dy) = dyck-bd-1-2-glob n′ (suc n) (dyck-cond-suc n′ n) dy
dyck-bd-1-2-glob (suc n′) zero c (⇓ dy) = dyck-bd-2-glob n′ 0 dy
dyck-bd-1-2-glob (suc n′) (suc n) c (⇓ dy) = dyck-bd-1-2-glob (suc (suc n′)) n tt dy

dyck-bd-2-glob n′ zero (⇑ dy) = dyck-bd-1-2-glob (suc n′) 0 tt dy
dyck-bd-2-glob n′ (suc n) (⇑ dy) = trans≃d (dyck-bd-2-glob n′ n dy) (dyck-bd-2-≃ (suc (suc (n + suc n′))) (sym≃d (dyck-subst-⇑ (+-assoc (suc n) (suc n′) _) dy)))
dyck-bd-2-glob n′ zero (⇓ dy) = dyck-bd-2-glob n′ 1 dy
dyck-bd-2-glob n′ (suc n) (⇓ dy) = trans≃d (dyck-bd-2-glob n′ (suc (suc n)) dy) (sym≃d (dyck-bd-2-≃ (suc (suc n + suc n′)) (dyck-subst-⇓ (+-assoc (suc (suc n)) (suc n′) _) dy)))
