{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Dyck.Typing (index : ℕ)
                        (rule : Fin index → Rule)
                        (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                        (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                        (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Dyck
open import Catt.Typing.Properties.Lifting index rule lift-rule
open import Catt.Globular
open import Catt.Globular.Typing index rule lift-rule
open import Catt.Typing.Properties.Substitution index rule lift-rule susp-rule sub-rule
open import Catt.Globular.Properties
open import Catt.Dyck.Properties
open import Catt.Syntax.SyntacticEquality
open P index rule

dyck-to-ctx-Ty : (dy : Dyck n d) → Typing-Ctx (dyck-to-ctx dy)
dyck-type-Ty : (dy : Dyck n d) → Typing-Ty (dyck-to-ctx dy) (dyck-type dy)
dyck-term-Ty : (dy : Dyck n d) → Typing-Tm (dyck-to-ctx dy) (dyck-term dy) (dyck-type dy)
dyck-pre-type-Ty : (dy : Dyck n d) → Typing-Ty (dyck-to-ctx dy , dyck-type dy)
      (liftTerm (dyck-term dy) ─⟨ liftType (dyck-type dy) ⟩⟶ 0V)
dyck-pre-type-Ty dy = TyArr (lift-tm-typing (dyck-term-Ty dy)) (lift-ty-typing (dyck-type-Ty dy)) (TyVarZ (dyck-type-Ty dy) refl≈ty)

dyck-to-ctx-Ty End = TyAdd TyEmp TyStar
dyck-to-ctx-Ty (⇑ dy) = TyAdd (TyAdd (dyck-to-ctx-Ty dy) (dyck-type-Ty dy)) (dyck-pre-type-Ty dy)
dyck-to-ctx-Ty (⇓ dy) = dyck-to-ctx-Ty dy

dyck-type-Ty End = TyStar
dyck-type-Ty (⇑ dy) = lift-ty-typing (TyArr (lift-tm-typing (dyck-term-Ty dy)) (lift-ty-typing (dyck-type-Ty dy)) (TyVarZ (dyck-type-Ty dy) refl≈ty))
dyck-type-Ty (⇓ dy) = transport-typing-ty (ty-base-Ty (dyck-type-Ty dy) (<-transˡ 0<1+n (≤-reflexive (sym (dyck-type-dim dy))))) refl≃c (ty-base-lift (dyck-pre-type dy))

dyck-term-Ty End = TyVarZ TyStar refl≈ty
dyck-term-Ty (⇑ dy) = TyVarZ (dyck-pre-type-Ty dy) refl≈ty
dyck-term-Ty (⇓ dy) = term-conversion (ty-tgt-Ty (dyck-type-Ty dy) (<-transˡ 0<1+n (≤-reflexive (sym (dyck-type-dim dy))))) (reflexive≈ty (ty-base-lift (dyck-pre-type dy)))

{-
dyck-inc-1-Ty : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → Typing-Sub (dyck-to-ctx (dyck-bd-1 n dy)) (dyck-to-ctx dy) (dyck-inc-1 n dy b)
dyck-inc-2-Ty : (n : ℕ) → (dy : Dyck m (n + d)) → (b : Bool) → Typing-Sub (dyck-to-ctx (dyck-bd-2 n dy)) (dyck-to-ctx dy) (dyck-inc-2 n dy b)

dyck-inc-1-Ty n End b = id-Ty (TyAdd TyEmp TyStar)

dyck-inc-1-Ty n (⇑ dy) b = TyExt (TyExt (lift-sub-typing (lift-sub-typing (dyck-inc-1-Ty (suc n) dy b))) (dyck-type-Ty (dyck-bd-1 (suc n) dy)) (term-conversion (var-Ty (dyck-to-ctx-Ty (⇑ dy)) (suc zero)) (reflexive≈ty l1))) (dyck-pre-type-Ty (dyck-bd-1 (suc n) dy)) (term-conversion (var-Ty (dyck-to-ctx-Ty (⇑ dy)) zero) (reflexive≈ty (Arr≃ l2 l3 refl≃tm)))
  where
    l1 : liftType (liftType (dyck-type dy)) ≃ty
           (dyck-type (dyck-bd-1 (suc n) dy) [
            liftSub (liftSub (dyck-inc-1 (suc n) dy b)) ]ty)
    l1 = begin
      < liftType (liftType (dyck-type dy)) >ty
        ≈˘⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc-1 (suc n) dy b)) ⟩
      < liftType (liftType (dyck-type (dyck-bd-1 (suc n) dy) [ dyck-inc-1 (suc n) dy b ]ty)) >ty
        ≈˘⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-1 (suc n) dy)) (dyck-inc-1 (suc n) dy b)) ⟩
      < liftType (dyck-type (dyck-bd-1 (suc n) dy) [ liftSub (dyck-inc-1 (suc n) dy b) ]ty) >ty
        ≈˘⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd-1 (suc n) dy)) (liftSub (dyck-inc-1 (suc n) dy b)) ⟩
      < dyck-type (dyck-bd-1 (suc n) dy) [ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) ]ty >ty ∎
      where
        open Reasoning ty-setoid

    l2 : liftTerm (liftTerm (dyck-term dy)) ≃tm
           (liftTerm (dyck-term (dyck-bd-1 (suc n) dy)) [
            ⟨ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) , 1V ⟩ ]tm)
    l2 = begin
      < liftTerm (liftTerm (dyck-term dy)) >tm
        ≈˘⟨ lift-tm-≃ (lift-tm-≃ (dyck-term-inc-1 n dy b)) ⟩
      < liftTerm (liftTerm (dyck-term (dyck-bd-1 (suc n) dy) [ dyck-inc-1 (suc n) dy b ]tm)) >tm
        ≈˘⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ (dyck-term (dyck-bd-1 (suc n) dy)) (dyck-inc-1 (suc n) dy b)) ⟩
      < liftTerm (dyck-term (dyck-bd-1 (suc n) dy) [ liftSub (dyck-inc-1 (suc n) dy b) ]tm) >tm
        ≈˘⟨ apply-lifted-sub-tm-≃ (dyck-term (dyck-bd-1 (suc n) dy)) (liftSub (dyck-inc-1 (suc n) dy b)) ⟩
      < dyck-term (dyck-bd-1 (suc n) dy) [ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) ]tm >tm
        ≈˘⟨ lift-sub-comp-lem-tm (liftSub (liftSub (dyck-inc-1 (suc n) dy b))) (dyck-term (dyck-bd-1 (suc n) dy)) ⟩
      < liftTerm (dyck-term (dyck-bd-1 (suc n) dy))
        [ ⟨ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) , 1V ⟩ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l3 : liftType (liftType (dyck-type dy)) ≃ty
           (liftType (dyck-type (dyck-bd-1 (suc n) dy)) [
            ⟨ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) , 1V ⟩ ]ty)
    l3 = begin
      < liftType (liftType (dyck-type dy)) >ty
        ≈⟨ l1 ⟩
      < dyck-type (dyck-bd-1 (suc n) dy) [ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) ]ty >ty
        ≈˘⟨ lift-sub-comp-lem-ty (liftSub (liftSub (dyck-inc-1 (suc n) dy b))) (dyck-type (dyck-bd-1 (suc n) dy)) ⟩
      < liftType (dyck-type (dyck-bd-1 (suc n) dy))
        [ ⟨ liftSub (liftSub (dyck-inc-1 (suc n) dy b)) , 1V ⟩ ]ty >ty ∎
      where
        open Reasoning ty-setoid
dyck-inc-1-Ty zero (⇓ dy) false = dyck-inc-2-Ty 1 dy false
dyck-inc-1-Ty {m = zero} zero (⇓ dy) true = dyck-inc-2-Ty 1 dy true
dyck-inc-1-Ty {m = suc m} zero (⇓ dy) true = replaceSub-Ty (dyck-inc-2-Ty 1 dy true) (term-conversion (dyck-term-Ty (⇓ dy)) (reflexive≈ty lem))
  where
    lem : dyck-type (⇓ dy) ≃ty
            (dyck-to-ctx (dyck-bd-1 zero (⇓ dy)) ‼ zero [ dyck-inc-2 1 dy true
             ]ty)
    lem = begin
      < dyck-type (⇓ dy) >ty
        ≈˘⟨ ty-base-lift (dyck-pre-type dy) ⟩
      < ty-base (liftType (dyck-pre-type dy)) >ty
        ≈˘⟨ dyck-type-inc-2 1 dy true ⟩
      < dyck-type (dyck-bd-2 1 dy) [ dyck-inc-2 1 dy true ]ty >ty
        ≈⟨ sub-action-≃-ty (dyck-type-bd-2 1 dy) refl≃s ⟩
      < dyck-to-ctx (dyck-bd-2 1 dy) ‼ zero [ dyck-inc-2 1 dy true ]ty >ty ∎
      where
        open Reasoning ty-setoid
dyck-inc-1-Ty (suc n) (⇓ dy) b = dyck-inc-1-Ty n dy b

dyck-inc-2-Ty zero dy b = dyck-inc-1-Ty zero dy b
dyck-inc-2-Ty (suc n) (⇑ dy) b = lift-sub-typing (lift-sub-typing (dyck-inc-2-Ty n dy b))
dyck-inc-2-Ty (suc n) (⇓ dy) b = dyck-inc-2-Ty (suc (suc n)) dy b
-}
-- dyck-inc-Ty : (n : ℕ) → (dy : Dyck m d) → (b : Bool) → Typing-Sub (dyck-to-ctx (dyck-bd n dy)) (dyck-to-ctx dy) (dyck-inc n dy b)
-- dyck-inc-Ty {m = zero} n End b = id-Ty (TyAdd TyEmp TyStar)
-- dyck-inc-Ty {m = zero} n (⇓ dy) b = ⊥-elim (dyck-zero-lem dy)
-- dyck-inc-Ty {m = suc m} n (⇑ dy) b = TyExt (TyExt (lift-sub-typing (lift-sub-typing (dyck-inc-Ty (suc n) dy b))) (dyck-type-Ty (dyck-bd (suc n) dy)) (term-conversion (var-Ty (dyck-to-ctx-Ty (⇑ dy)) (suc zero)) (reflexive≈ty l1))) (dyck-pre-type-Ty (dyck-bd (suc n) dy)) (term-conversion (var-Ty (dyck-to-ctx-Ty (⇑ dy)) zero) (reflexive≈ty (Arr≃ l2 l3 refl≃tm)))

--   where
--     l1 : liftType (liftType (dyck-type dy)) ≃ty
--            (dyck-type (dyck-bd (suc n) dy) [
--             liftSub (liftSub (dyck-inc (suc n) dy b)) ]ty)
--     l1 = begin
--       < liftType (liftType (dyck-type dy)) >ty
--         ≈˘⟨ lift-ty-≃ (lift-ty-≃ (dyck-type-inc (suc n) dy b)) ⟩
--       < liftType (liftType (dyck-type (dyck-bd (suc n) dy) [ dyck-inc (suc n) dy b ]ty)) >ty
--         ≈˘⟨ lift-ty-≃ (apply-lifted-sub-ty-≃ (dyck-type (dyck-bd (suc n) dy)) (dyck-inc (suc n) dy b)) ⟩
--       < liftType (dyck-type (dyck-bd (suc n) dy) [ liftSub (dyck-inc (suc n) dy b) ]ty) >ty
--         ≈˘⟨ apply-lifted-sub-ty-≃ (dyck-type (dyck-bd (suc n) dy)) (liftSub (dyck-inc (suc n) dy b)) ⟩
--       < dyck-type (dyck-bd (suc n) dy) [ liftSub (liftSub (dyck-inc (suc n) dy b)) ]ty >ty ∎
--       where
--         open Reasoning ty-setoid

--     l2 : liftTerm (liftTerm (dyck-term dy)) ≃tm
--            (liftTerm (dyck-term (dyck-bd (suc n) dy)) [
--             ⟨ liftSub (liftSub (dyck-inc (suc n) dy b)) , 1V ⟩ ]tm)
--     l2 = begin
--       < liftTerm (liftTerm (dyck-term dy)) >tm
--         ≈˘⟨ lift-tm-≃ (lift-tm-≃ (dyck-term-inc n dy b)) ⟩
--       < liftTerm (liftTerm (dyck-term (dyck-bd (suc n) dy) [ dyck-inc (suc n) dy b ]tm)) >tm
--         ≈˘⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ (dyck-term (dyck-bd (suc n) dy)) (dyck-inc (suc n) dy b)) ⟩
--       < liftTerm (dyck-term (dyck-bd (suc n) dy) [ liftSub (dyck-inc (suc n) dy b) ]tm) >tm
--         ≈˘⟨ apply-lifted-sub-tm-≃ (dyck-term (dyck-bd (suc n) dy)) (liftSub (dyck-inc (suc n) dy b)) ⟩
--       < dyck-term (dyck-bd (suc n) dy) [ liftSub (liftSub (dyck-inc (suc n) dy b)) ]tm >tm
--         ≈˘⟨ lift-sub-comp-lem-tm (liftSub (liftSub (dyck-inc (suc n) dy b))) (dyck-term (dyck-bd (suc n) dy)) ⟩
--       < liftTerm (dyck-term (dyck-bd (suc n) dy))
--         [ ⟨ liftSub (liftSub (dyck-inc (suc n) dy b)) , 1V ⟩ ]tm >tm ∎
--       where
--         open Reasoning tm-setoid

--     l3 : liftType (liftType (dyck-type dy)) ≃ty
--            (liftType (dyck-type (dyck-bd (suc n) dy)) [
--             ⟨ liftSub (liftSub (dyck-inc (suc n) dy b)) , 1V ⟩ ]ty)
--     l3 = begin
--       < liftType (liftType (dyck-type dy)) >ty
--         ≈⟨ l1 ⟩
--       < dyck-type (dyck-bd (suc n) dy) [ liftSub (liftSub (dyck-inc (suc n) dy b)) ]ty >ty
--         ≈˘⟨ lift-sub-comp-lem-ty (liftSub (liftSub (dyck-inc (suc n) dy b))) (dyck-type (dyck-bd (suc n) dy)) ⟩
--       < liftType (dyck-type (dyck-bd (suc n) dy))
--         [ ⟨ liftSub (liftSub (dyck-inc (suc n) dy b)) , 1V ⟩ ]ty >ty ∎
--       where
--         open Reasoning ty-setoid

-- dyck-inc-Ty {m = suc m} zero (⇓ dy) false = transport-typing-sub (lift-sub-typing (lift-sub-typing (dyck-inc-Ty zero (trim dy) false))) refl≃c (sym≃c (dyck-ctx-split dy)) refl≃s
-- dyck-inc-Ty {m = suc m} zero (⇓ dy) true = replaceSub-Ty (transport-typing-sub (lift-sub-typing (lift-sub-typing (dyck-inc-Ty zero (trim dy) true))) refl≃c (sym≃c (dyck-ctx-split dy)) refl≃s) (term-conversion (var-Ty (dyck-to-ctx-Ty dy) (suc zero)) (reflexive≈ty {!!}))

-- dyck-inc-Ty {m = suc m} (suc n) (⇓ dy) b = dyck-inc-Ty n dy b
