open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Label.Typing (index : ℕ)
                              (rule : Fin index → Rule)
                              (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                              (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                              (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Path.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Tree.Properties
open import Catt.Tree.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Suspension
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing index rule lift-rule

data Typing-Label : (ΓS : CtxOrTree m) → Label (COT-to-MT ΓS) S A → Set where
  TySing : {L : Label (COT-to-MT ΓS) Sing A} → Typing-Path ΓS (ap L PPHere) A → Typing-Label ΓS L
  TyJoin : Typing-Path ΓS (ap L PPHere) (lty L)
         → Typing-Label ΓS (label₁ L)
         → Typing-Label ΓS (label₂ L)
         → Typing-Label ΓS L

ap-pphere-Ty : Typing-Label ΓS L → Typing-Path ΓS (ap L PPHere) (lty L)
ap-pphere-Ty (TySing xty) = xty
ap-pphere-Ty (TyJoin xty Lty Mty) = xty

apt-pphere-Ty : Typing-Label ΓS L → Typing-Tm (COT-to-Ctx ΓS) (apt L PPHere) (lty L)
apt-pphere-Ty Lty = path-to-term-Ty (ap-pphere-Ty Lty)

label₁-Ty : Typing-Label ΓS L → Typing-Label ΓS (label₁ L)
label₁-Ty (TyJoin x Lty Mty) = Lty

label₂-Ty : Typing-Label ΓS L → Typing-Label ΓS (label₂ L)
label₂-Ty (TyJoin x Lty Mty) = Mty

convert-type-Ty : Typing-Label ΓS L
                → lty L ≈[ COT-to-Ctx ΓS ]ty B
                → Typing-Label ΓS (convert-type L B)
convert-type-Ty (TySing x) p = TySing (TyPConv x p)
convert-type-Ty (TyJoin x Lty Mty) p = TyJoin (TyPConv x p) (convert-type-Ty Lty (Arr≈ refl≈tm p refl≈tm)) (convert-type-Ty Mty p)

label-to-sub-Ty : Typing-Label ΓS L
                → Typing-Ty (COT-to-Ctx ΓS) (lty L)
                → Typing-Sub (tree-to-ctx (ltree L)) (COT-to-Ctx ΓS) (label-to-sub L)
label-to-sub-Ty (TySing xty) Aty = TyExt (TyNull Aty) (path-to-term-Ty xty)
label-to-sub-Ty {L = L} (TyJoin xty Lty Mty) Aty
  = sub-from-connect-Ty (unrestrictTy (label-to-sub-Ty Lty (TyArr (path-to-term-Ty xty) Aty (apt-pphere-Ty Mty))))
                        getSndTy
                        (label-to-sub-Ty Mty Aty)
                        (reflexive≈tm (label-to-sub-lem L))

map-pext-Ty : Typing-Label (incTree S) L
            → Typing-Label (incTree (Join S T)) (map-pext L)
map-pext-Ty (TySing xty) = TySing (TyExt xty)
map-pext-Ty (TyJoin xty Lty Mty) = TyJoin (TyExt xty) (map-pext-Ty Lty) (map-pext-Ty Mty)

map-pshift-Ty : Typing-Label (incTree T) L
              → Typing-Label (incTree (Join S T)) (map-pshift L)
map-pshift-Ty (TySing xty) = TySing (TyShift xty)
map-pshift-Ty (TyJoin xty Lty Mty) = TyJoin (TyShift xty) (map-pshift-Ty Lty) (map-pshift-Ty Mty)

id-label-Ty : (S : Tree n) → Typing-Label (incTree S) (id-label S)
id-label-Ty Sing = TySing TyHere
id-label-Ty (Join S₁ S₂) = TyJoin TyHere
                                  (convert-type-Ty (map-pext-Ty (id-label-Ty S₁)) (reflexive≈ty (Arr≃ (connect-inc-left-fst-var getSnd (tree-size S₂))
                                                                                                      refl≃ty
                                                                                                      (connect-inc-fst-var getSnd (tree-size S₂)))))
                                  (map-pshift-Ty (id-label-Ty S₂))

label-sub-Ty : Typing-Label ΓS L
                  → Typing-Sub (COT-to-Ctx ΓS) (COT-to-Ctx ΔT) σ
                  → Typing-Label ΔT (label-sub L (COT-to-MT ΔT) σ)
label-sub-Ty (TySing xty) σty = TySing (TyOther (apply-sub-tm-typing (path-to-term-Ty xty) σty))
label-sub-Ty (TyJoin xty Lty Mty) σty = TyJoin (TyOther (apply-sub-tm-typing (path-to-term-Ty xty) σty)) (label-sub-Ty Lty σty) (label-sub-Ty Mty σty)

to-label-Ty : (S : Tree n) → (ΓS : CtxOrTree m) → Typing-Sub (tree-to-ctx S) (COT-to-Ctx ΓS) σ → Typing-Label ΓS (to-label S σ (COT-to-MT ΓS))
to-label-Ty S ΓS σty = label-sub-Ty (id-label-Ty S) σty

{-
transport-label-typing : Typing-Label ΓS L A → L ≃l M → A ≈[ COT-to-Ctx ΓS ]ty B → Typing-Label ΓS M B
transport-label-typing (TySing x) (LSing≃ y) q = TySing (transport-path-typing x y q)
transport-label-typing (TyJoin x Lty Mty) (LJoin≃ y p p′) q
  = TyJoin (transport-path-typing x y q)
           (transport-label-typing Lty p (Arr≈ (reflexive≈tm (path-to-term-≃ y)) q (reflexive≈tm (path-to-term-≃ (first-label-≃ p′)))))
           (transport-label-typing Mty p′ q)

label-eq-conv : (L : Label X S) → A ≈[ Γ ]ty B → label-to-sub L A ≈[ Γ ]s label-to-sub L B
label-eq-conv (LSing x) p = Ext≈ (Null≈ p) refl≈tm
label-eq-conv (LJoin x L M) p = sub-from-connect-≈ (unrestrictEq (label-eq-conv L (Arr≈ refl≈tm p refl≈tm))) (label-eq-conv M p)
-}
connect-label-Ty : (Lty : Typing-Label ΓS L)
                 → (Mty : Typing-Label ΓS M)
                 → apt L (last-path S) ≈[ COT-to-Ctx ΓS ]tm apt M PPHere
                 → Typing-Label ΓS (connect-label L M)
connect-label-Ty (TySing x) (TySing y) p = TySing x
connect-label-Ty (TySing x) (TyJoin y Mty Mty′) p = TyJoin x (convert-type-Ty Mty (Arr≈ (sym≈tm p) refl≈ty refl≈tm)) Mty′
connect-label-Ty (TyJoin x Lty Lty′) Mty p = TyJoin x Lty (connect-label-Ty Lty′ Mty p)

connect-tree-inc-left-Ty : (S : Tree n)
                         → (T : Tree m)
                         → Typing-Label (incTree (connect-tree S T)) (connect-tree-inc-left S T)
connect-tree-inc-left-Ty Sing T = TySing TyHere
connect-tree-inc-left-Ty (Join S₁ S₂) T
  = TyJoin TyHere (convert-type-Ty (map-pext-Ty (id-label-Ty S₁)) (reflexive≈ty (Arr≃ (connect-inc-left-fst-var getSnd (connect-tree-length S₂ T))
                                                                                      refl≃ty
                                                                                      lem)))
                  (map-pshift-Ty (connect-tree-inc-left-Ty S₂ T))
    where
      open Reasoning tm-setoid
      lem : getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm
          ≃tm apt (connect-tree-inc-left (Join S₁ S₂) T) (PPShift PPHere)
      lem = begin
        < getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
          ≈⟨ connect-inc-fst-var getSnd (connect-tree-length S₂ T) ⟩
        < Var (fromℕ (connect-tree-length S₂ T)) [ connect-susp-inc-right (tree-size S₁) (connect-tree-length S₂ T) ]tm >tm
          ≈˘⟨ sub-action-≃-tm (path-to-term-≃ (connect-tree-inc-left-pphere S₂ T)) refl≃s ⟩
        < apt (connect-tree-inc-left S₂ T) PPHere
          [ connect-susp-inc-right (tree-size S₁) (connect-tree-length S₂ T) ]tm >tm ∎

connect-tree-inc-right-Ty : (S : Tree n)
                          → (T : Tree m)
                          → Typing-Label (incTree (connect-tree S T)) (connect-tree-inc-right S T)
connect-tree-inc-right-Ty Sing T = id-label-Ty T
connect-tree-inc-right-Ty (Join S₁ S₂) T = map-pshift-Ty (connect-tree-inc-right-Ty S₂ T)

{-
-- label-index-Ty : Typing-Label ΓS L A
--                → Typing-Ty (COT-to-Ctx ΓS) A
--                → Typing-Path (incTree (label-to-tree L)) P B
--                → Typing-Path ΓS (L ‼< A > P) (B [ label-to-sub L A ]ty)
-- label-index-Ty Lty Aty (TyPConv Pty p) = TyPConv (label-index-Ty Lty Aty Pty) (apply-sub-ty-eq (label-typing-to-sub Lty Aty) p)
-- label-index-Ty Lty Aty (TyOther tty) = TyOther (apply-sub-tm-typing tty (label-typing-to-sub Lty Aty))
-- label-index-Ty Lty Aty TyHere = first-label-Ty Lty
-- label-index-Ty {A = A} (TyJoin {P = P} {L = L} {M = M} x Lty Mty) Aty (TyExt {A = B} Pty)
--   = TyPConv (label-index-Ty Lty (TyArr (path-to-term-Ty x) Aty (first-label-term-Ty Mty)) Pty) (reflexive≈ty lem)
--   where
--     open Reasoning ty-setoid

--     lem : B [ label-to-sub L (path-to-term P ─⟨ A ⟩⟶ path-to-term (first-label M)) ]ty
--           ≃ty suspTy B [ connect-susp-inc-left _ _ ]ty
--                        [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A) ]ty
--     lem = begin
--       < B [ label-to-sub L (path-to-term P ─⟨ A ⟩⟶ path-to-term (first-label M)) ]ty >ty
--         ≈˘⟨ unrestrict-comp-ty B (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M)) ⟩
--       < suspTy B [ unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M)) ]ty >ty
--         ≈˘⟨ sub-action-≃-ty refl≃ty (sub-from-connect-inc-left (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) getSnd (label-to-sub M A)) ⟩
--       < suspTy B [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A)
--                  ∘ connect-susp-inc-left _ _ ]ty >ty
--         ≈⟨ assoc-ty _ _ (suspTy B) ⟩
--       < suspTy B [ connect-susp-inc-left _ _ ]ty
--                  [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A) ]ty >ty ∎

-- label-index-Ty {A = A} (TyJoin {P = P} {L = L} {M = M} x Lty Mty) Aty (TyShift {A = B} Pty)
--   = TyPConv (label-index-Ty Mty Aty Pty) (reflexive≈ty lem)
--   where
--     open Reasoning ty-setoid

--     lem : (B [ label-to-sub M A ]ty) ≃ty
--           B [ connect-susp-inc-right _ _ ]ty
--             [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A) ]ty
--     lem = begin
--       < B [ label-to-sub M A ]ty >ty
--         ≈˘⟨ sub-action-≃-ty refl≃ty (sub-from-connect-inc-right (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) getSnd (label-to-sub M A) (trans≃tm (unrestrict-snd (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (first-label-prop M A))) ⟩
--       < B [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A)
--           ∘ connect-susp-inc-right _ _ ]ty >ty
--         ≈⟨ assoc-ty _ _ B ⟩
--       < B [ connect-susp-inc-right _ _ ]ty
--           [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A) ]ty >ty ∎
-}

extend-Ty : Typing-Path (incTree S) P A → Typing-Label ΓS L → Typing-Ty (COT-to-Ctx ΓS) (lty L) → Typing-Path ΓS (P >>= L) (A [ label-to-sub L ]ty)
extend-Ty (TyPConv Pty x) Lty Aty = TyPConv (extend-Ty Pty Lty Aty) (apply-sub-ty-eq (label-to-sub-Ty Lty Aty) x)
extend-Ty TyHere Lty Aty = ap-pphere-Ty Lty
extend-Ty {L = L} (TyExt {A = A} Pty) Lty Aty = TyPConv (extend-Ty Pty (label₁-Ty Lty) (TyArr (apt-pphere-Ty Lty) Aty (apt-pphere-Ty (label₂-Ty Lty)))) (reflexive≈ty lem)
  where
    open Reasoning ty-setoid
    lem : A [ label-to-sub (label₁ L) ]ty
      ≃ty suspTy A [ connect-susp-inc-left _ _ ]ty
                   [ label-to-sub L ]ty
    lem = begin
      < A [ label-to-sub (label₁ L) ]ty >ty
        ≈˘⟨ unrestrict-comp-ty A (label-to-sub (label₁ L)) ⟩
      < suspTy A [ unrestrict (label-to-sub (label₁ L)) ]ty >ty
        ≈˘⟨ sub-action-≃-ty (refl≃ty {A = suspTy A}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L))) ⟩
      < suspTy A [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))
                 ∘ connect-susp-inc-left _ _ ]ty >ty
        ≈⟨ assoc-ty _ _ (suspTy A) ⟩
      < suspTy A [ connect-susp-inc-left _ _ ]ty
                 [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]ty >ty ∎
extend-Ty {L = L} (TyShift {A = A} Pty) Lty Aty = TyPConv (extend-Ty Pty (label₂-Ty Lty) Aty) (reflexive≈ty lem)
  where
    open Reasoning ty-setoid
    lem : A [ label-to-sub (label₂ L) ]ty
      ≃ty A [ connect-susp-inc-right _ _ ]ty
            [ label-to-sub L ]ty
    lem = begin
      < A [ label-to-sub (label₂ L) ]ty >ty
        ≈˘⟨ sub-action-≃-ty (refl≃ty {A = A}) (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L)) (label-to-sub-lem L)) ⟩
      < A [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))
          ∘ connect-susp-inc-right _ _ ]ty >ty
        ≈⟨ assoc-ty _ _ A ⟩
      < A [ connect-susp-inc-right _ _ ]ty
          [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]ty >ty ∎
extend-Ty (TyOther x) Lty Aty = TyOther (apply-sub-tm-typing x (label-to-sub-Ty Lty Aty))

label-comp-Ty : Typing-Label (incTree T) L
              → Typing-Label ΓS M
              → Typing-Ty (COT-to-Ctx ΓS) (lty M)
              → Typing-Label ΓS (label-comp L M)
label-comp-Ty (TySing x) Mty Aty = TySing (extend-Ty x Mty Aty)
label-comp-Ty {L = L} {M = M} (TyJoin x Lty Lty′) Mty Aty
  = TyJoin (extend-Ty x Mty Aty)
           (convert-type-Ty (label-comp-Ty Lty Mty Aty) (reflexive≈ty (Arr≃ (label-to-sub-path M (ap L PPHere)) refl≃ty (label-to-sub-path M (ap L (PPShift PPHere))))))
           (label-comp-Ty Lty′ Mty Aty)


label-between-connect-trees-Ty : Typing-Label (incTree S′) L
                               → Typing-Label (incTree T′) M
                               → apt L (last-path S) ≈[ tree-to-ctx S′ ]tm tree-last-var S′
                               → apt M PPHere ≈[ tree-to-ctx T′ ]tm Var (fromℕ (tree-size T′))
                               → Typing-Label (incTree (connect-tree S′ T′)) (label-between-connect-trees L M)
label-between-connect-trees-Ty {S′ = S′} {S = S} {L = L} {T′ = T′} {M = M} Lty Mty p q
  = connect-label-Ty (label-comp-Ty Lty (connect-tree-inc-left-Ty _ _) TyStar)
                     (label-comp-Ty Mty (connect-tree-inc-right-Ty _ _) TyStar)
                     {!!}
  where
    open Reasoning (tm-setoid-≈ _)

    lem : path-to-term (ap L (last-path S) >>= connect-tree-inc-left S′ T′)
        ≈[ tree-to-ctx (connect-tree S′ T′) ]tm
          path-to-term (ap M ⟦ PHere ⟧ >>= connect-tree-inc-right S′ T′)
    lem = begin
      path-to-term (ap L (last-path S) >>= connect-tree-inc-left S′ T′)
        ≈˘⟨ reflexive≈tm (label-to-sub-path (connect-tree-inc-left S′ T′) (ap L (last-path S))) ⟩
      apt L (last-path S) [ label-to-sub (connect-tree-inc-left S′ T′) ]tm
        ≈⟨ apply-sub-tm-eq (label-to-sub-Ty (connect-tree-inc-left-Ty S′ T′) TyStar) p ⟩
      tree-last-var S′ [ label-to-sub (connect-tree-inc-left S′ T′) ]tm
        ≈˘⟨ reflexive≈tm (sub-action-≃-tm (last-path-to-term S′) refl≃s) ⟩
      path-to-term (carrier (last-path S′)) [ label-to-sub (connect-tree-inc-left S′ T′) ]tm
        ≈⟨ reflexive≈tm (label-to-sub-ppath (connect-tree-inc-left S′ T′) (last-path S′)) ⟩
      apt (connect-tree-inc-left S′ T′) (last-path S′)
        ≈⟨ reflexive≈tm (path-to-term-≃ (connect-tree-inc-pphere S′ T′)) ⟩
      apt (connect-tree-inc-right S′ T′) PPHere
        ≈˘⟨ reflexive≈tm (label-to-sub-ppath (connect-tree-inc-right S′ T′) PPHere) ⟩
      Var (fromℕ (tree-size T′)) [ label-to-sub (connect-tree-inc-right S′ T′) ]tm
        ≈˘⟨ apply-sub-tm-eq (label-to-sub-Ty (connect-tree-inc-right-Ty S′ T′) TyStar) q ⟩
      apt M PPHere [ label-to-sub (connect-tree-inc-right S′ T′) ]tm
        ≈⟨ reflexive≈tm (label-to-sub-path (connect-tree-inc-right S′ T′) (ap M PPHere)) ⟩
      path-to-term (ap M PPHere >>= connect-tree-inc-right S′ T′) ∎

label-between-joins-Ty : Typing-Label (incTree S′) L
                       → Typing-Label (incTree T′) M
                       → apt M PPHere ≈[ tree-to-ctx T′ ]tm Var (fromℕ (tree-size T′))
                       → Typing-Label (incTree (Join S′ T′)) (label-between-joins L M)
label-between-joins-Ty {S′ = S′} {L = L} {T′ = T′} {M = M} Lty Mty p
  = TyJoin TyHere (convert-type-Ty (map-pext-Ty Lty) (Arr≈ (reflexive≈tm (connect-inc-left-fst-var getSnd _)) refl≈ty lem)) (map-pshift-Ty Mty)
  where
    open Reasoning (tm-setoid-≈ _)
    lem : (getSnd [ connect-susp-inc-left (tree-size S′) (tree-size T′) ]tm) ≈[ _ ]tm apt (label-between-joins L M) (PPShift PPHere)
    lem = begin
      getSnd [ connect-susp-inc-left (tree-size S′) (tree-size T′) ]tm
        ≈⟨ reflexive≈tm (connect-inc-fst-var getSnd (tree-size T′)) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S′) (tree-size T′) ]tm
        ≈˘⟨ apply-sub-tm-eq (connect-susp-inc-right-Ty (tree-to-ctx S′)) p ⟩
      apt M ⟦ PHere ⟧ [ connect-susp-inc-right (tree-size S′) (tree-size T′) ]tm ∎

{-

data _≃Ml<_>_ : Label X S → Bool → Label Y T → Set where
  MlSingf : LSing P ≃Ml< false > LSing Q
  MlSingt : path-to-term P ≃tm path-to-term Q → LSing P ≃Ml< true > LSing Q
  MlJoin : {b : Bool} → L ≃Ml< true > L′ → M ≃Ml< false > M′ → LJoin P L M ≃Ml< b > LJoin Q L′ M′

max-eq-to-eq : {L : Label (COT-to-MT ΓS) S}
             → {M : Label (COT-to-MT ΔT) T}
             → L ≃Ml< true > M
             → Typing-Label ΓS L A
             → Typing-Label ΔT M B
             → (p : COT-to-Ctx ΓS ≃c COT-to-Ctx ΔT)
             → idSub≃ p ∘ label-to-sub L A ≈[ COT-to-Ctx ΔT ]s label-to-sub M B
max-eq-to-eq (MlSingt {P = P} x) (TySing Pty) (TySing Qty) p = let
  eq = trans≃tm (idSub≃-on-tm p (path-to-term P)) x
  in Ext≈ (Null≈ (Ty-unique-≃ eq (apply-sub-tm-typing (path-to-term-Ty Pty) (idSub≃-Ty p)) (path-to-term-Ty Qty))) (reflexive≈tm eq)
max-eq-to-eq {A = A} {B = B} (MlJoin q MlSingf) (TyJoin {P = P} {L = L} Pty Lty (TySing {P = P′} Pty′)) (TyJoin {P = Q} {L = M} Qty Mty (TySing {P = Q′} QTy′)) p = begin
  < idSub≃ p ∘
       unrestrict
       (label-to-sub L
        (path-to-term P ─⟨ A ⟩⟶ first-label-term (LSing P′))) >s′
    ≈˘⟨ reflexive≈s (unrestrict-comp-higher (idSub≃ p) (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ path-to-term P′))) ⟩
  < unrestrict (idSub≃ p ∘ label-to-sub L (path-to-term P ─⟨ A ⟩⟶ path-to-term P′)) >s′
    ≈⟨ unrestrictEq (max-eq-to-eq q Lty Mty p) ⟩
  < unrestrict (label-to-sub M (path-to-term Q ─⟨ B ⟩⟶ first-label-term (LSing Q′))) >s′ ∎
  where
    open Reasoning (sub-setoid-≈ _)
max-eq-to-eq {A = A} {B = B} (MlJoin q q′@(MlJoin a b)) (TyJoin {P = P} {L = L} {M = L′} Pty Lty Lty′) (TyJoin {P = Q} {L = M} {M = M′} Qty Mty Mty′) p = begin
  < idSub≃ p
  ∘ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′)))
                     (label-to-sub L′ A) >s′
    ≈⟨ reflexive≈s (sub-from-connect-sub (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′))) (label-to-sub L′ A) (idSub≃ p)) ⟩
  < sub-from-connect (idSub≃ p ∘ unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′)))
                     (idSub≃ p ∘ label-to-sub L′ A) >s′
    ≈˘⟨ reflexive≈s (sub-from-connect-≃ (unrestrict-comp-higher (idSub≃ p) (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′))) refl≃s) ⟩
  < sub-from-connect
    (unrestrict (idSub≃ p ∘ label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′)))
    (idSub≃ p ∘ label-to-sub L′ A) >s′
    ≈⟨ sub-from-connect-≈ (unrestrictEq (max-eq-to-eq q Lty Mty p)) (max-eq-to-eq (MlJoin a b) Lty′ Mty′ p) ⟩
  < sub-from-connect
    (unrestrict (label-to-sub M (path-to-term Q ─⟨ B ⟩⟶ path-to-term (first-label M′))))
    (label-to-sub M′ B) >s′ ∎
  where
    open Reasoning (sub-setoid-≈ _)

-- connect-label-inc-left : (L : Label X S)
--                        → (M : Label X T)
--                        → label-comp (connect-tree-inc-left S T) (connect-label L M) ≃Ml< true > L
-- connect-label-inc-left (LSing P) M = MlSingt (replace-first-label M P)
-- connect-label-inc-left (LJoin P L L′) M = {!!}
-}
