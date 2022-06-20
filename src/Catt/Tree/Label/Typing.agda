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

data Typing-Label : (Γ : CtxOrTree m) → Label (COT-to-MT Γ) S → (A : Ty m) → Set where
  TySing : Typing-Path ΓS P A → Typing-Label ΓS (LSing P) A
  TyJoin : Typing-Path ΓS P A → Typing-Label ΓS L (path-to-term P ─⟨ A ⟩⟶ path-to-term (M ‼l PPHere)) → Typing-Label ΓS M A → Typing-Label ΓS (LJoin P L M) A

data Typing-Label-func : (ΓS : CtxOrTree m) → Label-func (COT-to-MT ΓS) S → (A : Ty m) → Set where
  TyFSing : {L : Label-func (COT-to-MT ΓS) Sing} → Typing-Path ΓS (L PPHere) A → Typing-Label-func ΓS L A
  TyFJoin : {L : Label-func (COT-to-MT ΓS) (Join S T)}
          → Typing-Path ΓS (L PPHere) A
          → Typing-Label-func ΓS (label-func₁ L) (path-to-term (L PPHere) ─⟨ A ⟩⟶ path-to-term (L (PPShift PPHere)))
          → Typing-Label-func ΓS (label-func₂ L) A
          → Typing-Label-func ΓS L A

label-func-pext-Ty : {L : Label-func (someTree S) U}
                   → Typing-Label-func (incTree S) L A
                   → Typing-Label-func (incTree (Join S T)) (map-label-func PExt L) (suspTy A [ connect-susp-inc-left (tree-size S) (tree-size T) ]ty)
label-func-pext-Ty (TyFSing xty) = TyFSing (TyExt xty)
label-func-pext-Ty (TyFJoin xty Lty Mty) = TyFJoin (TyExt xty) (label-func-pext-Ty Lty) (label-func-pext-Ty Mty)

label-func-pshift-Ty : {L : Label-func (someTree T) U}
                     → Typing-Label-func (incTree T) L A
                     → Typing-Label-func (incTree (Join S T)) (map-label-func PShift L) (A [ connect-susp-inc-right (tree-size S) (tree-size T) ]ty)
label-func-pshift-Ty (TyFSing xty) = TyFSing (TyShift xty)
label-func-pshift-Ty (TyFJoin xty Lty Mty) = TyFJoin (TyShift xty) (label-func-pshift-Ty Lty) (label-func-pshift-Ty Mty)

id-label-func-Ty2 : (S : Tree n) → Typing-Label-func (incTree S) (id-label-func S) ⋆
id-label-func-Ty2 Sing = TyFSing TyHere
id-label-func-Ty2 (Join S₁ S₂) = TyFJoin TyHere {!!} (label-func-pshift-Ty (id-label-func-Ty2 S₂))

label-func-sub-Ty : {L : Label-func (COT-to-MT ΓS) S}
                  → Typing-Label-func ΓS L A
                  → Typing-Sub (COT-to-Ctx ΓS) (COT-to-Ctx ΔT) σ
                  → Typing-Label-func ΔT (map-label-func (λ Z → POther (path-to-term Z [ σ ]tm)) L) (A [ σ ]ty)
label-func-sub-Ty (TyFSing xty) σty = TyFSing (TyOther (apply-sub-tm-typing (path-to-term-Ty xty) σty))
label-func-sub-Ty (TyFJoin xty Lty Mty) σty = TyFJoin (TyOther (apply-sub-tm-typing (path-to-term-Ty xty) σty)) (label-func-sub-Ty Lty σty) (label-func-sub-Ty Mty σty)

to-label-func-Ty : (S : Tree n) → (ΓS : CtxOrTree m) → Typing-Sub (tree-to-ctx S) (COT-to-Ctx ΓS) σ → Typing-Label-func ΓS (to-label-func S σ (COT-to-MT ΓS)) (sub-type σ)
to-label-func-Ty S ΓS σty = label-func-sub-Ty (id-label-func-Ty2 S) σty

first-label-Ty : Typing-Label ΓS L A → Typing-Path ΓS (first-label L) A
first-label-Ty (TySing tty) = tty
first-label-Ty (TyJoin tty Lty Mty) = tty

first-label-term-Ty : Typing-Label ΓS L A → Typing-Tm (COT-to-Ctx ΓS) (first-label-term L) A
first-label-term-Ty Lty = path-to-term-Ty (first-label-Ty Lty)

label-typing-to-sub : Typing-Label ΓS L A → Typing-Ty (COT-to-Ctx ΓS) A → Typing-Sub (tree-to-ctx (label-to-tree L)) (COT-to-Ctx ΓS) (label-to-sub L A)
label-typing-to-sub (TySing tty) Aty = TyExt (TyNull Aty) (path-to-term-Ty tty)
label-typing-to-sub {A = A} (TyJoin {P = P} {L = L} {M = M} tty Lty Mty) Aty
  = sub-from-connect-Ty (unrestrictTy (label-typing-to-sub Lty (TyArr (path-to-term-Ty tty) Aty (first-label-term-Ty Mty)))) getSndTy (label-typing-to-sub Mty Aty) (reflexive≈tm lem)
  where
    open Reasoning tm-setoid
    lem : getSnd [ unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M)) ]tm
          ≃tm Var (fromℕ _) [ label-to-sub M A ]tm
    lem = begin
      < getSnd [ unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M)) ]tm >tm
        ≈⟨ unrestrict-snd (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M)) ⟩
      < first-label-term M >tm
        ≈⟨ first-label-prop M A ⟩
      < Var (fromℕ _) [ label-to-sub M A ]tm >tm ∎

label-typing-conv : Typing-Label ΓS L A → A ≈[ COT-to-Ctx ΓS ]ty B → Typing-Label ΓS L B
label-typing-conv (TySing tty) p = TySing (TyPConv tty p)
label-typing-conv (TyJoin tty Lty Mty) p = TyJoin (TyPConv tty p) (label-typing-conv Lty (Arr≈ refl≈tm p refl≈tm)) (label-typing-conv Mty p)

transport-label-typing : Typing-Label ΓS L A → L ≃l M → A ≈[ COT-to-Ctx ΓS ]ty B → Typing-Label ΓS M B
transport-label-typing (TySing x) (LSing≃ y) q = TySing (transport-path-typing x y q)
transport-label-typing (TyJoin x Lty Mty) (LJoin≃ y p p′) q
  = TyJoin (transport-path-typing x y q)
           (transport-label-typing Lty p (Arr≈ (reflexive≈tm (path-to-term-≃ y)) q (reflexive≈tm (path-to-term-≃ (first-label-≃ p′)))))
           (transport-label-typing Mty p′ q)

label-eq-conv : (L : Label X S) → A ≈[ Γ ]ty B → label-to-sub L A ≈[ Γ ]s label-to-sub L B
label-eq-conv (LSing x) p = Ext≈ (Null≈ p) refl≈tm
label-eq-conv (LJoin x L M) p = sub-from-connect-≈ (unrestrictEq (label-eq-conv L (Arr≈ refl≈tm p refl≈tm))) (label-eq-conv M p)

label-sub-Ty : Typing-Label ΓS L A → Typing-Sub (COT-to-Ctx ΓS) (COT-to-Ctx ΔT) σ → Typing-Label ΔT (L [ σ ]< COT-to-MT ΔT >l) (A [ σ ]ty)
label-sub-Ty (TySing tty) σty = TySing (TyOther (apply-sub-tm-typing (path-to-term-Ty tty) σty))
label-sub-Ty {σ = σ} (TyJoin {M = M} tty Lty Mty) σty
  = TyJoin (TyOther (apply-sub-tm-typing (path-to-term-Ty tty) σty)) (label-typing-conv (label-sub-Ty Lty σty) (reflexive≈ty (Arr≃ refl≃tm refl≃ty (sym≃tm (first-label-sub M σ))))) (label-sub-Ty Mty σty)

label-pext-Ty : Typing-Label (incTree S) L A → Typing-Label (incTree (Join S T)) (map-label PExt L) (suspTy A [ connect-susp-inc-left (tree-size S) (tree-size T) ]ty)
label-pext-Ty (TySing xty) = TySing (TyExt xty)
label-pext-Ty (TyJoin {M = M} xty Lty Mty) = TyJoin (TyExt xty) (label-typing-conv (label-pext-Ty Lty) (reflexive≈ty (Arr≃ refl≃tm refl≃ty (sym≃tm (first-label-term-pext M))))) (label-pext-Ty Mty)

label-pshift-Ty : Typing-Label (incTree T) L A → Typing-Label (incTree (Join S T)) (map-label PShift L) (A [ connect-susp-inc-right (tree-size S) (tree-size T) ]ty)
label-pshift-Ty (TySing xty) = TySing (TyShift xty)
label-pshift-Ty (TyJoin {M = M} xty Lty Mty) = TyJoin (TyShift xty) (label-typing-conv (label-pshift-Ty Lty) (reflexive≈ty (Arr≃ refl≃tm refl≃ty (sym≃tm (first-label-term-pshift M))))) (label-pshift-Ty Mty)

id-label-Ty : (S : Tree n) → Typing-Label (incTree S) (id-label S) ⋆
id-label-Ty Sing = TySing TyHere
id-label-Ty (Join S T)
  = TyJoin TyHere
           (label-typing-conv (label-pext-Ty (id-label-Ty S)) (reflexive≈ty (Arr≃ (connect-inc-left-fst-var getSnd _) refl≃ty lem)))
           (label-pshift-Ty (id-label-Ty T))
  where
    open Reasoning tm-setoid


    lem : getSnd [ connect-susp-inc-left _ _ ]tm
          ≃tm first-label-term (map-label PShift (id-label T))
    lem = begin
      < getSnd [ connect-susp-inc-left _ _ ]tm >tm
        ≈⟨ connect-inc-fst-var getSnd _ ⟩
      < Var (fromℕ _) [ connect-susp-inc-right _ _ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (path-to-term-≃ (id-first-label T)) refl≃s ⟩
      < first-label-term (id-label T) [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm
        ≈˘⟨ first-label-term-pshift (id-label T) ⟩
      < first-label-term (map-label PShift (id-label T)) >tm ∎

id-label-func-Ty : (S : Tree n) → Typing-Label (incTree S) (label-func-to-label (id-label-func S)) ⋆
id-label-func-Ty S = transport-label-typing (id-label-Ty S) (sym≃l (id-label-func-compat S)) refl≈ty

to-label-Ty : (S : Tree n) → Typing-Sub (tree-to-ctx S) (COT-to-Ctx ΔT) σ → Typing-Label ΔT (to-label S σ (COT-to-MT ΔT)) (sub-type σ)
to-label-Ty S σty = label-sub-Ty (id-label-Ty S) σty

replace-label-Ty : Typing-Label ΓS L A → Typing-Path ΓS P A → path-to-term P ≈[ COT-to-Ctx ΓS ]tm first-label-term L → Typing-Label ΓS (replace-label L P) A
replace-label-Ty (TySing x) tty p = TySing tty
replace-label-Ty (TyJoin x Lty Lty′) tty p = TyJoin tty (label-typing-conv Lty (Arr≈ (sym≈tm p) refl≈ty refl≈tm)) Lty′

connect-label-Ty : (Lty : Typing-Label ΓS L A)
                 → (Mty : Typing-Label ΓS M A)
                 → last-label-term L ≈[ COT-to-Ctx ΓS ]tm first-label-term M
                 → Typing-Label ΓS (connect-label L M) A
connect-label-Ty (TySing x) Mty p = replace-label-Ty Mty x p
connect-label-Ty {M = M} (TyJoin {M = L′} x Lty Lty′) Mty p = TyJoin x (label-typing-conv Lty (reflexive≈ty (Arr≃ refl≃tm refl≃ty (sym≃tm (connect-first-label L′ M))))) (connect-label-Ty Lty′ Mty p)

connect-label-func-Ty : {L : Label-func (COT-to-MT ΓS) S}
                      → {M : Label-func (COT-to-MT ΓS) T}
                      → (Lty : Typing-Label ΓS (label-func-to-label L) A)
                      → (Mty : Typing-Label ΓS (label-func-to-label M) A)
                      → path-to-term (L (last-path S)) ≈[ COT-to-Ctx ΓS ]tm path-to-term (M PPHere)
                      → Typing-Label ΓS (label-func-to-label (connect-label-func L M)) A
connect-label-func-Ty (TySing x) (TySing y) p = TySing x
connect-label-func-Ty (TySing x) (TyJoin y Mty Mty′) p = TyJoin x {!!} {!!}
connect-label-func-Ty (TyJoin x Lty Lty₁) Mty p = {!!}

connect-tree-inc-left-Ty : (S : Tree n)
                         → (T : Tree m)
                         → Typing-Label (incTree (connect-tree S T)) (connect-tree-inc-left S T) ⋆
connect-tree-inc-left-Ty Sing T = TySing TyHere
connect-tree-inc-left-Ty (Join S₁ S₂) T
  = TyJoin TyHere
           (label-typing-conv (label-pext-Ty (id-label-Ty S₁)) (reflexive≈ty (Arr≃ (connect-inc-left-fst-var getSnd _) refl≃ty lem)))
           (label-pshift-Ty (connect-tree-inc-left-Ty S₂ T))
  where
    open Reasoning tm-setoid
    lem : getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm
          ≃tm first-label-term (map-label PShift (connect-tree-inc-left S₂ T))
    lem = begin
      < getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
        ≈⟨ connect-inc-fst-var getSnd (tree-size (connect-tree S₂ T)) ⟩
      < Var (fromℕ (tree-size (connect-tree S₂ T))) [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
        ≈˘⟨ sub-action-≃-tm (connect-tree-inc-left-first-label S₂ T) refl≃s ⟩
      < first-label-term (connect-tree-inc-left S₂ T) [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm
        >tm
        ≈˘⟨ first-label-term-pshift (connect-tree-inc-left S₂ T) ⟩
      < first-label-term (map-label PShift (connect-tree-inc-left S₂ T)) >tm ∎

connect-tree-inc-left-func-Ty : (S : Tree n)
                              → (T : Tree m)
                              → Typing-Label (incTree (connect-tree S T)) (label-func-to-label (connect-tree-inc-left-func S T)) ⋆
connect-tree-inc-left-func-Ty Sing T = TySing TyHere
connect-tree-inc-left-func-Ty (Join S₁ S₂) T
  = TyJoin TyHere
           (transport-label-typing (label-pext-Ty (id-label-Ty S₁))
                                   (trans≃l (map-label-pext-≃ (sym≃l (id-label-func-compat S₁))) (sym≃l (label-func-to-label-map PExt (id-label-func S₁))))
                                   (reflexive≈ty (Arr≃ (connect-inc-left-fst-var getSnd _) refl≃ty lem)))
           (transport-label-typing (label-pshift-Ty (connect-tree-inc-left-func-Ty S₂ T)) (sym≃l (label-func-to-label-map PShift (connect-tree-inc-left-func S₂ T))) refl≈ty)
  where
    open Reasoning tm-setoid
    lem : getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm
          ≃tm path-to-term (first-label (label-func-to-label (label-func₂ (connect-tree-inc-left-func (Join S₁ S₂) T))))
    lem = begin
      < getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
        ≈⟨ connect-inc-fst-var getSnd (tree-size (connect-tree S₂ T)) ⟩
      < Var (fromℕ (tree-size (connect-tree S₂ T))) [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
        ≈˘⟨ sub-action-≃-tm (connect-tree-inc-left-func-first-label S₂ T) refl≃s ⟩
      < path-to-term (PShift {S = S₁}(connect-tree-inc-left-func S₂ T PPHere)) >tm
        ≈˘⟨ path-to-term-≃ (first-label-func-to-label (label-func₂ (connect-tree-inc-left-func (Join S₁ S₂) T))) ⟩
      < path-to-term (first-label (label-func-to-label (label-func₂ (connect-tree-inc-left-func (Join S₁ S₂) T)))) >tm ∎

connect-tree-inc-right-func-Ty : (S : Tree n)
                               → (T : Tree m)
                               → Typing-Label (incTree (connect-tree S T)) (label-func-to-label (connect-tree-inc-right-func S T)) ⋆
connect-tree-inc-right-func-Ty Sing T = id-label-func-Ty T
connect-tree-inc-right-func-Ty (Join S₁ S₂) T = transport-label-typing (label-pshift-Ty (connect-tree-inc-right-func-Ty S₂ T)) (sym≃l (label-func-to-label-map PShift (connect-tree-inc-right-func S₂ T))) refl≈ty

connect-tree-inc-right-Ty : (S : Tree n)
                          → (T : Tree m)
                          → Typing-Label (incTree (connect-tree S T)) (connect-tree-inc-right S T) ⋆
connect-tree-inc-right-Ty Sing T = id-label-Ty T
connect-tree-inc-right-Ty (Join S₁ S₂) T = label-pshift-Ty (connect-tree-inc-right-Ty S₂ T)

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

-- label-comp-Ty : Typing-Label (incTree T) L A
--               → Typing-Label ΓS M ⋆
--               → Typing-Label ΓS (label-comp L M) (A [ label-to-sub M ⋆ ]ty)
-- label-comp-Ty (TySing x) Mty = TySing (label-index-Ty Mty TyStar x)
-- label-comp-Ty {M = M} (TyJoin {P = P} {L = L} {M = L′} x Lty Lty′) Mty
--   = TyJoin (label-index-Ty Mty TyStar x)
--            (label-typing-conv (label-comp-Ty Lty Mty) (reflexive≈ty (sym≃ty (Arr≃ (label-index-to-term M ⋆ P)
--                                                                                   refl≃ty
--                                                                                   (trans≃tm (path-to-term-≃ (first-label-comp L′ M))
--                                                                                             (label-index-to-term M ⋆ (first-label L′)))))))
--            (label-comp-Ty Lty′ Mty)

-- label-between-connect-trees-Ty : Typing-Label (incTree S′) L ⋆
--                                → Typing-Label (incTree T′) M ⋆
--                                → last-label-term L ≈[ tree-to-ctx S′ ]tm tree-last-var S′
--                                → first-label-term M ≈[ tree-to-ctx T′ ]tm Var (fromℕ (tree-size T′))
--                                → Typing-Label (incTree (connect-tree S′ T′)) (label-between-connect-trees L M) ⋆
-- label-between-connect-trees-Ty {S′ = S′} {L = L} {T′ = T′} {M = M} Lty Mty p q
--   = connect-label-Ty (label-comp-Ty Lty (connect-tree-inc-left-Ty _ _))
--                      (label-comp-Ty Mty (connect-tree-inc-right-Ty _ _))
--                      lem
--   where
--     open Reasoning (tm-setoid-≈ _)

--     lem : last-label-term (label-comp L (connect-tree-inc-left S′ T′))
--           ≈[ tree-to-ctx (connect-tree S′ T′) ]tm
--           first-label-term (label-comp M (connect-tree-inc-right S′ T′))
--     lem = begin
--       last-label-term (label-comp L (connect-tree-inc-left S′ T′))
--         ≈⟨ reflexive≈tm (path-to-term-≃ (last-label-comp L (connect-tree-inc-left S′ T′))) ⟩
--       path-to-term (connect-tree-inc-left S′ T′ ‼< ⋆ > last-label L)
--         ≈⟨ reflexive≈tm (label-index-to-term (connect-tree-inc-left S′ T′) ⋆ (last-label L)) ⟩
--       path-to-term (last-label L) [ label-to-sub (connect-tree-inc-left S′ T′) ⋆ ]tm
--         ≈⟨ apply-sub-tm-eq (label-typing-to-sub (connect-tree-inc-left-Ty S′ T′) TyStar) p ⟩
--       tree-last-var S′ [ label-to-sub (connect-tree-inc-left S′ T′) ⋆ ]tm
--         ≈˘⟨ reflexive≈tm (last-label-prop (connect-tree-inc-left S′ T′) ⋆) ⟩
--       last-label-term (connect-tree-inc-left S′ T′)
--         ≈⟨ reflexive≈tm (path-to-term-≃ (connect-tree-inc-first-label S′ T′)) ⟩
--       first-label-term (connect-tree-inc-right S′ T′)
--         ≈⟨ reflexive≈tm (first-label-prop (connect-tree-inc-right S′ T′) ⋆) ⟩
--       Var (fromℕ (tree-size T′)) [ label-to-sub (connect-tree-inc-right S′ T′) ⋆ ]tm
--         ≈˘⟨ apply-sub-tm-eq (label-typing-to-sub (connect-tree-inc-right-Ty S′ T′) TyStar) q ⟩
--       path-to-term (first-label M) [ label-to-sub (connect-tree-inc-right S′ T′) ⋆ ]tm
--         ≈˘⟨ reflexive≈tm (label-index-to-term (connect-tree-inc-right S′ T′) ⋆ (first-label M)) ⟩
--       path-to-term (connect-tree-inc-right S′ T′ ‼< ⋆ > first-label M)
--         ≈˘⟨ reflexive≈tm (path-to-term-≃ (first-label-comp M (connect-tree-inc-right S′ T′))) ⟩
--       first-label-term (label-comp M (connect-tree-inc-right S′ T′)) ∎

-- label-between-joins-Ty : Typing-Label (incTree S′) L ⋆
--                        → Typing-Label (incTree T′) M ⋆
--                        → first-label-term M ≈[ tree-to-ctx T′ ]tm Var (fromℕ (tree-size T′))
--                        → Typing-Label (incTree (Join S′ T′)) (label-between-joins L M) ⋆
-- label-between-joins-Ty Lty Mty p = label-between-connect-trees-Ty (TyJoin TyHere (label-typing-conv (label-pext-Ty Lty) (reflexive≈ty (id-on-ty (suspTy ⋆)))) (TySing (TyShift TyHere))) Mty refl≈tm p


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
