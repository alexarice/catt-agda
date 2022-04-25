module Catt.Tree.Label.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Tree
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Label
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Syntax.Bundles
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties

data _≃l_ : {S : Tree n} → Label m S → Label l S → Set where
  LSing≃ : s ≃tm t → LSing s ≃l LSing t
  LJoin≃ : ∀ {L L′ : Label m S} {M M′ : Label m T} → s ≃tm t → L ≃l L′ → M ≃l M′ → LJoin s L M ≃l LJoin t L′ M′

refl≃l : L ≃l L
refl≃l {L = LSing x} = LSing≃ refl≃tm
refl≃l {L = LJoin x L M} = LJoin≃ refl≃tm refl≃l refl≃l

sym≃l : L ≃l M → M ≃l L
sym≃l (LSing≃ x) = LSing≃ (sym≃tm x)
sym≃l (LJoin≃ x p q) = LJoin≃ (sym≃tm x) (sym≃l p) (sym≃l q)

trans≃l : L ≃l L′ → L′ ≃l M → L ≃l M
trans≃l (LSing≃ x) (LSing≃ y) = LSing≃ (trans≃tm x y)
trans≃l (LJoin≃ x p q) (LJoin≃ y r s) = LJoin≃ (trans≃tm x y) (trans≃l p r) (trans≃l q s)

first-label-≃ : L ≃l M → first-label L ≃tm first-label M
first-label-≃ (LSing≃ x) = x
first-label-≃ (LJoin≃ x p q) = x

label-to-sub-≃ : L ≃l M → A ≃ty B → label-to-sub L A ≃s label-to-sub M B
label-to-sub-≃ (LSing≃ x) q = Ext≃ (Null≃ q) x
label-to-sub-≃ (LJoin≃ x p r) q = sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ p (Arr≃ x q (first-label-≃ r)))) (label-to-sub-≃ r q)

Same-Leaves : (L M : Label m S) → Set
Same-Leaves {S = S} L M = ∀ (P : Path S) → .⦃ is-Maximal P ⦄ → L ‼l P ≃tm M ‼l P

Same-Leaves-proj₁ : Same-Leaves (LJoin s L M) (LJoin t L′ M′) → Same-Leaves L L′
Same-Leaves-proj₁ f P = f (PExt P)

Same-Leaves-proj₂ : Same-Leaves (LJoin s L M) (LJoin t L′ M′) → .⦃ is-join (label-to-tree M) ⦄ → Same-Leaves M M′
Same-Leaves-proj₂ f P = f (PShift P) ⦃ maximal-join-not-here P ,, it ⦄

first-label-comp : (M : Label n S) → (σ : Sub n m A) → first-label (M [ σ ]l) ≃tm first-label M [ σ ]tm
first-label-comp (LSing x) σ = refl≃tm
first-label-comp (LJoin x L M) σ = refl≃tm

label-comp-to-sub-comp : (L : Label m S)
                       → (σ : Sub m n B)
                       → (A : Ty m)
                       → label-to-sub (L [ σ ]l) (A [ σ ]ty) ≃s σ ∘ label-to-sub L A
label-comp-to-sub-comp (LSing x) σ A = refl≃s
label-comp-to-sub-comp (LJoin x L M) σ A = begin
  < sub-from-connect
      (unrestrict
       (label-to-sub (L [ σ ]l)
        ((x [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ first-label (M [ σ ]l))))
      (label-to-sub (M [ σ ]l) (A [ σ ]ty)) >s
    ≈⟨ sub-from-connect-≃ l1 (label-comp-to-sub-comp M σ A) ⟩
  < sub-from-connect
    (σ ∘ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)))
    (σ ∘ label-to-sub M A)
    >s
    ≈˘⟨ sub-from-connect-sub (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A) σ ⟩
  < σ ∘ sub-from-connect
       (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)))
       (label-to-sub M A) >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict
       (label-to-sub (L [ σ ]l)
        ((x [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ first-label (M [ σ ]l))) ≃s (σ ∘ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)))
    l1 = begin
      < unrestrict (label-to-sub (L [ σ ]l) ((x [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ first-label (M [ σ ]l))) >s
        ≈⟨ unrestrict-≃ (label-to-sub-≃ {L = L [ σ ]l} refl≃l (Arr≃ refl≃tm refl≃ty (first-label-comp M σ))) ⟩
      < unrestrict (label-to-sub (L [ σ ]l) ((x ─⟨ A ⟩⟶ first-label M) [ σ ]ty)) >s
        ≈⟨ unrestrict-≃ (label-comp-to-sub-comp L σ (x ─⟨ A ⟩⟶ first-label M)) ⟩
      < unrestrict (σ ∘ label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) >s
        ≈⟨ unrestrict-comp-higher σ (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ⟩
      < σ ∘ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) >s ∎

first-label-susp : (L : Label n S) → first-label (suspLabel L) ≃tm suspTm (first-label L)
first-label-susp (LSing x) = refl≃tm
first-label-susp (LJoin x L M) = refl≃tm

label-to-sub-susp : (L : Label n S) → (A : Ty n) → label-to-sub (suspLabel L) (suspTy A) ≃s suspSubRes (label-to-sub L A)
label-to-sub-susp (LSing x) A = refl≃s
label-to-sub-susp (LJoin x L M) A = begin
  < sub-from-connect
      (unrestrict (label-to-sub (suspLabel L) (suspTm x ─⟨ suspTy A ⟩⟶ first-label (suspLabel M))))
      (label-to-sub (suspLabel M) (suspTy A)) >s
    ≈⟨ sub-from-connect-≃ l1 (label-to-sub-susp M A) ⟩
  < sub-from-connect
    (suspSubRes (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))))
    (suspSubRes (label-to-sub M A)) >s
    ≈˘⟨ sub-from-connect-susp-res (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A) ⟩
  < suspSubRes
      (sub-from-connect
       (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)))
       (label-to-sub M A)) >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict
           (label-to-sub (suspLabel L)
            (suspTm x ─⟨ suspTy A ⟩⟶ first-label (suspLabel M)))
           ≃s
           suspSubRes (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)))
    l1 = begin
      < unrestrict (label-to-sub (suspLabel L) (suspTm x ─⟨ suspTy A ⟩⟶ first-label (suspLabel M))) >s
        ≈⟨ unrestrict-≃ (label-to-sub-≃ (refl≃l {L = suspLabel L}) (Arr≃ refl≃tm refl≃ty (first-label-susp M))) ⟩
      < unrestrict (label-to-sub (suspLabel L) (suspTm x ─⟨ suspTy A ⟩⟶ suspTm (first-label M))) >s
        ≈⟨ unrestrict-≃ (label-to-sub-susp L (x ─⟨ A ⟩⟶ first-label M)) ⟩
      < unrestrict (suspSubRes (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) >s
        ≈˘⟨ sub-res-unrestrict-comm (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ⟩
      < suspSubRes (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) >s ∎

id-first-label : (T : Tree n) → first-label (id-label T) ≃tm Var (fromℕ n)
id-first-label Sing = refl≃tm
id-first-label (Join S T) = refl≃tm

id-label-is-id-sub : (S : Tree n) → label-to-sub (id-label S) ⋆ ≃s idSub {suc n}
id-label-is-id-sub Sing = refl≃s
id-label-is-id-sub (Join S T) = begin
  < sub-from-connect
      (unrestrict
       (label-to-sub
        (suspLabel (id-label S) [ connect-susp-inc-left _ _ ]l)
        (Var (fromℕ _) ─⟨ ⋆ ⟩⟶
         first-label (id-label T [ connect-susp-inc-right _ _ ]l))))
      (label-to-sub (id-label T [ connect-susp-inc-right _ _ ]l) ⋆) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (connect-susp-inc-left _ _) (connect-susp-inc-right _ _) >s
    ≈⟨ sub-from-connect-prop getSnd ⟩
  < idSub >s ∎
  where


    l3 : first-label (id-label T [ connect-susp-inc-right _ _ ]l) ≃tm
           (getSnd [ connect-susp-inc-left _ _ ]tm)
    l3 = begin
      < first-label (id-label T [ connect-susp-inc-right _ _ ]l) >tm
        ≈⟨ first-label-comp (id-label T) (connect-susp-inc-right _ _) ⟩
      < first-label (id-label T) [ connect-susp-inc-right _ _ ]tm >tm
        ≈⟨ sub-action-≃-tm (id-first-label T) refl≃s ⟩
      < Var (fromℕ _) [ connect-susp-inc-right _ _ ]tm >tm
        ≈˘⟨ connect-inc-fst-var getSnd _ ⟩
      < getSnd [ connect-susp-inc-left _ _ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (suspLabel (id-label S) [ connect-susp-inc-left _ _ ]l) (_ ─⟨ ⋆ ⟩⟶ _)) ≃s connect-susp-inc-left _ _
    l1 = begin
      < unrestrict (label-to-sub
         (suspLabel (id-label S) [ connect-susp-inc-left _ _ ]l)
         (Var (fromℕ _) ─⟨ ⋆ ⟩⟶
          first-label (id-label T [ connect-susp-inc-right _ _ ]l))) >s
        ≈⟨ unrestrict-≃ (label-to-sub-≃ (refl≃l {L = suspLabel (id-label S) [ connect-susp-inc-left _ _ ]l}) (Arr≃ (sym≃tm (connect-inc-left-fst-var getSnd _)) refl≃ty l3)) ⟩
      < (unrestrict (label-to-sub (suspLabel (id-label S) [ connect-susp-inc-left _ _ ]l) ((getFst ─⟨ ⋆ ⟩⟶ getSnd) [ connect-susp-inc-left _ _ ]ty))) >s
        ≈⟨ unrestrict-≃ (label-comp-to-sub-comp (suspLabel (id-label S)) (connect-susp-inc-left _ _) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) ⟩
      < unrestrict (connect-susp-inc-left _ _
                   ∘ label-to-sub (suspLabel (id-label S)) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) >s
        ≈⟨ unrestrict-≃ (sub-action-≃-sub (label-to-sub-susp (id-label S) ⋆) refl≃s) ⟩
      < unrestrict (connect-susp-inc-left _ _ ∘ suspSubRes (label-to-sub (id-label S) ⋆)) >s
        ≈⟨ unrestrict-comp-higher (connect-susp-inc-left _ _) (suspSubRes (label-to-sub (id-label S) ⋆)) ⟩
      < connect-susp-inc-left _ _ ∘ suspSub (label-to-sub (id-label S) ⋆) >s
        ≈⟨ sub-action-≃-sub (susp-sub-≃ (id-label-is-id-sub S)) refl≃s ⟩
      < connect-susp-inc-left _ _ ∘ suspSub idSub >s
        ≈⟨ sub-action-≃-sub susp-functorial-id refl≃s ⟩
      < connect-susp-inc-left _ _ ∘ idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-left _ _) ⟩
      < connect-susp-inc-left _ _ >s ∎

    l2 : label-to-sub (id-label T [ connect-susp-inc-right _ _ ]l) ⋆ ≃s connect-susp-inc-right _ _
    l2 = begin
      < label-to-sub (id-label T [ connect-susp-inc-right _ _ ]l) ⋆ >s
        ≈⟨ label-comp-to-sub-comp (id-label T) (connect-susp-inc-right _ _) ⋆ ⟩
      < connect-susp-inc-right _ _ ∘ label-to-sub (id-label T) ⋆ >s
        ≈⟨ sub-action-≃-sub (id-label-is-id-sub T) refl≃s ⟩
      < connect-susp-inc-right _ _ ∘ idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-right _ _) ⟩
      < connect-susp-inc-right _ _ >s ∎

sub-to-label-to-sub : (S : Tree n) → (σ : Sub (suc n) m A) → label-to-sub (to-label S σ) A ≃s σ
sub-to-label-to-sub {A = A} S σ = begin
  < label-to-sub (id-label S [ σ ]l) A >s
    ≈⟨ label-comp-to-sub-comp (id-label S) σ ⋆ ⟩
  < σ ∘ label-to-sub (id-label S) ⋆  >s
    ≈⟨ sub-action-≃-sub (id-label-is-id-sub S) refl≃s ⟩
  < σ ∘ idSub >s
    ≈⟨ id-right-unit σ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid

first-label-prop : (L : Label m S) → (A : Ty m) → first-label L ≃tm Var (fromℕ _) [ label-to-sub L A ]tm
first-label-prop (LSing x) A = refl≃tm
first-label-prop (LJoin x L M) A = begin
  < x >tm
    ≈˘⟨ unrestrict-fst (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ⟩
  < Var (fromℕ _)
    [ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ]tm >tm
    ≈˘⟨ sub-from-connect-fst-var (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A) ⟩
  < Var (fromℕ _) [ sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A) ]tm >tm ∎
  where
    open Reasoning tm-setoid

‼l-prop : (L : Label m S) → (P : Path S) → (A : Ty m) → L ‼l P ≃tm path-to-var P [ label-to-sub L A ]tm
‼l-prop L PHere A = first-label-prop L A
‼l-prop (LJoin x L M) (PExt P) A = begin
  < L ‼l P >tm
    ≈⟨ ‼l-prop L P (x ─⟨ A ⟩⟶ first-label M) ⟩
  < path-to-var P [ label-to-sub L (x ─⟨ A ⟩⟶ first-label M) ]tm >tm
    ≈˘⟨ unrestrict-comp-tm (path-to-var P) (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ⟩
  < suspTm (path-to-var P) [ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = suspTm (path-to-var P)}) (sub-from-connect-inc-left (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) getSnd (label-to-sub M A)) ⟩
  < suspTm (path-to-var P)
    [ sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A)
      ∘ connect-susp-inc-left _ _ ]tm >tm
    ≈⟨ assoc-tm _ _ (suspTm (path-to-var P)) ⟩
  < suspTm (path-to-var P)
    [ connect-susp-inc-left _ _ ]tm
    [ sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A) ]tm >tm ∎
  where
    open Reasoning tm-setoid
‼l-prop (LJoin x L M) (PShift P) A = begin
  < M ‼l P >tm
    ≈⟨ ‼l-prop M P A ⟩
  < path-to-var P [ label-to-sub M A ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = path-to-var P}) (sub-from-connect-inc-right (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) getSnd (label-to-sub M A) lem) ⟩
  < path-to-var P
    [ sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A)
      ∘ connect-susp-inc-right _ _ ]tm >tm
    ≈⟨ assoc-tm _ _ (path-to-var P) ⟩
  < path-to-var P
    [ connect-susp-inc-right _ _ ]tm
    [ sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A) ]tm >tm ∎
  where
    open Reasoning tm-setoid

    lem : getSnd [ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ]tm
          ≃tm Var (fromℕ _) [ label-to-sub M A ]tm
    lem = begin
      < getSnd [ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ]tm >tm
        ≈⟨ unrestrict-snd (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ⟩
      < first-label M >tm
        ≈⟨ first-label-prop M A ⟩
      < Var (fromℕ _) [ label-to-sub M A ]tm >tm ∎

‼l-prop-2 : (σ : Sub (suc (tree-size S)) m A) → (P : Path S) → to-label S σ ‼l P ≃tm path-to-var P [ σ ]tm
‼l-prop-2 {S = S} σ P = trans≃tm (‼l-prop (to-label S σ) P (sub-type σ)) (sub-action-≃-tm (refl≃tm {s = path-to-var P}) (sub-to-label-to-sub S σ))
