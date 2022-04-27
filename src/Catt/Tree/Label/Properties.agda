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
  LJoin≃ : ∀ {L : Label m S} {L′ : Label m′ S} {M : Label m T} {M′ : Label m′ T} → s ≃tm t → L ≃l L′ → M ≃l M′ → LJoin s L M ≃l LJoin t L′ M′

refl≃l : L ≃l L
refl≃l {L = LSing x} = LSing≃ refl≃tm
refl≃l {L = LJoin x L M} = LJoin≃ refl≃tm refl≃l refl≃l

sym≃l : L ≃l M → M ≃l L
sym≃l (LSing≃ x) = LSing≃ (sym≃tm x)
sym≃l (LJoin≃ x p q) = LJoin≃ (sym≃tm x) (sym≃l p) (sym≃l q)

trans≃l : L ≃l L′ → L′ ≃l M → L ≃l M
trans≃l (LSing≃ x) (LSing≃ y) = LSing≃ (trans≃tm x y)
trans≃l (LJoin≃ x p q) (LJoin≃ y r s) = LJoin≃ (trans≃tm x y) (trans≃l p r) (trans≃l q s)

record LABEL (S : Tree n) : Set where
  constructor <_>l
  field
    {label-n} : ℕ
    label : Label label-n S

open LABEL public

label-setoid : (S : Tree n) → Setoid _ _
label-setoid S = record { Carrier = LABEL S
                        ; _≈_ = λ x y → label x ≃l label y
                        ; isEquivalence = record { refl = refl≃l
                                                 ; sym = sym≃l
                                                 ; trans = trans≃l
                                                 }
                        }

first-label-≃ : L ≃l M → first-label L ≃tm first-label M
first-label-≃ (LSing≃ x) = x
first-label-≃ (LJoin≃ x p q) = x

last-label-≃ : L ≃l M → last-label L ≃tm last-label M
last-label-≃ (LSing≃ x) = x
last-label-≃ (LJoin≃ x p q) = last-label-≃ q

label-to-sub-≃ : L ≃l M → A ≃ty B → label-to-sub L A ≃s label-to-sub M B
label-to-sub-≃ (LSing≃ x) q = Ext≃ (Null≃ q) x
label-to-sub-≃ (LJoin≃ x p r) q = sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ p (Arr≃ x q (first-label-≃ r)))) (label-to-sub-≃ r q)

sub-action-≃-label : L ≃l M → σ ≃s τ → L [ σ ]l ≃l M [ τ ]l
sub-action-≃-label (LSing≃ x) q = LSing≃ (sub-action-≃-tm x q)
sub-action-≃-label (LJoin≃ x p p′) q = LJoin≃ (sub-action-≃-tm x q) (sub-action-≃-label p q) (sub-action-≃-label p′ q)

replace-label-≃ : L ≃l M → s ≃tm t → replace-label L s ≃l replace-label M t
replace-label-≃ (LSing≃ x) q = LSing≃ q
replace-label-≃ (LJoin≃ x p p′) q = LJoin≃ q p p′

connect-label-≃ : L ≃l L′ → M ≃l M′ → connect-label L M ≃l connect-label L′ M′
connect-label-≃ (LSing≃ x) q = replace-label-≃ q x
connect-label-≃ (LJoin≃ x p p′) q = LJoin≃ x p (connect-label-≃ p′ q)

id-on-label : (L : Label m S) → L [ idSub ]l ≃l L
id-on-label (LSing x) = LSing≃ (id-on-tm x)
id-on-label (LJoin x L M) = LJoin≃ (id-on-tm x) (id-on-label L) (id-on-label M)

susp-functorial-label : (σ : Sub m n ⋆) → (L : Label m S) → suspLabel (L [ σ ]l) ≃l suspLabel L [ suspSub σ ]l
susp-functorial-label σ (LSing x) = LSing≃ (susp-functorial-tm σ x)
susp-functorial-label σ (LJoin x L M) = LJoin≃ (susp-functorial-tm σ x) (susp-functorial-label σ L) (susp-functorial-label σ M)

Same-Leaves : (L M : Label m S) → Set
Same-Leaves {S = S} L M = ∀ (P : Path S) → .⦃ is-Maximal P ⦄ → L ‼l P ≃tm M ‼l P

Same-Leaves-proj₁ : Same-Leaves (LJoin s L M) (LJoin t L′ M′) → Same-Leaves L L′
Same-Leaves-proj₁ f P = f (PExt P)

Same-Leaves-proj₂ : Same-Leaves (LJoin s L M) (LJoin t L′ M′) → .⦃ is-join (label-to-tree M) ⦄ → Same-Leaves M M′
Same-Leaves-proj₂ f P = f (PShift P) ⦃ maximal-join-not-here P ,, it ⦄

first-label-comp : (M : Label n S) → (σ : Sub n m A) → first-label (M [ σ ]l) ≃tm first-label M [ σ ]tm
first-label-comp (LSing x) σ = refl≃tm
first-label-comp (LJoin x L M) σ = refl≃tm

last-label-comp : (M : Label n S) → (σ : Sub n m A) → last-label (M [ σ ]l) ≃tm last-label M [ σ ]tm
last-label-comp (LSing x) σ = refl≃tm
last-label-comp (LJoin x L M) σ = last-label-comp M σ

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

replace-label-comp : (L : Label m S) → (t : Tm m) → (σ : Sub m n A) → replace-label (L [ σ ]l) (t [ σ ]tm) ≃l replace-label L t [ σ ]l
replace-label-comp (LSing x) t σ = refl≃l
replace-label-comp (LJoin x L M) t σ = refl≃l

connect-label-comp : (L : Label m S) → (M : Label m T) → (σ : Sub m n A) → connect-label (L [ σ ]l) (M [ σ ]l) ≃l connect-label L M [ σ ]l
connect-label-comp (LSing x) M σ = replace-label-comp M x σ
connect-label-comp (LJoin x L L′) M σ = LJoin≃ refl≃tm refl≃l (connect-label-comp L′ M σ)

assoc-label : (τ : Sub n l B) → (σ : Sub m n A) → (L : Label m S) → L [ τ ∘ σ ]l ≃l L [ σ ]l [ τ ]l
assoc-label τ σ (LSing x) = LSing≃ (assoc-tm τ σ x)
assoc-label τ σ (LJoin x L M) = LJoin≃ (assoc-tm τ σ x) (assoc-label τ σ L) (assoc-label τ σ M)

to-label-comp : (S : Tree n) → (σ : Sub (suc n) m A) → (μ : Sub m l B) → to-label S (μ ∘ σ) ≃l to-label S σ [ μ ]l
to-label-comp S σ μ = assoc-label μ σ (id-label S)

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

susp-replace-label : (L : Label m S) → (t : Tm m) → suspLabel (replace-label L t) ≃l replace-label (suspLabel L) (suspTm t)
susp-replace-label (LSing x) t = refl≃l
susp-replace-label (LJoin x L M) t = refl≃l

susp-connect-label : (L : Label m S) → (M : Label m T) → suspLabel (connect-label L M) ≃l connect-label (suspLabel L) (suspLabel M)
susp-connect-label (LSing x) M = susp-replace-label M x
susp-connect-label (LJoin x L L′) M = LJoin≃ refl≃tm refl≃l (susp-connect-label L′ M)

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

last-label-prop : (L : Label m S) → (A : Ty m) → last-label L ≃tm tree-last-var S [ label-to-sub L A ]tm
last-label-prop (LSing x) A = refl≃tm
last-label-prop (LJoin {S = S} {T = T} x L M) A = begin
  < last-label M >tm
    ≈⟨ last-label-prop M A ⟩
  < tree-last-var T [ label-to-sub M A ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var T}) (sub-from-connect-inc-right (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) getSnd (label-to-sub M A) lem) ⟩
  < tree-last-var T
    [ sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A)
      ∘ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var T) ⟩
  < tree-last-var T
    [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm
    [ sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A) ]tm >tm ∎
  where
    open Reasoning tm-setoid

    lem : (getSnd [ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))
             ]tm)
            ≃tm (Var (fromℕ _) [ label-to-sub M A ]tm)
    lem = begin
      < getSnd [ unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ]tm >tm
        ≈⟨ unrestrict-snd (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ⟩
      < first-label M >tm
        ≈⟨ first-label-prop M A ⟩
      < Var (fromℕ _) [ label-to-sub M A ]tm >tm ∎

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

‼l-comp : (L : Label m S) → (P : Path S) → (σ : Sub m n A) → (L [ σ ]l) ‼l P ≃tm L ‼l P [ σ ]tm
‼l-comp (LSing x) PHere σ = refl≃tm
‼l-comp (LJoin x L M) PHere σ = refl≃tm
‼l-comp (LJoin x L M) (PExt P) σ = ‼l-comp L P σ
‼l-comp (LJoin x L M) (PShift P) σ = ‼l-comp M P σ

replace-first-label : (L : Label m S) → (t : Tm m) → first-label (replace-label L t) ≃tm t
replace-first-label (LSing x) t = refl≃tm
replace-first-label (LJoin x L M) t = refl≃tm

connect-first-label : (L : Label m S) → (M : Label m T) → first-label (connect-label L M) ≃tm first-label L
connect-first-label (LSing x) M = replace-first-label M x
connect-first-label (LJoin x L₁ L₂) M = refl≃tm

label-join-lem : (t : Tm m) → (L : Label m S) → (M : Label m T) → (A : Ty m)
               → getSnd [ unrestrict (label-to-sub L (t ─⟨ A ⟩⟶ first-label M)) ]tm ≃tm Var (fromℕ _) [ label-to-sub M A ]tm
label-join-lem t L M A = begin
 < getSnd [ unrestrict (label-to-sub L (t ─⟨ A ⟩⟶ first-label M)) ]tm >tm
   ≈⟨ unrestrict-snd (label-to-sub L (t ─⟨ A ⟩⟶ first-label M)) ⟩
 < first-label M >tm
   ≈⟨ first-label-prop M A ⟩
 < Var (fromℕ _) [ label-to-sub M A ]tm >tm ∎
   where
     open Reasoning tm-setoid

lift-replace-label : (L : Label m S) → (t : Tm m) → liftLabel (replace-label L t) ≃l replace-label (liftLabel L) (liftTerm t)
lift-replace-label (LSing x) t = refl≃l
lift-replace-label (LJoin x L M) t = refl≃l

lift-connect-label : (L : Label m S) → (M : Label m T) → liftLabel (connect-label L M) ≃l connect-label (liftLabel L) (liftLabel M)
lift-connect-label (LSing x) M = lift-replace-label M x
lift-connect-label (LJoin x L L′) M = LJoin≃ refl≃tm refl≃l (lift-connect-label L′ M)

lift-first-label : (L : Label m S) → first-label (liftLabel L) ≃tm liftTerm (first-label L)
lift-first-label (LSing x) = refl≃tm
lift-first-label (LJoin x L M) = refl≃tm

lift-label-to-sub : (L : Label m S) → (A : Ty m) → label-to-sub (liftLabel L) (liftType A) ≃s liftSub (label-to-sub L A)
lift-label-to-sub (LSing x) A = refl≃s
lift-label-to-sub (LJoin x L M) A = begin
  < sub-from-connect (unrestrict (label-to-sub (liftLabel L) (liftTerm x ─⟨ liftType A ⟩⟶ first-label (liftLabel M))))
                     (label-to-sub (liftLabel M) (liftType A)) >s
    ≈⟨ sub-from-connect-≃ lem (lift-label-to-sub M A) ⟩
  < sub-from-connect (liftSub (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)))) (liftSub (label-to-sub M A)) >s
    ≈˘⟨ sub-from-connect-lift (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A) ⟩
  < liftSub (sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)))
                              (label-to-sub M A)) >s ∎
  where
    open Reasoning sub-setoid

    lem : unrestrict
            (label-to-sub (liftLabel L)
             (liftTerm x ─⟨ liftType A ⟩⟶ first-label (liftLabel M)))
            ≃s liftSub (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)))
    lem = begin
      < unrestrict (label-to-sub (liftLabel L) (liftTerm x ─⟨ liftType A ⟩⟶ first-label (liftLabel M))) >s
        ≈⟨ unrestrict-≃ (label-to-sub-≃ (refl≃l {L = liftLabel L}) (Arr≃ refl≃tm refl≃ty (lift-first-label M))) ⟩
      < unrestrict (label-to-sub (liftLabel L) (liftType (x ─⟨ A ⟩⟶ first-label M))) >s
        ≈⟨ unrestrict-≃ (lift-label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ⟩
      < unrestrict (liftSub (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) >s
        ≈⟨ unrestrict-lift (label-to-sub L (x ─⟨ A ⟩⟶ first-label M)) ⟩
      < liftSub (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) >s ∎

apply-lifted-sub-label-≃ : (L : Label m S) → (σ : Sub m n A) → L [ liftSub σ ]l ≃l liftLabel (L [ σ ]l)
apply-lifted-sub-label-≃ (LSing x) σ = LSing≃ (apply-lifted-sub-tm-≃ x σ)
apply-lifted-sub-label-≃ (LJoin x L M) σ = LJoin≃ (apply-lifted-sub-tm-≃ x σ) (apply-lifted-sub-label-≃ L σ) (apply-lifted-sub-label-≃ M σ)

lift-to-label : (S : Tree n) → (σ : Sub (suc n) m A) → liftLabel (to-label S σ) ≃l to-label S (liftSub σ)
lift-to-label S σ = sym≃l (apply-lifted-sub-label-≃ (id-label S) σ)

susp-to-label : (S : Tree n) → (σ : Sub (suc n) m ⋆) → to-label (suspTree S) (suspSub σ) ≃l LJoin getFst (suspLabel (to-label S σ)) (LSing getSnd)
susp-to-label S σ = LJoin≃ (sym≃tm (susp-sub-preserve-getFst σ)) lem (LSing≃ (sym≃tm (susp-sub-preserve-getSnd σ)))
  where
    open Reasoning (label-setoid _)

    lem : suspLabel (id-label S) [ connect-susp-inc-left _ 0 ]l
                                 [ suspSub σ ]l
          ≃l suspLabel (to-label S σ)
    lem = begin
      < suspLabel (id-label S) [ connect-susp-inc-left _ 0 ]l
                               [ suspSub σ ]l >l
        ≈⟨ sub-action-≃-label (id-on-label (suspLabel (id-label S))) refl≃s ⟩
      < suspLabel (id-label S) [ suspSub σ ]l >l
        ≈˘⟨ susp-functorial-label σ (id-label S) ⟩
      < suspLabel (id-label S [ σ ]l) >l ∎



connect-tree-inc-left-first-label : (S : Tree n)
                                  → (T : Tree m)
                                  → first-label (connect-tree-inc-left S T) ≃tm Var (fromℕ (connect-tree-length S T))
connect-tree-inc-left-first-label Sing T = refl≃tm
connect-tree-inc-left-first-label (Join S₁ S₂) T = connect-inc-left-fst-var getSnd (connect-tree-length S₂ T)

replace-label-prop : (L : Label m S) → (t : Tm m) → t ≃tm first-label L → replace-label L t ≃l L
replace-label-prop (LSing x) t p = LSing≃ p
replace-label-prop (LJoin x L M) t p = LJoin≃ p refl≃l refl≃l

connect-tree-inc-first-label : (S : Tree n)
                             → (T : Tree m)
                             → last-label (connect-tree-inc-left S T) ≃tm first-label (connect-tree-inc-right S T)
connect-tree-inc-first-label Sing T = sym≃tm (id-first-label T)
connect-tree-inc-first-label (Join S₁ S₂) T = begin
  < last-label (replace-label (connect-tree-inc-left S₂ T [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]l)
                              (getSnd [ connect-susp-inc-left _ (connect-tree-length S₂ T) ]tm)) >tm
    ≈⟨ last-label-≃ (replace-label-prop (connect-tree-inc-left S₂ T [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]l) (getSnd [ connect-susp-inc-left _ (connect-tree-length S₂ T) ]tm) lem) ⟩
  < last-label (connect-tree-inc-left S₂ T [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]l) >tm
    ≈⟨ last-label-comp (connect-tree-inc-left S₂ T) (connect-susp-inc-right _ (connect-tree-length S₂ T)) ⟩
  < last-label (connect-tree-inc-left S₂ T) [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]tm >tm
    ≈⟨ sub-action-≃-tm (connect-tree-inc-first-label S₂ T) refl≃s ⟩
  < first-label (connect-tree-inc-right S₂ T) [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]tm >tm
    ≈˘⟨ first-label-comp (connect-tree-inc-right S₂ T) (connect-susp-inc-right _ (connect-tree-length S₂ T)) ⟩
  < first-label (connect-tree-inc-right S₂ T [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]l) >tm ∎
  where
    open Reasoning tm-setoid
    lem : (getSnd [ connect-susp-inc-left _ (connect-tree-length S₂ T) ]tm)
            ≃tm
            first-label
            (connect-tree-inc-left S₂ T [
             connect-susp-inc-right _ (connect-tree-length S₂ T) ]l)
    lem = begin
      < getSnd [ connect-susp-inc-left _ (connect-tree-length S₂ T) ]tm >tm
        ≈⟨ connect-inc-fst-var getSnd (connect-tree-length S₂ T) ⟩
      < Var (fromℕ (connect-tree-length S₂ T)) [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]tm >tm
        ≈˘⟨ sub-action-≃-tm (connect-tree-inc-left-first-label S₂ T) refl≃s ⟩
      < first-label (connect-tree-inc-left S₂ T) [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]tm >tm
        ≈˘⟨ first-label-comp (connect-tree-inc-left S₂ T) (connect-susp-inc-right _ (connect-tree-length S₂ T)) ⟩
      < first-label (connect-tree-inc-left S₂ T [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]l) >tm ∎

last-path-‼ : (L : Label m S) → L ‼l last-path S ≃tm last-label L
last-path-‼ (LSing x) = refl≃tm
last-path-‼ (LJoin x L M) = last-path-‼ M

label-between-connect-trees-first-label : (L : Label (suc m) S)
                                        → (M : Label (suc n) T)
                                        → (S′ : Tree m)
                                        → (T′ : Tree n)
                                        → first-label (label-between-connect-trees L M S′ T′) ≃tm first-label L [ label-to-sub (connect-tree-inc-left S′ T′) ⋆ ]tm
label-between-connect-trees-first-label L M S′ T′ = begin
  < first-label (label-between-connect-trees L M S′ T′) >tm
    ≈⟨ connect-first-label (L [ label-to-sub (connect-tree-inc-left S′ T′) ⋆ ]l) (M [ label-to-sub (connect-tree-inc-right S′ T′) ⋆ ]l) ⟩
  < first-label (L [ label-to-sub (connect-tree-inc-left S′ T′) ⋆ ]l) >tm
    ≈⟨ first-label-comp L (label-to-sub (connect-tree-inc-left S′ T′) ⋆) ⟩
  < first-label L [ label-to-sub (connect-tree-inc-left S′ T′) ⋆ ]tm >tm ∎
  where
    open Reasoning tm-setoid

label-between-joins-first-label : (L : Label (suc m) S)
                                → (M : Label (suc n) T)
                                → (S′ : Tree m)
                                → (T′ : Tree n)
                                → first-label (label-between-joins L M S′ T′) ≃tm Var (fromℕ (n + (2 + m)))
label-between-joins-first-label L M S′ T′ = begin
  < first-label (label-between-joins L M S′ T′) >tm
    ≈⟨ label-between-connect-trees-first-label (LJoin getFst (suspLabel L) (LSing getSnd)) M (suspTree S′) T′ ⟩
  < getFst [ label-to-sub (connect-tree-inc-left (suspTree S′) T′) ⋆ ]tm >tm
    ≈˘⟨ ‼l-prop (connect-tree-inc-left (suspTree S′) T′) PHere ⋆ ⟩
  < first-label (connect-tree-inc-left (suspTree S′) T′) >tm
    ≈⟨ connect-tree-inc-left-first-label (suspTree S′) T′ ⟩
  < Var (fromℕ (connect-tree-length (suspTree S′) T′)) >tm ∎
  where
    open Reasoning tm-setoid
