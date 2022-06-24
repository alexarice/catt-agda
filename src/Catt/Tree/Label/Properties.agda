module Catt.Tree.Label.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Tree
open import Catt.Tree.Properties
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


module _ where
  open Reasoning tm-setoid

  extend-ppath : (P : PPath S) → (L : Label X S A) → (carrier P >>= L) ≃p ap L P
  extend-ppath ⟦ PHere ⟧ L = refl≃p
  extend-ppath ⟦ PExt P ⟧ L = extend-ppath ⟦ P ⟧ (label₁ L)
  extend-ppath ⟦ PShift P ⟧ L = extend-ppath ⟦ P ⟧ (label₂ L)

  label-to-sub-path : (L : Label X S A) → (P : Path (someTree S)) → path-to-term P [ label-to-sub L ]tm ≃tm path-to-term (P >>= L)
  label-to-sub-lem : (L : Label X (Join S T) A) → getSnd [ unrestrict (label-to-sub (label₁ L)) ]tm ≃tm Var (fromℕ m) [ label-to-sub (label₂ L) ]tm

  label-to-sub-path {S = Sing} L PHere = refl≃tm
  label-to-sub-path {S = Sing} L (POther t) = refl≃tm
  label-to-sub-path {S = Join S T} L PHere = begin
    < Var (fromℕ _) [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]tm >tm
      ≈⟨ sub-from-connect-fst-var (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
    < getFst [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
      ≈⟨ unrestrict-fst (label-to-sub (label₁ L)) ⟩
    < apt L PPHere >tm ∎
  label-to-sub-path {S = Join S T} L (PExt P) = begin
    < suspTm (path-to-term P) [ connect-susp-inc-left _ _ ]tm
                              [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                                 (label-to-sub (label₂ L)) ]tm >tm
      ≈˘⟨ assoc-tm _ _ (suspTm (path-to-term P)) ⟩
    < suspTm (path-to-term P) [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                                 (label-to-sub (label₂ L))
                              ∘ connect-susp-inc-left _ _ ]tm >tm
      ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (path-to-term P)}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L))) ⟩
    < suspTm (path-to-term P) [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
      ≈⟨ unrestrict-comp-tm (path-to-term P) (label-to-sub (label₁ L)) ⟩
    < path-to-term P [ label-to-sub (label₁ L) ]tm >tm
      ≈⟨ label-to-sub-path (label₁ L) P ⟩
    < path-to-term (P >>= label₁ L) >tm ∎
  label-to-sub-path {S = Join S T} L (PShift P) = begin
    < path-to-term P [ connect-susp-inc-right _ _ ]tm
                     [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                        (label-to-sub (label₂ L)) ]tm >tm
      ≈˘⟨ assoc-tm _ _ (path-to-term P) ⟩
    < path-to-term P [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                        (label-to-sub (label₂ L))
                     ∘ connect-susp-inc-right _ _ ]tm >tm
      ≈⟨ sub-action-≃-tm (refl≃tm {s = path-to-term P}) (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L)) (label-to-sub-lem L)) ⟩
    < path-to-term P [ label-to-sub (label₂ L) ]tm >tm
      ≈⟨ label-to-sub-path (label₂ L) P ⟩
    < path-to-term (P >>= label₂ L) >tm ∎
  label-to-sub-path {S = Join S T} L (POther t) = refl≃tm

  label-to-sub-lem L = begin
    < getSnd [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
      ≈⟨ unrestrict-snd (label-to-sub (label₁ L)) ⟩
    < apt L (PPShift PPHere) >tm
      ≡⟨⟩
    < apt (label₂ L) PPHere >tm
      ≈˘⟨ label-to-sub-path (label₂ L) PHere ⟩
    < Var (fromℕ _) [ label-to-sub (label₂ L) ]tm >tm ∎

  label-to-sub-ppath : (L : Label X S A) → (P : PPath S) → path-to-term (carrier P) [ label-to-sub L ]tm ≃tm apt L P
  label-to-sub-ppath L ⟦ P ⟧ = begin
    < path-to-term P [ label-to-sub L ]tm >tm
      ≈⟨ label-to-sub-path L P ⟩
    < path-to-term (P >>= L) >tm
      ≈⟨ path-to-term-≃ (extend-ppath ⟦ P ⟧ L) ⟩
    < apt L ⟦ P ⟧ >tm ∎

  connect-tree-inc-left-pphere : (S : Tree n)
                               → (T : Tree m)
                               → ap (connect-tree-inc-left S T) PPHere ≃p (PHere {S = connect-tree S T})
  connect-tree-inc-left-pphere Sing T = refl≃p
  connect-tree-inc-left-pphere (Join S₁ S₂) T = refl≃p

  connect-tree-inc-pphere : (S : Tree n)
                          → (T : Tree m)
                          → ap (connect-tree-inc-left S T) (last-path S) ≃p ap (connect-tree-inc-right S T) PPHere
  connect-tree-inc-pphere Sing T = refl≃p
  connect-tree-inc-pphere (Join S₁ S₂) T = ≃Shift refl≃ (connect-tree-inc-pphere S₂ T)

label-sub-to-sub : {X : MaybeTree n} → (L : Label X S A) → (Y : MaybeTree m) → (σ : Sub n m B) → label-to-sub (label-sub L Y σ) ≃s σ ∘ label-to-sub L
label-sub-to-sub {S = Sing} L Y σ = refl≃s
label-sub-to-sub {S = Join S T} L Y σ = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (label-sub L Y σ))))
                     (label-to-sub (label₂ (label-sub L Y σ))) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (σ ∘ unrestrict (label-to-sub (label₁ L)))
                     (σ ∘ label-to-sub (label₂ L)) >s
    ≈˘⟨ sub-from-connect-sub (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) σ ⟩
  < σ ∘ label-to-sub L >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (label₁ (label-sub L Y σ))) ≃s (σ ∘ unrestrict (label-to-sub (label₁ L)))
    l1 = begin
      < unrestrict (label-to-sub (label₁ (label-sub L Y σ))) >s
        ≡⟨⟩
      < unrestrict (label-to-sub (label-sub (label₁ L) Y σ)) >s
        ≈⟨ unrestrict-≃ (label-sub-to-sub (label₁ L) Y σ) ⟩
      < unrestrict (σ ∘ label-to-sub (label₁ L)) >s
        ≈⟨ unrestrict-comp-higher σ (label-to-sub (label₁ L)) ⟩
      < σ ∘ unrestrict (label-to-sub (label₁ L)) >s ∎

    l2 : label-to-sub (label₂ (label-sub L Y σ)) ≃s (σ ∘ label-to-sub (label₂ L))
    l2 = begin
      < label-to-sub (label₂ (label-sub L Y σ)) >s
        ≡⟨⟩
      < label-to-sub (label-sub (label₂ L) Y σ) >s
        ≈⟨ label-sub-to-sub (label₂ L) Y σ ⟩
      < σ ∘ label-to-sub (label₂ L) >s ∎

_≃l_ : Label X S A → Label Y S B → Set
_≃l_ {S = S} L M = (P : PPath S) → ap L P ≃p ap M P

label-to-sub-≃ : (L : Label X S A) → (M : Label Y S B) → (L ≃l M) → A ≃ty B → label-to-sub L ≃s label-to-sub M
label-to-sub-≃ {S = Sing} L M p q = Ext≃ (Null≃ q) (path-to-term-≃ (p PPHere))
label-to-sub-≃ {S = Join S T} L M p q
  = sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ (label₁ L) (label₁ M) (λ P → p (PPExt P)) (Arr≃ (path-to-term-≃ (p PPHere)) q (path-to-term-≃ (p (PPShift PPHere))))))
                       (label-to-sub-≃ (label₂ L) (label₂ M) (λ P → p (PPShift P)) q)

susp-label-to-sub : (L : Label X S A) → label-to-sub (susp-label L) ≃s suspSubRes (label-to-sub L)
susp-label-to-sub {S = Sing} L = Ext≃ (Null≃ refl≃ty) (susp-path-to-term (ap L PPHere))
susp-label-to-sub {S = Join S T} {A = A} L = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (susp-label L))))
                                 (label-to-sub (label₂ (susp-label L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ (label₁ (susp-label L)) (susp-label (label₁ L)) (λ P → refl≃p) (Arr≃ (susp-path-to-term (ap L PPHere))
                                                                                                                              refl≃ty
                                                                                                                              (susp-path-to-term (ap L (PPShift PPHere)))))) refl≃s ⟩
  < sub-from-connect (unrestrict (label-to-sub (susp-label (label₁ L))))
                                 (label-to-sub (susp-label (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (susp-label-to-sub (label₁ L)))
                          (susp-label-to-sub (label₂ L)) ⟩
  < sub-from-connect (unrestrict (suspSubRes (label-to-sub (label₁ L)))) (suspSubRes (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-≃ (sub-res-unrestrict-comm (label-to-sub (label₁ L))) refl≃s ⟩
  < sub-from-connect (suspSubRes (unrestrict (label-to-sub (label₁ L)))) (suspSubRes (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-susp-res (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < suspSubRes (sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                             (label-to-sub (label₂ L))) >s ∎
  where
    open Reasoning sub-setoid

lift-label-to-sub : (L : Label (Other n) S A) → label-to-sub (lift-label L) ≃s liftSub (label-to-sub L)
lift-label-to-sub {S = Sing} L = refl≃s
lift-label-to-sub {S = Join S T} L = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (lift-label L))))
                                 (label-to-sub (label₂ (lift-label L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (lift-label-to-sub (label₁ L))) (lift-label-to-sub (label₂ L)) ⟩
  < sub-from-connect (unrestrict (liftSub (label-to-sub (label₁ L)))) (liftSub (label-to-sub (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-lift (label-to-sub (label₁ L))) (refl≃s {σ = liftSub (label-to-sub (label₂ L))}) ⟩
  < sub-from-connect (liftSub (unrestrict (label-to-sub (label₁ L)))) (liftSub (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-lift (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < liftSub (sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))) >s ∎
  where
    open Reasoning sub-setoid

id-label-to-sub : (S : Tree n) → label-to-sub (id-label S) ≃s idSub {n = suc n}
id-label-to-sub Sing = refl≃s
id-label-to-sub (Join S T) = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (id-label (Join S T)))))
                                 (label-to-sub (label₂ (id-label (Join S T)))) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (connect-susp-inc-left _ _) (connect-susp-inc-right _ _) >s
    ≈⟨ sub-from-connect-prop getSnd ⟩
  < idSub >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (label₁ (id-label (Join S T)))) ≃s connect-susp-inc-left (tree-size S) (tree-size T)
    l1 = begin
      < unrestrict (label-to-sub (label₁ (id-label (Join S T)))) >s
        ≈˘⟨ unrestrict-≃ (label-to-sub-≃ (label-sub (susp-label (id-label S))
                                                    (someTree (Join S T))
                                                    (connect-susp-inc-left (tree-size S) (tree-size T)))
                                         (label₁ (id-label (Join S T)))
                                         (λ P → ≃Other (sub-action-≃-tm (id-on-tm (suspTm (path-to-term (carrier P)))) refl≃s))
                                         (Arr≃ (connect-inc-left-fst-var getSnd (tree-size T))
                                               refl≃ty
                                               (connect-inc-fst-var getSnd (tree-size T)))) ⟩
      < unrestrict (label-to-sub (label-sub (susp-label (id-label S)) (someTree (Join S T)) (connect-susp-inc-left (tree-size S) (tree-size T)))) >s
        ≈⟨ unrestrict-≃ (label-sub-to-sub (susp-label (id-label S)) (someTree (Join S T)) (connect-susp-inc-left (tree-size S) (tree-size T))) ⟩
      < unrestrict (connect-susp-inc-left (tree-size S) (tree-size T) ∘ label-to-sub (susp-label (id-label S))) >s
        ≈⟨ unrestrict-comp-higher (connect-susp-inc-left (tree-size S) (tree-size T)) (label-to-sub (susp-label (id-label S))) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ∘ unrestrict (label-to-sub (susp-label (id-label S))) >s
        ≈⟨ sub-action-≃-sub (unrestrict-≃ (susp-label-to-sub (id-label S))) refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ∘ suspSub (label-to-sub (id-label S)) >s
        ≈⟨ sub-action-≃-sub (susp-sub-≃ (id-label-to-sub S)) refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ∘ suspSub idSub >s
        ≈⟨ sub-action-≃-sub susp-functorial-id refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ∘ idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-left (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) >s ∎

    l2 : label-to-sub (label₂ (id-label (Join S T))) ≃s connect-susp-inc-right (tree-size S) (tree-size T)
    l2 = begin
      < label-to-sub (label₂ (id-label (Join S T))) >s
        ≈⟨ label-to-sub-≃ (label₂ (id-label (Join S T))) (label-sub (id-label T) (someTree (Join S T)) (connect-susp-inc-right (tree-size S) (tree-size T))) (λ P → ≃Other refl≃tm) refl≃ty ⟩
      < label-to-sub (label-sub (id-label T) (someTree (Join S T)) (connect-susp-inc-right (tree-size S) (tree-size T))) >s
        ≈⟨ label-sub-to-sub (id-label T) (someTree (Join S T)) (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ∘ label-to-sub (id-label T) >s
        ≈⟨ sub-action-≃-sub (id-label-to-sub T) refl≃s ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ∘ idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) >s ∎

sub-to-label-to-sub : (S : Tree n) → (σ : Sub (suc n) m A) → (Y : MaybeTree m) → label-to-sub (to-label S σ Y) ≃s σ
sub-to-label-to-sub S σ Y = begin
  < label-to-sub (to-label S σ Y) >s
    ≡⟨⟩
  < label-to-sub (label-sub (id-label S) Y σ) >s
    ≈⟨ label-sub-to-sub (id-label S) Y σ ⟩
  < σ ∘ label-to-sub (id-label S) >s
    ≈⟨ sub-action-≃-sub (id-label-to-sub S) refl≃s ⟩
  < σ ∘ idSub >s
    ≈⟨ id-right-unit σ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid

sub-path-equality : {S : Tree n} → (σ : Sub (suc n) m A) → (τ : Sub (suc n) m′ B) → ((P : PPath S) → path-to-term (carrier P) [ σ ]tm ≃tm path-to-term (carrier P) [ τ ]tm) → A ≃ty B → σ ≃s τ
sub-path-equality {S = S} σ τ f p = begin
  < σ >s
    ≈˘⟨ sub-to-label-to-sub S σ (Other _) ⟩
  < label-to-sub (to-label S σ (Other _)) >s
    ≈⟨ label-to-sub-≃ (to-label S σ (Other _)) (to-label S τ (Other _)) (λ P → ≃Other (f P)) p ⟩
  < label-to-sub (to-label S τ (Other _)) >s
    ≈⟨ sub-to-label-to-sub S τ (Other _) ⟩
  < τ >s ∎
  where
    open Reasoning sub-setoid

_≃lm_ : (L : Label X S A) → (M : Label Y S B) → Set
_≃lm_ {S = S} L M = (Q : PPath S) → .⦃ is-Maximal Q ⦄ → apt L Q ≃tm apt M Q

connect-label-pphere : (L : Label X S A)
                     → (M : Label X T A)
                     → connect-label L M .ap PPHere ≃p ap L PPHere
connect-label-pphere {S = Sing} L M = refl≃p
connect-label-pphere {S = Join S₁ S₂} L M = refl≃p

connect-label-inc-left : (L : Label X S A)
                       → (M : Label X T A)
                       → (label-comp (connect-tree-inc-left S T) (connect-label L M)) ≃lm L
connect-label-inc-left {S = Sing} L M ⟦ PHere ⟧ = refl≃tm
connect-label-inc-left {S = Join S₁ S₂} L M ⟦ PExt Q ⟧ = path-to-term-≃ (extend-ppath ⟦ PExt Q ⟧ (connect-label L M))
connect-label-inc-left {S = Join S₁ S₂} L M ⟦ PShift Q ⟧ = connect-label-inc-left (label₂ L) M ⟦ Q ⟧ ⦃ proj₂ it ⦄

-- connect-label₂ : (L : Label X (Join S T) A) → (M : Label X U A) → label₂ (connect-label L M) ≃l connect-label (label₂ L) M
-- connect-label₂ = {!!}

replace-label-map-func : (f : Path X → Path Y) → (L : Label-func X S) → (P : Path X) → (Z : PPath S) → map-lf f (replace-label-func L P) Z ≃p replace-label-func (map-lf f L) (f P) Z
replace-label-map-func f L P ⟦ PHere ⟧ = refl≃p
replace-label-map-func f L P ⟦ PExt Z ⟧ = refl≃p
replace-label-map-func f L P ⟦ PShift Z ⟧ = refl≃p

connect-label-map-func : (f : Path X → Path Y) → (L : Label-func X S) → (M : Label-func X T) → (Z : PPath (connect-tree S T)) → map-lf f (connect-label-func L M) Z ≃p connect-label-func (map-lf f L) (map-lf f M) Z
connect-label-map-func {S = Sing} f L M = replace-label-map-func f M (L PPHere)
connect-label-map-func {S = Join S₁ S₂} f L M ⟦ PHere ⟧ = refl≃p
connect-label-map-func {S = Join S₁ S₂} f L M ⟦ PExt Z ⟧ = refl≃p
connect-label-map-func {S = Join S₁ S₂} f L M ⟦ PShift Z ⟧ = connect-label-map-func f (λ X → L (PPShift X)) M ⟦ Z ⟧

replace-label-prop : (L : Label X S A) → replace-label L (ap L PPHere) ≃l L
replace-label-prop L ⟦ PHere ⟧ = refl≃p
replace-label-prop L ⟦ PExt Q ⟧ = refl≃p
replace-label-prop L ⟦ PShift Q ⟧ = refl≃p

connect-label-prop : (S : Tree n) → (T : Tree m) → connect-label (connect-tree-inc-left S T) (connect-tree-inc-right S T) ≃l id-label (connect-tree S T)
connect-label-prop Sing T Z = replace-label-prop (id-label T) Z
connect-label-prop (Join S₁ S₂) T ⟦ PHere ⟧ = refl≃p
connect-label-prop (Join S₁ S₂) T ⟦ PExt Z ⟧ = refl≃p
connect-label-prop (Join S₁ S₂) T ⟦ PShift Z ⟧ = trans≃p (sym≃p (connect-label-map-func PShift (connect-tree-inc-left S₂ T .ap) (connect-tree-inc-right S₂ T .ap) ⟦ Z ⟧)) (≃Shift refl≃ (connect-label-prop S₂ T ⟦ Z ⟧))

label-≃ : S ≃ T → Label X T A → Label X S A
label-≃ p L .ap Z = ap L (ppath-≃ p Z)

_≃l′_ : Label X S A → Label Y T B → Set
_≃l′_ {S = S} {T = T} L M = Σ[ p ∈ S ≃ T ] L ≃l label-≃ p M

label-to-sub-≃′ : (L : Label X S A) → (M : Label Y T B) → L ≃l′ M → A ≃ty B → label-to-sub L ≃s label-to-sub M
label-to-sub-≃′ L M (p ,, q) r with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = label-to-sub-≃ L M (λ P → trans≃p (q P) (≃Other (lem P))) r
  where
    open Reasoning tm-setoid
    lem : (P : PPath _) → apt M (ppath-≃ p P) ≃tm apt M P
    lem P = begin
      < apt M (ppath-≃ p P) >tm
        ≈˘⟨ label-to-sub-ppath M (ppath-≃ p P) ⟩
      < path-to-term (carrier (ppath-≃ p P)) [ label-to-sub M ]tm >tm
        ≈⟨ sub-action-≃-tm (path-to-term-≃ (ppath-≃-≃p p P)) refl≃s ⟩
      < path-to-term (carrier P) [ label-to-sub M ]tm >tm
        ≈⟨ label-to-sub-ppath M P ⟩
      < apt M P >tm ∎

label-to-sub-comp : (L : Label (someTree T) S A) → (M : Label X T B)
                  → label-to-sub (label-comp L M) ≃s label-to-sub M ∘ label-to-sub L
label-to-sub-comp {S = S} L M = sub-path-equality (label-to-sub (label-comp L M)) (label-to-sub M ∘ label-to-sub L) lem refl≃ty
  where
    open Reasoning tm-setoid
    lem : (P : PPath S) →
            (path-to-term (carrier P) [ label-to-sub (label-comp L M) ]tm) ≃tm
            (path-to-term (carrier P) [ label-to-sub M ∘ label-to-sub L ]tm)
    lem ⟦ P ⟧ = begin
      < path-to-term P [ label-to-sub (label-comp L M) ]tm >tm
        ≈⟨ label-to-sub-ppath (label-comp L M) ⟦ P ⟧ ⟩
      < apt (label-comp L M) ⟦ P ⟧ >tm
        ≡⟨⟩
      < path-to-term (ap L ⟦ P ⟧ >>= M) >tm
        ≈˘⟨ label-to-sub-path M (ap L ⟦ P ⟧) ⟩
      < apt L ⟦ P ⟧ [ label-to-sub M ]tm >tm
        ≈˘⟨ sub-action-≃-tm (label-to-sub-ppath L ⟦ P ⟧) refl≃s ⟩
      < path-to-term P [ label-to-sub L ]tm [ label-to-sub M ]tm >tm
        ≈˘⟨ assoc-tm (label-to-sub M) (label-to-sub L) (path-to-term P) ⟩
      < path-to-term P [ label-to-sub M ∘ label-to-sub L ]tm >tm ∎
