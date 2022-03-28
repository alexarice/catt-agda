module Catt.Tree.Substitution.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Substitution
open import Catt.Syntax.SyntacticEquality
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties

_≃ts_ : TreeSub n m → TreeSub n′ m′ → Set
S ≃ts T = TreeEq _≃tm_ S T

TreeSub-to-Sub-≃ : S ≃ts T → A ≃ty B → TreeSub-to-Sub S A ≃s TreeSub-to-Sub T B
TreeSub-to-Sub-≃ (Sing≃ x) q = Ext≃ (Null≃ q) x
TreeSub-to-Sub-≃ (Join≃ x p q) r = sub-from-connect-≃ (unrestrict-≃ (TreeSub-to-Sub-≃ p (Arr≃ x r (first-label-≃ q)))) (TreeSub-to-Sub-≃ q r)

first-label-sub : (T : TreeSub n m) → (σ : Sub m l A) → first-label (T [ σ ]ts) ≃tm first-label T [ σ ]tm
first-label-sub (Sing x) σ = refl≃tm
first-label-sub (Join x _ _) σ = refl≃tm

first-label-idTreeSub : (T : Tree⊤ n) → first-label (idTreeSub T) ≃tm Var (fromℕ n)
first-label-idTreeSub (Sing x) = refl≃tm
first-label-idTreeSub (Join x S T) = connect-inc-left-fst-var getSnd (tree-size T)

TreeSub-to-Sub-subbed : (T : TreeSub n m) → (A : Ty m) → (σ : Sub m l B) → TreeSub-to-Sub (T [ σ ]ts) (A [ σ ]ty) ≃s σ ∘ TreeSub-to-Sub T A
TreeSub-to-Sub-subbed (Sing x) A σ = refl≃s
TreeSub-to-Sub-subbed (Join x S T) A σ = begin
  < sub-from-connect
      (unrestrict (TreeSub-to-Sub (S [ σ ]ts) ((x [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ first-label (T [ σ ]ts))))
      (TreeSub-to-Sub (T [ σ ]ts) (A [ σ ]ty)) >s
    ≈⟨ sub-from-connect-≃ lem (TreeSub-to-Sub-subbed T A σ) ⟩
  < sub-from-connect
    (σ ∘ unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)))
    (σ ∘ TreeSub-to-Sub T A) >s
    ≈˘⟨ sub-from-connect-sub (unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)))
                             (TreeSub-to-Sub T A)
                             σ ⟩
  < σ ∘ sub-from-connect
        (unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)))
        (TreeSub-to-Sub T A) >s ∎
  where
    open Reasoning sub-setoid

    lem : unrestrict
            (TreeSub-to-Sub (S [ σ ]ts)
             ((x [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ first-label (T [ σ ]ts)))
            ≃s (σ ∘ unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)))
    lem = begin
      < unrestrict (TreeSub-to-Sub (S [ σ ]ts) ((x [ σ ]tm) ─⟨ A [ σ ]ty ⟩⟶ first-label (T [ σ ]ts))) >s
        ≈⟨ unrestrict-≃ (TreeSub-to-Sub-≃ (reflTree refl≃tm {T = S [ σ ]ts}) (Arr≃ refl≃tm refl≃ty (first-label-sub T σ))) ⟩
      < unrestrict (TreeSub-to-Sub (S [ σ ]ts) ((x ─⟨ A ⟩⟶ first-label T) [ σ ]ty)) >s
        ≈⟨ unrestrict-≃ (TreeSub-to-Sub-subbed S (x ─⟨ A ⟩⟶ first-label T) σ) ⟩
      < unrestrict (σ ∘ TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)) >s
        ≈˘⟨ unrestrict-comp-left σ (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)) ⟩
      < σ ∘ unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)) >s ∎

map-tree-susp : (T : TreeSub n m) → (A : Ty m) → TreeSub-to-Sub (map-tree suspTm T) (suspTy A) ≃s suspSubRes (TreeSub-to-Sub T A)
map-tree-susp (Sing x) A = refl≃s
map-tree-susp (Join x S T) A = begin
  < sub-from-connect
      (unrestrict
       (TreeSub-to-Sub (map-tree suspTm S)
        (suspTm x ─⟨ suspTy A ⟩⟶ first-label {Xr = Tm} (map-tree suspTm T))))
      (TreeSub-to-Sub (map-tree suspTm T) (suspTy A)) >s
    ≈⟨ sub-from-connect-≃ lem (map-tree-susp T A) ⟩
  < sub-from-connect
    (suspSubRes
     (unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T))))
    (suspSubRes (TreeSub-to-Sub T A))
    >s
    ≈˘⟨ sub-from-connect-susp-res (unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T))) (TreeSub-to-Sub T A) ⟩
  < suspSubRes
      (sub-from-connect
       (unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)))
       (TreeSub-to-Sub T A)) >s ∎
  where
    open Reasoning sub-setoid

    lem : unrestrict
            (TreeSub-to-Sub (map-tree suspTm S)
             (suspTm x ─⟨ suspTy A ⟩⟶ first-label {Xr = Tm} (map-tree suspTm T)))
            ≃s
            suspSubRes
            (unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)))
    lem = begin
      < unrestrict (TreeSub-to-Sub (map-tree suspTm S)
        (suspTm x ─⟨ suspTy A ⟩⟶ first-label {Xr = Tm} (map-tree suspTm T))) >s
        ≈⟨ unrestrict-≃ (TreeSub-to-Sub-≃ (reflTree refl≃tm {T = map-tree suspTm S}) (Arr≃ refl≃tm refl≃ty (first-label-map {_∼_ = _≃tm_} suspTm T refl≃tm))) ⟩
      < unrestrict (TreeSub-to-Sub (map-tree suspTm S) (suspTy (x ─⟨ A ⟩⟶ first-label T)))
        >s
        ≈⟨ unrestrict-≃ (map-tree-susp S (x ─⟨ A ⟩⟶ first-label T)) ⟩
      < unrestrict (suspSubRes (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T))) >s
        ≈˘⟨ sub-res-unrestrict-comm (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T)) ⟩
      < suspSubRes (unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ first-label T))) >s ∎

idTreeSub-to-idSub : (T : Tree⊤ n) → TreeSub-to-Sub (idTreeSub T) ⋆ ≃s idSub {n = (suc n)}
idTreeSub-to-idSub Sing⊤ = refl≃s
idTreeSub-to-idSub (Join⊤ S T) = begin
  < sub-from-connect
      (unrestrict
        (TreeSub-to-Sub
         (map-tree suspTm (idTreeSub S) [ connect-susp-inc-left _ _ ]ts)
         ((getFst [ connect-susp-inc-left _ _ ]tm) ─⟨ ⋆ ⟩⟶
          first-label (idTreeSub T [ connect-susp-inc-right _ _ ]ts))))
      (TreeSub-to-Sub (idTreeSub T [ connect-susp-inc-right _ _ ]ts) ⋆) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (connect-inc-left getSnd _) (connect-inc-right getSnd _) >s
    ≈⟨ sub-from-connect-prop getSnd ⟩
  < idSub >s ∎
  where

    l3 : first-label (idTreeSub T [ connect-susp-inc-right _ _ ]ts) ≃tm
           (getSnd [ connect-susp-inc-left _ _ ]tm)
    l3 = begin
      < first-label (idTreeSub T [ connect-susp-inc-right _ _ ]ts) >tm
        ≈⟨ first-label-sub (idTreeSub T) (connect-susp-inc-right _ _) ⟩
      < first-label (idTreeSub T) [ connect-susp-inc-right _ _ ]tm >tm
        ≈⟨ sub-action-≃-tm (first-label-idTreeSub T) refl≃s ⟩
      < Var (fromℕ _) [ connect-susp-inc-right _ _ ]tm >tm
        ≈˘⟨ connect-inc-fst-var getSnd _ ⟩
      < getSnd [ connect-susp-inc-left _ _ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    open Reasoning sub-setoid

    l4 : unrestrict
           (TreeSub-to-Sub (map-tree suspTm (idTreeSub S))
            (getFst ─⟨ ⋆ ⟩⟶ getSnd))
           ≃s idSub
    l4 = begin
      < unrestrict (TreeSub-to-Sub (map-tree suspTm (idTreeSub S)) (getFst ─⟨ ⋆ ⟩⟶ getSnd)) >s
        ≈⟨ unrestrict-≃ (map-tree-susp (idTreeSub S) ⋆) ⟩
      < suspSub (TreeSub-to-Sub (idTreeSub S) ⋆) >s
        ≈⟨ susp-sub-≃ (idTreeSub-to-idSub S) ⟩
      < suspSub idSub >s
        ≈⟨ susp-functorial-id ⟩
      < idSub >s ∎

    l1 : unrestrict
           (TreeSub-to-Sub
             (map-tree suspTm (idTreeSub S) [ connect-susp-inc-left _ _ ]ts)
             ((getFst [ connect-susp-inc-left _ _ ]tm) ─⟨ ⋆ ⟩⟶
              first-label (idTreeSub T [ connect-susp-inc-right _ _ ]ts)))
       ≃s connect-inc-left getSnd (tree-size T)
    l1 = begin
      < unrestrict
        (TreeSub-to-Sub (map-tree suspTm (idTreeSub S) [ connect-susp-inc-left _ _ ]ts)
                        ((getFst [ connect-susp-inc-left _ _ ]tm) ─⟨ ⋆ ⟩⟶
                        first-label (idTreeSub T [ connect-susp-inc-right _ _ ]ts))) >s
        ≈⟨ unrestrict-≃ (TreeSub-to-Sub-≃ (reflTree refl≃tm {T = map-tree suspTm (idTreeSub S) [ connect-susp-inc-left _ _ ]ts}) (Arr≃ refl≃tm refl≃ty l3)) ⟩
      < unrestrict (TreeSub-to-Sub (map-tree suspTm (idTreeSub S) [ connect-susp-inc-left _ _ ]ts)
                                   ((getFst ─⟨ ⋆ ⟩⟶ getSnd) [ connect-susp-inc-left _ _ ]ty)) >s
        ≈⟨ unrestrict-≃ (TreeSub-to-Sub-subbed (map-tree suspTm (idTreeSub S)) (getFst ─⟨ ⋆ ⟩⟶ getSnd) (connect-susp-inc-left _ (tree-size T))) ⟩
      < unrestrict (connect-susp-inc-left _ (tree-size T) ∘
                     TreeSub-to-Sub (map-tree suspTm (idTreeSub S))
                     (getFst ─⟨ ⋆ ⟩⟶ getSnd)) >s
        ≈˘⟨ unrestrict-comp-left (connect-susp-inc-left _ (tree-size T)) (TreeSub-to-Sub (map-tree suspTm (idTreeSub S))
                                                                           (getFst ─⟨ ⋆ ⟩⟶ getSnd)) ⟩
      < connect-susp-inc-left _ (tree-size T) ∘ unrestrict (TreeSub-to-Sub (map-tree suspTm (idTreeSub S))
         (getFst ─⟨ ⋆ ⟩⟶ getSnd)) >s
        ≈⟨ sub-action-≃-sub l4 refl≃s ⟩
      < connect-susp-inc-left _ (tree-size T) ∘ idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-left _ (tree-size T)) ⟩
      < connect-inc-left getSnd (tree-size T) >s ∎

    l2 : TreeSub-to-Sub (idTreeSub T [ connect-susp-inc-right (tree-size S) (tree-size T) ]ts) ⋆ ≃s connect-susp-inc-right (tree-size S) (tree-size T)
    l2 = begin
      < TreeSub-to-Sub (idTreeSub T [ connect-susp-inc-right (tree-size S) (tree-size T) ]ts) ⋆ >s
        ≈⟨ TreeSub-to-Sub-subbed (idTreeSub T) ⋆ (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ∘ TreeSub-to-Sub (idTreeSub T) ⋆ >s
        ≈⟨ sub-action-≃-sub (idTreeSub-to-idSub T) refl≃s ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ∘ idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) >s ∎

sub-to-treeSub-to-sub : (T : Tree⊤ n) → (σ : Sub (suc n) m A) → TreeSub-to-Sub (sub-to-treeSub T σ) A ≃s σ
sub-to-treeSub-to-sub {A = A} T σ = begin
  < TreeSub-to-Sub (idTreeSub T [ σ ]ts) A >s
    ≈⟨ TreeSub-to-Sub-subbed (idTreeSub T) ⋆ σ ⟩
  < σ ∘ TreeSub-to-Sub (idTreeSub T) ⋆ >s
    ≈⟨ sub-action-≃-sub (idTreeSub-to-idSub T) refl≃s ⟩
  < σ ∘ idSub >s
    ≈⟨ id-right-unit σ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid
