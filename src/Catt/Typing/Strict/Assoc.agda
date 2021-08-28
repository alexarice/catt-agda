{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

module Catt.Typing.Strict.Assoc where

open import Catt.Typing.Base
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Pasting
-- open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import Catt.Pasting.Insertion
open import Catt.Pasting.Tree
open import Data.Fin using (Fin;zero;suc)
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤;tt)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Nullary
open import Catt.Suspension
open import Catt.Suspension.Properties

record InsertionData : Set where
  field
    {id-n′} : ℕ
    id-Γ : Ctx id-n′
    {id-m} : ℕ
    {id-d} : ℕ
    {id-n} : ℕ
    id-S : Tree id-m
    id-A : Ty (tree-to-ctx id-S) id-d
    id-σ : Sub (tree-to-ctx id-S) id-Γ
    id-B : Ty id-Γ id-d
    id-x : ctx-dim (tree-to-ctx id-S) ≤ ty-dim id-A
    id-P : Path id-S
    id-bp : is-branching-path id-P
    id-T : Tree id-n
    id-τ : Sub (tree-to-ctx id-T) id-Γ
    id-C : Ty (tree-to-ctx id-T) (suc (height-of-branching id-P id-bp))
    id-D : Ty id-Γ (suc (height-of-branching id-P id-bp))
    id-y : ctx-dim (tree-to-ctx id-T) ≤ ty-dim id-C
    id-lh : has-linear-height (path-length id-P) id-T
    id-tlh : type-has-linear-height (path-length id-P) id-T id-lh id-C

open InsertionData

insertionRule : Rule
insertionRule .Args = InsertionData
insertionRule .tctIndex = Fin 2
insertionRule .tgtdims zero a = a .id-d
insertionRule .tgtdims (suc zero) a = suc (height-of-branching (a .id-P) _)
insertionRule .tctLen zero a = a .id-n′
insertionRule .tctLen (suc i) a = a .id-n′
insertionRule .tctCtx zero a = a .id-Γ
insertionRule .tctCtx (suc i) a = a .id-Γ
insertionRule .tct zero a = Coh (tree-to-ctx (a .id-S)) (a .id-A) (a .id-x) (a .id-σ)
insertionRule .tct (suc zero) a = Coh (tree-to-ctx (a .id-T)) (a .id-C) (a .id-y) (a .id-τ)
insertionRule .tctTy zero a = a .id-B
insertionRule .tctTy (suc zero) a = a .id-D
insertionRule .eqtIndex = Fin 1
insertionRule .eqtlhsdim zero a = suc (suc (height-of-branching (a .id-P) (a .id-bp)))
insertionRule .eqtlhsLen zero a = a .id-n′
insertionRule .eqtlhsCtx zero a = a .id-Γ
insertionRule .eqtlhs zero a = branching-path-to-var (a .id-S) (a .id-P) (a .id-bp) [ a .id-σ ]tm
insertionRule .eqtrhsdim zero a = suc (suc (height-of-branching (a .id-P) _))
insertionRule .eqtrhsLen zero a = a .id-n′
insertionRule .eqtrhsCtx zero a = a .id-Γ
insertionRule .eqtrhs zero a = Coh (tree-to-ctx (a .id-T)) (a .id-C) (a .id-y) (a .id-τ)
insertionRule .dimlhs a = suc (a .id-d)
insertionRule .dimrhs a = suc (a .id-d)
insertionRule .lhsLen a = a .id-n′
insertionRule .lhsCtx a = a .id-Γ
insertionRule .rhsLen a = a .id-n′
insertionRule .rhsCtx a = a .id-Γ
insertionRule .lhs a = Coh (tree-to-ctx (a .id-S)) (a .id-A) (a .id-x) (a .id-σ)
insertionRule .rhs a = Coh (tree-to-ctx (insertion-tree (a .id-S)
                                                        (a .id-P)
                                                        (a .id-T)
                                                        (a .id-lh)))
                           (a .id-A [ (exterior-sub (a .id-S)
                                                    (a .id-P)
                                                    (a .id-bp)
                                                    (a .id-T)
                                                    (a .id-lh)
                                                    (a .id-C)
                                                    (a .id-y)
                                                    (a .id-tlh)) ]ty)
                           (≤-trans (≤-reflexive (tree-to-ctx-dim (insertion-tree (a .id-S) (a .id-P) (a .id-T) _))) (≤-trans (s≤s (insertion-reduces-dim (a .id-S) (a .id-P) (a .id-T) (a .id-bp) (a .id-lh) (≤-pred (≤-trans (≤-reflexive (sym (tree-to-ctx-dim (a .id-T)))) (a .id-y))))) (≤-trans (≤-reflexive (sym (tree-to-ctx-dim (a .id-S)))) (a .id-x))))
                           (sub-from-insertion (a .id-S)
                                               (a .id-P)
                                               (a .id-bp)
                                               (a .id-T)
                                               (a .id-lh)
                                               (a .id-C)
                                               (a .id-y)
                                               (a .id-tlh)
                                               (a .id-σ)
                                               (a .id-τ))

open import Catt.Typing ⊤ (λ x → insertionRule)

Ins≈ : (S : Tree n)
     → {A : Ty (tree-to-ctx S) d}
     → {σ : Sub (tree-to-ctx S) Γ}
     → .{x : ctx-dim (tree-to-ctx S) ≤ ty-dim A}
     → (ty : Typing-Tm Γ (Coh (tree-to-ctx S) A x σ) B)
     → (P : Path S)
     → (bp : is-branching-path P)
     → (T : Tree m)
     → {τ : Sub (tree-to-ctx T) Γ}
     → {C : Ty (tree-to-ctx T) (suc (height-of-branching P _))}
     → {D : Ty Γ (suc (height-of-branching P _))}
     → .{y : ctx-dim (tree-to-ctx T) ≤ ty-dim C}
     → (ty2 : Typing-Tm Γ (Coh (tree-to-ctx T) C y τ) D)
     → (branching-path-to-var S P bp [ σ ]tm) ≈tm (Coh (tree-to-ctx T) C y τ)
     → (lh : has-linear-height (path-length P) T)
     → (tlh : type-has-linear-height (path-length P) T lh C)
     → (Coh (tree-to-ctx S) A x σ) ≈tm
       (Coh (tree-to-ctx (insertion-tree S
                                         P
                                         T
                                         lh))
            (A [ exterior-sub S P bp T lh C y tlh ]ty)
                 -- Use reasoning?
            (≤-trans (≤-reflexive (tree-to-ctx-dim (insertion-tree S P T _))) (≤-trans (s≤s (insertion-reduces-dim S P T bp lh (≤-pred (≤-trans (≤-reflexive (sym (tree-to-ctx-dim T))) y)))) (≤-trans (≤-reflexive (sym (tree-to-ctx-dim S))) x)))
            (sub-from-insertion S P bp T lh C y tlh σ τ))
Ins≈ {Γ = Γ} {B = B} S {x = x} ty P bp T {D = D} {y = y} ty2 eqt lh tlh = Rule≈ tt id typing eq
  where
    id : InsertionData
    id .id-n′ = _
    id .id-Γ = Γ
    id .id-m = _
    id .id-d = _
    id .id-n = _
    id .id-S = _
    id .id-A = _
    id .id-σ = _
    id .id-B = B
    id .id-x = recompute ((ctx-dim (tree-to-ctx (id .id-S))) ≤? (ty-dim (id .id-A))) x
    id .id-P = P
    id .id-bp = bp
    id .id-T = T
    id .id-τ = _
    id .id-C = _
    id .id-D = D
    id .id-y = recompute ((ctx-dim (tree-to-ctx (id .id-T))) ≤? (ty-dim (id .id-C))) y
    id .id-lh = lh
    id .id-tlh = tlh

    typing : (j : Fin 2) → Typing-Tm (insertionRule .tctCtx j id) (insertionRule .tct j id) (insertionRule .tctTy j id)
    typing zero = ty
    typing (suc zero) = ty2

    eq : (j : Fin 1) → (insertionRule .eqtlhs j id) ≈tm (insertionRule .eqtrhs j id)
    eq zero = eqt

open import Catt.Typing.Properties.Base ⊤ (λ x → insertionRule)

props : (i : ⊤) → Props i
props i .lift-rule a tc eq = begin
  < liftTerm (insertionRule .lhs a) >tm ≡⟨⟩
  < Coh (tree-to-ctx (a .id-S)) (a .id-A) _ (liftSub (a .id-σ)) >tm ≈⟨ Ins≈ (a .id-S) (tc zero) (a .id-P) (a .id-bp) (a .id-T) (tc (suc zero)) lem (a .id-lh) (a .id-tlh) ⟩
  < Coh (tree-to-ctx (insertion-tree (a .id-S) (a .id-P) (a .id-T) _)) (a .id-A [ exterior-sub (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _ (a .id-tlh) ]ty) _ (sub-from-insertion (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _ (a .id-tlh) (liftSub (a .id-σ)) (liftSub (a .id-τ))) >tm
    ≈⟨ reflexive≈tm (Coh≃ refl≃c refl≃ty (sym≃s lem2)) ⟩
  < liftTerm (insertionRule .rhs a) >tm ∎
  where
    lem2 : liftSub (sub-from-insertion (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _ (a .id-tlh) (a .id-σ) (a .id-τ)) ≃s sub-from-insertion (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _ (a .id-tlh) (liftSub (a .id-σ)) (liftSub (a .id-τ))
    lem2 = begin
      < liftSub (sub-from-insertion (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _ (a .id-tlh) (a .id-σ) (a .id-τ)) >s ≈⟨ lift-sub-from-insertion (a .id-S) (a .id-P) (a .id-bp) (a .id-T) (a .id-lh) (a .id-C) (a .id-y) (a .id-tlh) (a .id-σ) (a .id-τ) ⟩
      < sub-from-insertion (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _ (a .id-tlh) (liftSub (a .id-σ)) (liftSub (a .id-τ)) >s
        ≈⟨ sub-from-insertion-≃ (a .id-S) (a .id-P) (a .id-bp) (a .id-T) (a .id-lh) (a .id-C) (a .id-y) (a .id-tlh) (lift-sub-≃ refl≃s) (lift-sub-≃ refl≃s) ⟩
      < sub-from-insertion (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _ (a .id-tlh) (liftSub (a .id-σ)) (liftSub (a .id-τ)) >s ∎
      where
        open Reasoning sub-setoid
    open Reasoning tm-setoid-≈
    lem : (branching-path-to-var (a .id-S) (a .id-P) _ [ liftSub (a .id-σ) ]tm) ≈tm Coh (tree-to-ctx (a .id-T)) (a .id-C) _ (liftSub (a .id-τ))
    lem = begin
      < branching-path-to-var (a .id-S) (a .id-P) _ [ liftSub (a .id-σ) ]tm >tm ≈⟨ reflexive≈tm (apply-lifted-sub-tm-≃ (branching-path-to-var (a .id-S) (a .id-P) _) (a .id-σ)) ⟩
      < liftTerm (branching-path-to-var (a .id-S) (a .id-P) _ [ a .id-σ ]tm) >tm ≈⟨ eq zero ⟩
      < Coh (tree-to-ctx (a .id-T)) (a .id-C) _ (liftSub (a .id-τ)) >tm ∎
props i .susp-rule a ty eq = begin
  < Coh (suspCtx (tree-to-ctx (a .id-S))) (suspTy (a .id-A)) _
      (suspSub (a .id-σ)) >tm ≈⟨ Ins≈ (susp-tree (a .id-S)) (ty zero) (PExt (a .id-P)) (a .id-bp) (susp-tree (a .id-T)) (ty (suc zero)) lem (a .id-lh) (type-has-linear-height-susp (a .id-T) (a .id-lh) (a .id-tlh)) ⟩
  < Coh (tree-to-ctx (insertion-tree (susp-tree (a .id-S)) (PExt (a .id-P)) (susp-tree (a .id-T)) _))
    (suspTy (a .id-A) [
     exterior-sub (susp-tree (a .id-S)) (PExt (a .id-P)) _
     (susp-tree (a .id-T)) _ (suspTy (a .id-C)) (≤-trans (≤-reflexive (ctx-susp-dim (tree-to-ctx (a .id-T)))) (s≤s (a .id-y))) (type-has-linear-height-susp (a .id-T) (a .id-lh) (a .id-tlh))
     ]ty)
    _
    (sub-from-insertion (susp-tree (a .id-S)) (PExt (a .id-P)) _
     (susp-tree (a .id-T)) _ (suspTy (a .id-C)) _ _ (suspSub (a .id-σ))
     (suspSub (a .id-τ)))
    >tm ≈⟨ reflexive≈tm (Coh≃ refl≃c {!!} {!!}) ⟩
  < Coh
      (suspCtx
       (tree-to-ctx (insertion-tree (a .id-S) (a .id-P) (a .id-T) _)))
      (suspTy
       (a .id-A [
        exterior-sub (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _
        (a .id-tlh)
        ]ty))
      _
      (suspSub
       (sub-from-insertion (a .id-S) (a .id-P) _ (a .id-T) _ (a .id-C) _
        (a .id-tlh) (a .id-σ) (a .id-τ))) >tm ∎
  where
    open Reasoning tm-setoid-≈

    lem : (branching-path-to-var (susp-tree (a .id-S)) (PExt (a .id-P)) _ [
             suspSub (a .id-σ) ]tm)
            ≈tm
            Coh (tree-to-ctx (susp-tree (a .id-T))) (suspTy (a .id-C)) _
            (suspSub (a .id-τ))
    lem = begin
      < suspTm (branching-path-to-var (a .id-S) (a .id-P) _) [ idSub (suspCtx (tree-to-ctx (a .id-S))) ]tm [ suspSub (a .id-σ) ]tm >tm
        ≈⟨ reflexive≈tm (sub-action-≃-tm (id-on-tm (suspTm (branching-path-to-var (a .id-S) (a .id-P) _))) refl≃s) ⟩
      < suspTm (branching-path-to-var (a .id-S) (a .id-P) _) [ suspSub (a .id-σ) ]tm >tm ≈⟨ reflexive≈tm (sym≃tm (susp-functorial-tm (a .id-σ) (branching-path-to-var (a .id-S) (a .id-P) (a .id-bp)))) ⟩
      < suspTm (branching-path-to-var (a .id-S) (a .id-P) _ [ a .id-σ ]tm) >tm ≈⟨ eq zero ⟩
      < Coh (tree-to-ctx (susp-tree (a .id-T))) (suspTy (a .id-C)) _ (suspSub (a .id-τ)) >tm ∎
