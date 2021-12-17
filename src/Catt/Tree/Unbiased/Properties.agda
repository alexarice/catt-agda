{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased.Properties where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Data.Nat
open import Data.Bool using (Bool; true; false)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Fin using (Fin; zero; suc; fromℕ)
open import Catt.Discs
open import Catt.Discs.Properties
open import Data.Nat.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Data.Empty
open import Catt.Globular
open import Catt.Globular.Properties

-- unbiased-type-inc-lem : (d : ℕ) → (T : Tree n) → unbiased-type d (tree-bd d T) [ tree-inc d T true ]ty ≃ty unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty
-- unbiased-type-inc-lem zero T = refl≃ty
-- unbiased-type-inc-lem (suc d) T = Arr≃ (l1 (unbiased-term d (tree-bd d (tree-bd (suc d) T))) false) (l2 (unbiased-type d (tree-bd d (tree-bd (suc d) T)))) (l1 (unbiased-term d (tree-bd d (tree-bd (suc d) T))) true)
--   where
--     l1 : (t : Tm (suc (tree-bd-len d (tree-bd (suc d) T)))) → (b : Bool) →
--          t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T true ]tm
--            ≃tm
--          t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T false ]tm
--     l1 t b = begin
--       < t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T true ]tm >tm
--         ≈˘⟨ assoc-tm (tree-inc (suc d) T true) (tree-inc d (tree-bd (suc d) T) b) t ⟩
--       < t [ tree-inc (suc d) T true ∘ tree-inc d (tree-bd (suc d) T) b ]tm >tm
--         ≈⟨ sub-action-≃-tm (refl≃tm {s = t}) (tree-inc-glob-step d T true b) ⟩
--       < t [ tree-inc (suc d) T false ∘ tree-inc d (tree-bd (suc d) T) b ]tm >tm
--         ≈⟨ assoc-tm (tree-inc (suc d) T false) (tree-inc d (tree-bd (suc d) T) b) t ⟩
--       < t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T false ]tm >tm ∎
--       where
--         open Reasoning tm-setoid

--     l2 : (A : Ty (suc (tree-bd-len d (tree-bd (suc d) T))))
--        → A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T true ]ty
--        ≃ty A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T false ]ty
--     l2 A = begin
--       < A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T true ]ty >ty
--         ≈˘⟨ assoc-ty (tree-inc (suc d) T true) (tree-inc d (tree-bd (suc d) T) false) A ⟩
--       < A [ tree-inc (suc d) T true ∘ tree-inc d (tree-bd (suc d) T) false ]ty >ty
--         ≈⟨ sub-action-≃-ty (refl≃ty {A = A}) (tree-inc-glob-step d T true false) ⟩
--       < A [ tree-inc (suc d) T false ∘ tree-inc d (tree-bd (suc d) T) false ]ty >ty
--         ≈⟨ assoc-ty (tree-inc (suc d) T false) (tree-inc d (tree-bd (suc d) T) false) A ⟩
--       < A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T false ]ty >ty ∎
--       where
--         open Reasoning ty-setoid

-- unbiased-term-susp-lem : (d : ℕ) → (T : Tree n) → suspTm (unbiased-term d T) ≃tm unbiased-term (suc d) (suspTree T)
-- unbiased-type-susp-lem : (d : ℕ) → (T : Tree n) → suspTy (unbiased-type d T) ≃ty unbiased-type (suc d) (suspTree T)

-- unbiased-term-susp-lem d T with is-linear-dec T
-- ... | yes p = refl≃tm
-- ... | no p = Coh≃ refl≃ (unbiased-type-susp-lem d T) (susp-functorial-id (suc _))

-- unbiased-type-susp-lem zero T = refl≃ty
-- unbiased-type-susp-lem (suc d) T = Arr≃ (l1 false) l2 (l1 true)
--   where
--     l1 : (b : Bool)
--        → suspTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
--            ≃tm
--          unbiased-term (suc d) (tree-bd (suc d) (suspTree T))
--            [ tree-inc (suc d) (suspTree T) b ]tm
--     l1 b = begin
--       < suspTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm) >tm
--         ≈⟨ susp-functorial-tm (tree-inc d T b) (unbiased-term d (tree-bd d T)) ⟩
--       < suspTm (unbiased-term d (tree-bd d T))
--           [ suspSub (tree-inc d T b) ]tm >tm
--         ≈⟨ sub-action-≃-tm (unbiased-term-susp-lem d (tree-bd d T)) (tree-inc-susp-lem d T b) ⟩
--       < unbiased-term (suc d) (tree-bd (suc d) (suspTree T))
--           [ tree-inc (suc d) (suspTree T) b ]tm >tm ∎
--       where
--         open Reasoning tm-setoid

--     l2 : suspTy
--            (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty)
--            ≃ty
--            (unbiased-type (suc d) (tree-bd (suc d) (suspTree T)) [
--             tree-inc (suc d) (suspTree T) false ]ty)
--     l2 = begin
--       < suspTy (unbiased-type d (tree-bd d T) [ tree-inc d T false ]ty) >ty
--         ≈⟨ susp-functorial-ty (tree-inc d T false) (unbiased-type d (tree-bd d T)) ⟩
--       < suspTy (unbiased-type d (tree-bd d T))
--           [ suspSub (tree-inc d T false) ]ty >ty
--         ≈⟨ sub-action-≃-ty (unbiased-type-susp-lem d (tree-bd d T)) (tree-inc-susp-lem d T false) ⟩
--       < unbiased-type (suc d) (tree-bd (suc d) (suspTree T))
--           [ tree-inc (suc d) (suspTree T) false ]ty >ty ∎
--       where
--         open Reasoning ty-setoid

-- linear-tree-unbiased-lem : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → .(tree-dim T ≡ d) → tree-to-ctx T ‼ zero ≃ty unbiased-type d T
-- linear-tree-unbiased-lem zero Sing p = refl≃ty
-- linear-tree-unbiased-lem zero (Join S T) p with .(join-tree-has-non-zero-dim S T (sym p))
-- ... | ()
-- linear-tree-unbiased-lem (suc d) (Join S Sing) p = begin
--   < suspCtx (tree-to-ctx S) ‼ zero >ty
--     ≈⟨ susp-‼ (tree-to-ctx S) zero ⟩
--   < suspTy (tree-to-ctx S ‼ zero) >ty
--     ≈⟨ susp-ty-≃ (linear-tree-unbiased-lem d S (cong pred p)) ⟩
--   < suspTy (unbiased-type d S) >ty
--     ≈⟨ unbiased-type-susp-lem d S ⟩
--   < unbiased-type (suc d) (Join S Sing) >ty ∎
--   where
--     open Reasoning ty-setoid

-- unbiased-type-sphere-lem : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ suc d)
--                          → Var (fromℕ _)
--                            [ sub-from-sphere-unbiased (suc d) T ]tm
--                            ≃tm Var (fromℕ (tree-size T))
-- unbiased-type-sphere-lem zero T p = refl≃tm
-- unbiased-type-sphere-lem (suc d) T p = begin
--   < Var (fromℕ _)
--       [ sub-from-sphere-unbiased (suc (suc d)) T ]tm >tm ≡⟨⟩
--   < Var (fromℕ _)
--       [ sub-from-sphere (suc d) (unbiased-type (suc d) (tree-bd (suc d) T) [ tree-inc (suc d) T false ]ty) (trans (sym (sub-dim (tree-inc (suc d) T false) (unbiased-type (suc d) (tree-bd (suc d) T)))) (unbiased-type-dim (suc d) (tree-bd (suc d) T))) ]tm >tm
--     ≈⟨ sub-action-≃-tm (refl≃tm {s = Var (fromℕ _)}) (sphere-to-subbed-ty (suc d) (unbiased-type (suc d) (tree-bd (suc d) T)) (unbiased-type-dim (suc d) (tree-bd (suc d) T)) (tree-inc (suc d) T false)) ⟩ --(sphere-to-subbed-ty (unbiased-type (suc d) (tree-bd (suc d) T)) (tree-inc (suc d) T false))
--   < Var (fromℕ _)
--     [ tree-inc (suc d) T false ∘ sub-from-sphere-unbiased (suc d) (tree-bd (suc d) T) ]tm >tm
--     ≈⟨ assoc-tm (tree-inc (suc d) T false) (sub-from-sphere-unbiased (suc d) (tree-bd (suc d) T)) (Var (fromℕ _)) ⟩
--   < Var (fromℕ _)
--     [ sub-from-sphere-unbiased (suc d) (tree-bd (suc d) T) ]tm
--     [ tree-inc (suc d) T false ]tm >tm
--     ≈⟨ sub-action-≃-tm (unbiased-type-sphere-lem d (tree-bd (suc d) T) (tree-dim-bd′ (suc d) T (≤-trans (n≤1+n (suc d)) (≤-reflexive (sym p))))) refl≃s ⟩
--   < Var (fromℕ (tree-size (tree-bd (suc d) T)))
--     [ tree-inc (suc d) T false ]tm >tm
--     ≈⟨ tree-inc-preserve-fst-var d T false ⟩
--   < Var (fromℕ (tree-size T)) >tm ∎
--   where
--     open Reasoning tm-setoid

-- unbiased-type-disc-lem : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ d)
--                        → .⦃ NonZero′ d ⦄
--                        → Var (fromℕ _)
--                          [ sub-from-disc-unbiased d T ]tm
--                          ≃tm Var (fromℕ (tree-size T))
-- unbiased-type-disc-lem (suc zero) T p = refl≃tm -- id-on-tm (Var (fromℕ (tree-size T)))
-- unbiased-type-disc-lem (suc (suc d)) T p = begin
--   < Var (fromℕ _)
--     [ sub-from-disc-unbiased (suc (suc d)) T ]tm >tm
--     ≡⟨⟩
--   < Var (fromℕ _)
--       [ sub-from-sphere-unbiased (suc (suc d)) T ]tm >tm
--     ≈⟨ unbiased-type-sphere-lem (suc d) T p ⟩
--   < Var (fromℕ (tree-size T)) >tm ∎
--   where
--     open Reasoning tm-setoid

-- unbiased-type-sphere-lem-2 : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ suc d)
--                            → getSnd
--                              [ sub-from-sphere-unbiased (suc d) T ]tm
--                              ≃tm tree-last-var T
-- unbiased-type-sphere-lem-2 zero T p = refl≃tm
-- unbiased-type-sphere-lem-2 (suc d) T p = begin
--   < getSnd [ sub-from-sphere-unbiased (suc (suc d)) T ]tm >tm
--     ≡⟨⟩
--   < getSnd [ sub-from-sphere (suc d) (unbiased-type (suc d) (tree-bd (suc d) T) [ tree-inc (suc d) T false ]ty) (trans (sym (sub-dim (tree-inc (suc d) T false) (unbiased-type (suc d) (tree-bd (suc d) T)))) (unbiased-type-dim (suc d) (tree-bd (suc d) T))) ]tm >tm
--     ≈⟨ sub-action-≃-tm (refl≃tm {s = getSnd}) (sphere-to-subbed-ty (suc d) (unbiased-type (suc d) (tree-bd (suc d) T)) (unbiased-type-dim (suc d) (tree-bd (suc d) T)) (tree-inc (suc d) T false)) ⟩
--   < getSnd [ tree-inc (suc d) T false ∘ sub-from-sphere-unbiased (suc d) (tree-bd (suc d) T) ]tm >tm
--     ≈⟨ assoc-tm (tree-inc (suc d) T false) (sub-from-sphere-unbiased (suc d) (tree-bd (suc d) T)) getSnd ⟩
--   < getSnd [ sub-from-sphere-unbiased (suc d) (tree-bd (suc d) T) ]tm
--            [ tree-inc (suc d) T false ]tm >tm
--     ≈⟨ sub-action-≃-tm (unbiased-type-sphere-lem-2 d (tree-bd (suc d) T) (tree-dim-bd′ (suc d) T (≤-trans (n≤1+n (suc d)) (≤-reflexive (sym p))))) refl≃s ⟩
--   < tree-last-var (tree-bd (suc d) T) [ tree-inc (suc d) T false ]tm >tm
--     ≈⟨ tree-inc-preserve-last-var d T false ⟩
--   < tree-last-var T >tm ∎
--   where
--     open Reasoning tm-setoid

-- unbiased-type-disc-lem-2 : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ suc d)
--                          → getSnd
--                            [ sub-from-disc-unbiased (suc d) T ]tm
--                            ≃tm tree-last-var T
-- unbiased-type-disc-lem-2 d T p = begin
--   < getSnd
--     [ sub-from-disc-unbiased (suc d) T ]tm >tm
--     ≡⟨⟩
--   < getSnd
--       [ sub-from-sphere-unbiased (suc d) T ]tm >tm
--     ≈⟨ unbiased-type-sphere-lem-2 d T p ⟩
--   < tree-last-var T >tm ∎
--   where
--     open Reasoning tm-setoid

unbiased-type-≃ : d ≡ d′ → (S ≃ T) → unbiased-type d S ≃ty unbiased-type d′ T
unbiased-type-≃ refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃ty

unbiased-comp-≃ : d ≡ d′ → (S ≃ T) → unbiased-comp d S ≃tm unbiased-comp d′ T
unbiased-comp-≃ p q with ≃-to-same-n q
... | refl = Coh≃ q (unbiased-type-≃ p q) refl≃s

unbiased-type-truncate-1 : (d : ℕ) → (T : Tree n) → truncate 1 (unbiased-type (suc d) T) ≃ty Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T
unbiased-type-truncate-1 zero T = refl≃ty
unbiased-type-truncate-1 (suc d) T = begin
  < truncate 1
      ((unbiased-term (suc d) (tree-bd (suc d) T) [ tree-inc (suc d) T false ]tm)
        ─⟨ unbiased-type (suc d) T ⟩⟶
       (unbiased-term (suc d) (tree-bd (suc d) T) [ tree-inc (suc d) T true ]tm))>ty
    ≈⟨ truncate-≤ {s = unbiased-term (suc d) (tree-bd (suc d) T) [ tree-inc (suc d) T false ]tm} {t = unbiased-term (suc d) (tree-bd (suc d) T) [ tree-inc (suc d) T true ]tm} 1 (unbiased-type (suc d) T) (s≤s z≤n) ⟩
  < truncate 1 (unbiased-type (suc d) T) >ty
    ≈⟨ unbiased-type-truncate-1 d T ⟩
  < Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T >ty ∎
  where
    open Reasoning ty-setoid

unbiased-type-truncate-1′ : (d : ℕ) → .⦃ NonZero′ d ⦄ → (T : Tree n) → truncate 1 (unbiased-type d T) ≃ty Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T
unbiased-type-truncate-1′ (suc d) = unbiased-type-truncate-1 d

unbiased-term-≃ : (d ≡ d′) → S ≃ T → unbiased-term d S ≃tm unbiased-term d′ T
unbiased-term-≃ refl p with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = refl≃tm

unbiased-type-prop : (d : ℕ) → (T : Tree n) → (d′ : ℕ) → (d ≤ d′) → (b : Bool) → unbiased-type d T ≃ty unbiased-type d (tree-bd d′ T) [ tree-inc d′ T b ]ty
unbiased-type-prop zero T d′ p b = refl≃ty
unbiased-type-prop (suc d) T d′ p b = Arr≃ (lem false) (unbiased-type-prop d T d′ (≤-trans (n≤1+n d) p) b) (lem true)
  where
    lem : (b′ : Bool) → (unbiased-term d (tree-bd d T) [ tree-inc d T b′ ]tm) ≃tm
      ((unbiased-term d (tree-bd d (tree-bd d′ T)) [
        tree-inc d (tree-bd d′ T) b′ ]tm)
       [ tree-inc d′ T b ]tm)
    lem b′ = begin
      < unbiased-term d (tree-bd d T) [ tree-inc d T b′ ]tm >tm
        ≈˘⟨ sub-action-≃-tm (unbiased-term-≃ refl (tree-bd-glob d d′ T p)) (tree-inc-glob d d′ T b′ b p) ⟩
      < unbiased-term d (tree-bd d (tree-bd d′ T))
        [ tree-inc d′ T b ∘ tree-inc d (tree-bd d′ T) b′ ]tm >tm
        ≈⟨ assoc-tm _ _ (unbiased-term d (tree-bd d (tree-bd d′ T))) ⟩
      < unbiased-term d (tree-bd d (tree-bd d′ T))
        [ tree-inc d (tree-bd d′ T) b′ ]tm
        [ tree-inc d′ T b ]tm >tm ∎
      where
        open Reasoning tm-setoid

unbiased-term-susp-lem : (d : ℕ) → (T : Tree n) → suspTm (unbiased-term d T) ≃tm unbiased-term (suc d) (suspTree T)
unbiased-type-susp-lem : (d : ℕ) → (T : Tree n) → suspTy (unbiased-type d T) ≃ty unbiased-type (suc d) (suspTree T)
unbiased-comp-susp-lem : (d : ℕ) → (T : Tree n) → suspTm (unbiased-comp d T) ≃tm unbiased-comp (suc d) (suspTree T)

unbiased-term-susp-lem d T with is-linear-dec T
... | yes p = refl≃tm
... | no p = unbiased-comp-susp-lem d T

unbiased-type-susp-lem zero T = refl≃ty
unbiased-type-susp-lem (suc d) T = Arr≃ (l1 false) (unbiased-type-susp-lem d T) (l1 true)
  where
    l1 : (b : Bool)
       → suspTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
           ≃tm
         unbiased-term (suc d) (tree-bd (suc d) (suspTree T))
           [ tree-inc (suc d) (suspTree T) b ]tm
    l1 b = begin
      < suspTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm) >tm
        ≈⟨ susp-functorial-tm (tree-inc d T b) (unbiased-term d (tree-bd d T)) ⟩
      < suspTm (unbiased-term d (tree-bd d T))
          [ suspSub (tree-inc d T b) ]tm >tm
        ≈⟨ sub-action-≃-tm (unbiased-term-susp-lem d (tree-bd d T)) (tree-inc-susp-lem d T b) ⟩
      < unbiased-term (suc d) (tree-bd (suc d) (suspTree T))
          [ tree-inc (suc d) (suspTree T) b ]tm >tm ∎
      where
        open Reasoning tm-setoid

unbiased-comp-susp-lem d T = Coh≃ refl≃ (unbiased-type-susp-lem d T) susp-functorial-id

linear-tree-unbiased-lem : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → .(tree-dim T ≡ d) → tree-to-ctx T ‼ zero ≃ty unbiased-type d T
linear-tree-unbiased-lem zero Sing p = Star≃ refl
linear-tree-unbiased-lem zero (Join S T) p = ⊥-elim (join-tree-has-non-zero-dim S T (sym (recompute ((tree-dim (Join S T)) ≟ zero) p)))
linear-tree-unbiased-lem (suc d) (Join S Sing) p = begin
  < suspCtx (tree-to-ctx S) ‼ zero >ty
    ≈⟨ susp-‼ (tree-to-ctx S) zero ⟩
  < suspTy (tree-to-ctx S ‼ zero) >ty
    ≈⟨ susp-ty-≃ (linear-tree-unbiased-lem d S (cong pred p)) ⟩
  < suspTy (unbiased-type d S) >ty
    ≈⟨ unbiased-type-susp-lem d S ⟩
  < unbiased-type (suc d) (Join S Sing) >ty ∎
  where
    open Reasoning ty-setoid

sub-from-linear-tree-unbiased-0V : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → 0V [ sub-from-linear-tree-unbiased S T d ]tm ≃tm unbiased-comp (d + tree-dim S) T
sub-from-linear-tree-unbiased-0V Sing T d = unbiased-comp-≃ (sym (+-identityʳ d)) refl≃
sub-from-linear-tree-unbiased-0V (Join S Sing) T d = trans≃tm (sym≃tm (unrestrict-comp-tm 0V (sub-from-linear-tree-unbiased S T (suc d)))) (trans≃tm (sub-from-linear-tree-unbiased-0V S T (suc d)) (unbiased-comp-≃ (sym (+-suc d (tree-dim S))) refl≃))

sub-from-linear-tree-0V : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (t : Tm m) → (A : Ty m) → (p : ty-dim A ≡ tree-dim S) → 0V [ sub-from-linear-tree S t A p ]tm ≃tm t
sub-from-linear-tree-0V Sing t A p = refl≃tm
sub-from-linear-tree-0V (Join S Sing) t (s ─⟨ A ⟩⟶ s′) p = refl≃tm

sub-from-linear-tree-‼-0 : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (t : Tm m) → (A : Ty m) → (p : ty-dim A ≡ tree-dim S) → tree-to-ctx S ‼ zero [ sub-from-linear-tree S t A p ]ty ≃ty A
sub-from-linear-tree-‼-0 Sing t ⋆ p = refl≃ty
sub-from-linear-tree-‼-0 (Join S Sing) t (s ─⟨ A ⟩⟶ s′) p = begin
  < suspCtx (tree-to-ctx S) ‼ zero [ ⟨ ⟨ sub-from-linear-tree S s A (cong pred p) , s′ ⟩ , t ⟩ ]ty >ty
    ≈⟨ sub-action-≃-ty (‼-≃ zero zero refl (susp-lin-tree S)) refl≃s ⟩
  < ((0V [ sub-from-linear-tree S s A (cong pred p) ]tm)
    ─⟨ liftType (liftType (tree-to-ctx S ‼ zero))
       [ ⟨ ⟨ sub-from-linear-tree S s A (cong pred p) , s′ ⟩ , t ⟩ ]ty
       ⟩⟶ s′) >ty
    ≈⟨ Arr≃ (sub-from-linear-tree-0V S s A (cong pred p)) lem refl≃tm ⟩
  < s ─⟨ A ⟩⟶ s′ >ty ∎
  where
    open Reasoning ty-setoid

    lem : liftType (liftType (tree-to-ctx S ‼ zero))
            [ ⟨ ⟨ sub-from-linear-tree S s A (cong pred p) , s′ ⟩ , t ⟩ ]ty
            ≃ty A
    lem = begin
      < liftType (liftType (tree-to-ctx S ‼ zero))
        [ ⟨ ⟨ sub-from-linear-tree S s A _ , s′ ⟩ , t ⟩ ]ty >ty
        ≈⟨ lift-sub-comp-lem-ty ⟨ sub-from-linear-tree S s A _ , s′ ⟩ (liftType (tree-to-ctx S ‼ zero)) ⟩
      < liftType (tree-to-ctx S ‼ zero) [ ⟨ sub-from-linear-tree S s A _ , s′ ⟩ ]ty >ty
        ≈⟨ lift-sub-comp-lem-ty (sub-from-linear-tree S s A _) (tree-to-ctx S ‼ zero) ⟩
      < tree-to-ctx S ‼ zero [ sub-from-linear-tree S s A _ ]ty >ty
        ≈⟨ sub-from-linear-tree-‼-0 S s A (cong pred p) ⟩
      < A >ty ∎

unbiased-term-disk : (n : ℕ) → unbiased-term n (n-disk n) ≃tm 0V {suc (n * 2)}
unbiased-term-disk zero = refl≃tm
unbiased-term-disk (suc n) = trans≃tm (sym≃tm (unbiased-term-susp-lem n (n-disk n))) (susp-tm-≃ (unbiased-term-disk n))

unbiased-type-disk : (n : ℕ) → unbiased-type n (n-disk n) ≃ty (tree-to-ctx (n-disk n)) ‼ zero
unbiased-type-disk zero = refl≃ty
unbiased-type-disk (suc n) = begin
  < unbiased-type (suc n) (n-disk (suc n)) >ty
    ≈˘⟨ unbiased-type-susp-lem n (n-disk n) ⟩
  < suspTy (unbiased-type n (n-disk n)) >ty
    ≈⟨ susp-ty-≃ (unbiased-type-disk n) ⟩
  < suspTy (tree-to-ctx (n-disk n) ‼ zero) >ty
    ≈˘⟨ susp-‼ (tree-to-ctx (n-disk n)) zero ⟩
  < suspCtx (tree-to-ctx (n-disk n)) ‼ zero >ty ∎
  where
    open Reasoning ty-setoid

sub-from-linear-tree-≃ : S ≃ T → .⦃ _ : is-linear S ⦄ → .⦃ _ : is-linear T ⦄ → s ≃tm t → A ≃ty B → (p : ty-dim A ≡ tree-dim S) → (q : ty-dim B ≡ tree-dim T) → sub-from-linear-tree S s A p ≃s sub-from-linear-tree T t B q
sub-from-linear-tree-≃ Sing≃ b (Star≃ x) p q = Ext≃ (Null≃ (Star≃ x)) b
sub-from-linear-tree-≃ (Join≃ a Sing≃) b (Arr≃ c d e) p q = Ext≃ (Ext≃ (sub-from-linear-tree-≃ a c d (cong pred p) (cong pred q)) e) b

sub-from-linear-tree-sub : (a : S ≃ T) → .⦃ _ : is-linear S ⦄ → .⦃ _ : is-linear T ⦄ → (t : Tm m) → (A : Ty m) → (p : ty-dim A ≡ tree-dim S) → (σ : Sub m l ⋆) → σ ∘ sub-from-linear-tree S t A p ≃s sub-from-linear-tree T (t [ σ ]tm) (A [ σ ]ty) (trans (sym (sub-dim σ A)) (trans p (tree-dim-≃ a)))
sub-from-linear-tree-sub Sing≃ t A p σ = refl≃s
sub-from-linear-tree-sub (Join≃ a Sing≃) t (s ─⟨ A ⟩⟶ s′) p σ = Ext≃ (Ext≃ (sub-from-linear-tree-sub a s A (cong pred p) σ) refl≃tm) refl≃tm

identity-sub : (t : Tm n) → (A : Ty n) → (σ : Sub n m ⋆) → identity t A [ σ ]tm ≃tm identity (t [ σ ]tm) (A [ σ ]ty)
identity-sub t A σ = Coh≃ (n-disk-≃ (sub-dim σ A)) (unbiased-type-≃ (cong suc (sub-dim σ A)) (n-disk-≃ (sub-dim σ A))) (sub-from-linear-tree-sub (n-disk-≃ (sub-dim σ A)) ⦃ n-disk-is-linear (ty-dim A) ⦄ ⦃ n-disk-is-linear (ty-dim (A [ σ ]ty)) ⦄ t A (sym (tree-dim-n-disk (ty-dim A))) σ)

identity-≃ : s ≃tm t → A ≃ty B → identity s A ≃tm identity t B
identity-≃ {A = A} {B = B} p q = Coh≃ (n-disk-≃ (ty-dim-≃ q)) (unbiased-type-≃ (cong suc (ty-dim-≃ q)) (n-disk-≃ (ty-dim-≃ q))) (sub-from-linear-tree-≃ (n-disk-≃ (ty-dim-≃ q)) ⦃ n-disk-is-linear (ty-dim A) ⦄ ⦃ n-disk-is-linear (ty-dim B) ⦄ p q (sym (tree-dim-n-disk (ty-dim A))) (sym (tree-dim-n-disk (ty-dim B))))
