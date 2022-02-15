{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Globular
open import Catt.Globular.Properties

unbiased-type-dim : (d : ℕ) → (T : Tree n) → ty-dim (unbiased-type d T) ≡ d
unbiased-type-dim zero T = refl
unbiased-type-dim (suc d) T = cong suc (unbiased-type-dim d T)

unbiased-comp-dim : (d : ℕ) → (T : Tree n) → tm-height (tree-to-ctx T) (unbiased-comp d T) ≡ d
unbiased-comp-dim d T = trans (sym (sub-dim idSub (unbiased-type d T))) (unbiased-type-dim d T)

unbiased-type-≃ : d ≡ d′ → (S ≃ T) → unbiased-type d S ≃ty unbiased-type d′ T
unbiased-type-≃ refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃ty

unbiased-comp-≃ : d ≡ d′ → (S ≃ T) → unbiased-comp d S ≃tm unbiased-comp d′ T
unbiased-comp-≃ p q with ≃-to-same-n q
... | refl = Coh≃ (tree-to-ctx-≃ q) (unbiased-type-≃ p q) refl≃s

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

unbiased-type-truncate-1′ : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → truncate 1 (unbiased-type d T) ≃ty Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T
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

unbiased-comp-susp-lem d T = Coh≃ refl≃c (unbiased-type-susp-lem d T) susp-functorial-id

linear-tree-unbiased-lem : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → .(tree-dim T ≡ d) → tree-to-ctx T ‼ zero ≃ty unbiased-type d T
linear-tree-unbiased-lem zero Sing p = Star≃ refl
linear-tree-unbiased-lem zero (Join S T) ()
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

unbiased-term-disc : (n : ℕ) → unbiased-term n (n-disc n) ≃tm 0V {suc (n * 2)}
unbiased-term-disc zero = refl≃tm
unbiased-term-disc (suc n) = trans≃tm (sym≃tm (unbiased-term-susp-lem n (n-disc n))) (susp-tm-≃ (unbiased-term-disc n))

unbiased-type-disc : (n : ℕ) → unbiased-type n (n-disc n) ≃ty (tree-to-ctx (n-disc n)) ‼ zero
unbiased-type-disc zero = refl≃ty
unbiased-type-disc (suc n) = begin
  < unbiased-type (suc n) (n-disc (suc n)) >ty
    ≈˘⟨ unbiased-type-susp-lem n (n-disc n) ⟩
  < suspTy (unbiased-type n (n-disc n)) >ty
    ≈⟨ susp-ty-≃ (unbiased-type-disc n) ⟩
  < suspTy (tree-to-ctx (n-disc n) ‼ zero) >ty
    ≈˘⟨ susp-‼ (tree-to-ctx (n-disc n)) zero ⟩
  < suspCtx (tree-to-ctx (n-disc n)) ‼ zero >ty ∎
  where
    open Reasoning ty-setoid

sub-from-linear-tree-≃ : S ≃ T → .⦃ _ : is-linear S ⦄ → .⦃ _ : is-linear T ⦄ → s ≃tm t → A ≃ty B → (p : ty-dim A ≡ tree-dim S) → (q : ty-dim B ≡ tree-dim T) → sub-from-linear-tree S s A p ≃s sub-from-linear-tree T t B q
sub-from-linear-tree-≃ Sing≃ b (Star≃ x) p q = Ext≃ (Null≃ (Star≃ x)) b
sub-from-linear-tree-≃ (Join≃ a Sing≃) b (Arr≃ c d e) p q = Ext≃ (Ext≃ (sub-from-linear-tree-≃ a c d (cong pred p) (cong pred q)) e) b

sub-from-linear-tree-sub : (a : S ≃ T) → .⦃ _ : is-linear S ⦄ → .⦃ _ : is-linear T ⦄ → (t : Tm m) → (A : Ty m) → (p : ty-dim A ≡ tree-dim S) → (σ : Sub m l ⋆) → σ ∘ sub-from-linear-tree S t A p ≃s sub-from-linear-tree T (t [ σ ]tm) (A [ σ ]ty) (trans (sym (sub-dim σ A)) (trans p (tree-dim-≃ a)))
sub-from-linear-tree-sub Sing≃ t A p σ = refl≃s
sub-from-linear-tree-sub (Join≃ a Sing≃) t (s ─⟨ A ⟩⟶ s′) p σ = Ext≃ (Ext≃ (sub-from-linear-tree-sub a s A (cong pred p) σ) refl≃tm) refl≃tm

identity-sub : (t : Tm n) → (A : Ty n) → (σ : Sub n m ⋆) → identity t A [ σ ]tm ≃tm identity (t [ σ ]tm) (A [ σ ]ty)
identity-sub t A σ = Coh≃ (tree-to-ctx-≃ (n-disc-≃ (sub-dim σ A))) (unbiased-type-≃ (cong suc (sub-dim σ A)) (n-disc-≃ (sub-dim σ A))) (sub-from-linear-tree-sub (n-disc-≃ (sub-dim σ A)) ⦃ n-disc-is-linear (ty-dim A) ⦄ ⦃ n-disc-is-linear (ty-dim (A [ σ ]ty)) ⦄ t A (sym (tree-dim-n-disc (ty-dim A))) σ)

identity-≃ : s ≃tm t → A ≃ty B → identity s A ≃tm identity t B
identity-≃ {A = A} {B = B} p q = Coh≃ (tree-to-ctx-≃ (n-disc-≃ (ty-dim-≃ q))) (unbiased-type-≃ (cong suc (ty-dim-≃ q)) (n-disc-≃ (ty-dim-≃ q))) (sub-from-linear-tree-≃ (n-disc-≃ (ty-dim-≃ q)) ⦃ n-disc-is-linear (ty-dim A) ⦄ ⦃ n-disc-is-linear (ty-dim B) ⦄ p q (sym (tree-dim-n-disc (ty-dim A))) (sym (tree-dim-n-disc (ty-dim B))))
