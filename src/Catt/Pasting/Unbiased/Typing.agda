{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ; fromℕ)

module Catt.Pasting.Unbiased.Typing (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing index rule
open import Catt.Typing.Properties index rule props
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting.Unbiased
open import Catt.Pasting.Unbiased.Properties
open import Data.Nat.Properties
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Relation.Nullary
open import Catt.Discs
open import Data.Bool using (Bool; true; false)
open import Catt.Connection
open import Catt.Connection.Typing index rule props
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Typing index rule props
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤; tt)
open import Data.Empty

-- unbiased-term-Ty : (pd : Γ ⊢pd₀ d) → Typing-Tm Γ (unbiased-term pd) (unbiased-type pd)
-- unbiased-term-Ty {Γ = Γ , A} pd with pd-is-linear-dec pd
-- ... | yes p = TyVarZ (reflexive≈ty (sym≃ty (unbiased-type-linear pd ⦃ p ⦄)))
-- ... | no p = {!!}

-- unbiased-type-Ty : (pd : Γ ⊢pd₀ d) → Typing-Ty Γ (unbiased-type pd)
-- unbiased-type-Ty {d = zero} pd = TyStar
-- unbiased-type-Ty {d = suc d} pd = TyArr (apply-sub-tm-typing {!!} {!!}) {!!} {!!}

fst-var-Ty : (Γ : Ctx (suc n)) → Typing-Tm Γ (Var (fromℕ _)) ⋆
fst-var-Ty (∅ , A) = TyVarZ (reflexive≈ty (lift-ty-≃ (⋆-is-only-ty-in-empty-context A)))
fst-var-Ty (Γ , B , A) = lift-tm-typing (fst-var-Ty (Γ , B))

tree-last-var-Ty : (T : Tree n) → Typing-Tm (tree-to-ctx T) (tree-last-var T) ⋆
tree-last-var-Ty Sing = TyVarZ refl≈ty
tree-last-var-Ty (Join S T) = apply-sub-tm-typing (tree-last-var-Ty T) (connect-pd-inc-right-Ty (susp-pd (tree-to-pd S)) (tree-to-ctx T))

tree-inc-Ty : (d : ℕ) → (T : Tree n) → (b : Bool) → Typing-Sub (tree-to-ctx (tree-bd d T)) (tree-to-ctx T) (tree-inc d T b)
tree-inc-Ty zero T false = TyExt TyNull (fst-var-Ty (tree-to-ctx T))
tree-inc-Ty zero T true = TyExt TyNull (tree-last-var-Ty T)
tree-inc-Ty (suc d) Sing b = id-Ty
tree-inc-Ty (suc d) (Join S T) b = sub-between-connect-pds-Ty (susp-pd (tree-to-pd (tree-bd d S))) (susp-pd (tree-to-pd S)) (suspSubTy (tree-inc-Ty d S b)) (tree-inc-Ty (suc d) T b) (reflexive≈tm (suspSub-preserve-focus-tm (tree-to-pd (tree-bd d S)) (tree-to-pd S) (tree-inc d S b))) (reflexive≈tm (tree-inc-preserve-fst-var d T b))

unbiased-type-tree-inc-lem : (d : ℕ) → (T : Tree n) → unbiased-type-tree d (tree-bd d T) [ tree-inc d T true ]ty ≃ty unbiased-type-tree d (tree-bd d T) [ tree-inc d T false ]ty
unbiased-type-tree-inc-lem zero T = refl≃ty
unbiased-type-tree-inc-lem (suc d) T = Arr≃ (l1 (unbiased-term-tree d (tree-bd d (tree-bd (suc d) T))) false) (l2 (unbiased-type-tree d (tree-bd d (tree-bd (suc d) T)))) (l1 (unbiased-term-tree d (tree-bd d (tree-bd (suc d) T))) true)
  where
    l1 : (t : Tm (suc (tree-bd-len d (tree-bd (suc d) T)))) → (b : Bool) →
         t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T true ]tm
           ≃tm
         t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T false ]tm
    l1 t b = begin
      < t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T true ]tm >tm
        ≈˘⟨ assoc-tm (tree-inc (suc d) T true) (tree-inc d (tree-bd (suc d) T) b) t ⟩
      < t [ tree-inc (suc d) T true ∘ tree-inc d (tree-bd (suc d) T) b ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = t}) (tree-inc-glob-step d T true b) ⟩
      < t [ tree-inc (suc d) T false ∘ tree-inc d (tree-bd (suc d) T) b ]tm >tm
        ≈⟨ assoc-tm (tree-inc (suc d) T false) (tree-inc d (tree-bd (suc d) T) b) t ⟩
      < t [ tree-inc d (tree-bd (suc d) T) b ]tm [ tree-inc (suc d) T false ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : (A : Ty (suc (tree-bd-len d (tree-bd (suc d) T))) d)
       → A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T true ]ty
       ≃ty A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T false ]ty
    l2 A = begin
      < A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T true ]ty >ty
        ≈˘⟨ assoc-ty (tree-inc (suc d) T true) (tree-inc d (tree-bd (suc d) T) false) A ⟩
      < A [ tree-inc (suc d) T true ∘ tree-inc d (tree-bd (suc d) T) false ]ty >ty
        ≈⟨ sub-action-≃-ty (refl≃ty {A = A}) (tree-inc-glob-step d T true false) ⟩
      < A [ tree-inc (suc d) T false ∘ tree-inc d (tree-bd (suc d) T) false ]ty >ty
        ≈⟨ assoc-ty (tree-inc (suc d) T false) (tree-inc d (tree-bd (suc d) T) false) A ⟩
      < A [ tree-inc d (tree-bd (suc d) T) false ]ty [ tree-inc (suc d) T false ]ty >ty ∎
      where
        open Reasoning ty-setoid

join-tree-has-non-zero-dim : (S : Tree n) → (T : Tree m) → ¬ (zero ≡ tree-dim (Join S T))
join-tree-has-non-zero-dim S T p with ≤-trans (m≤m⊔n (suc (tree-dim S)) (tree-dim T)) (≤-reflexive (sym p))
... | ()

tree-inc-susp-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → suspSub (tree-inc d T b) ≃s tree-inc (suc d) (susp-tree T) b
tree-inc-susp-lem zero T false = sym≃s (id-left-unit ⟨ ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩ , suspTm (Var (fromℕ _)) ⟩)
tree-inc-susp-lem zero T true = sym≃s (id-left-unit ⟨ ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩ , suspTm (tree-last-var T) ⟩)
tree-inc-susp-lem (suc d) Sing b = refl≃s
tree-inc-susp-lem (suc d) (Join S T) b = sym≃s (id-left-unit _)

unbiased-term-tree-susp-lem : (d : ℕ) → (T : Tree n) → suspTm (unbiased-term-tree d T) ≃tm unbiased-term-tree (suc d) (susp-tree T)
unbiased-type-tree-susp-lem : (d : ℕ) → (T : Tree n) → suspTy (unbiased-type-tree d T) ≃ty unbiased-type-tree (suc d) (susp-tree T)

unbiased-term-tree-susp-lem d T with is-linear-dec T
... | yes p = refl≃tm
... | no p = Coh≃ refl≃c (unbiased-type-tree-susp-lem d T) (susp-functorial-id (suc _))

unbiased-type-tree-susp-lem zero T = Arr≃ refl≃tm refl≃ty (sym≃tm (susp-pd-focus-tm-is-getSnd (tree-to-pd T)))
unbiased-type-tree-susp-lem (suc d) T = Arr≃ (l1 false) l2 (l1 true)
  where
    l1 : (b : Bool)
       → suspTm (unbiased-term-tree d (tree-bd d T) [ tree-inc d T b ]tm)
           ≃tm
         unbiased-term-tree (suc d) (tree-bd (suc d) (susp-tree T))
           [ tree-inc (suc d) (susp-tree T) b ]tm
    l1 b = begin
      < suspTm (unbiased-term-tree d (tree-bd d T) [ tree-inc d T b ]tm) >tm
        ≈⟨ susp-functorial-tm (tree-inc d T b) (unbiased-term-tree d (tree-bd d T)) ⟩
      < suspTm (unbiased-term-tree d (tree-bd d T))
          [ suspSub (tree-inc d T b) ]tm >tm
        ≈⟨ sub-action-≃-tm (unbiased-term-tree-susp-lem d (tree-bd d T)) (tree-inc-susp-lem d T b) ⟩
      < unbiased-term-tree (suc d) (tree-bd (suc d) (susp-tree T))
          [ tree-inc (suc d) (susp-tree T) b ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : suspTy
           (unbiased-type-tree d (tree-bd d T) [ tree-inc d T false ]ty)
           ≃ty
           (unbiased-type-tree (suc d) (tree-bd (suc d) (susp-tree T)) [
            tree-inc (suc d) (susp-tree T) false ]ty)
    l2 = begin
      < suspTy (unbiased-type-tree d (tree-bd d T) [ tree-inc d T false ]ty) >ty
        ≈⟨ susp-functorial-ty (tree-inc d T false) (unbiased-type-tree d (tree-bd d T)) ⟩
      < suspTy (unbiased-type-tree d (tree-bd d T))
          [ suspSub (tree-inc d T false) ]ty >ty
        ≈⟨ sub-action-≃-ty (unbiased-type-tree-susp-lem d (tree-bd d T)) (tree-inc-susp-lem d T false) ⟩
      < unbiased-type-tree (suc d) (tree-bd (suc d) (susp-tree T))
          [ tree-inc (suc d) (susp-tree T) false ]ty >ty ∎
      where
        open Reasoning ty-setoid

linear-tree-unbiased-lem : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → .(tree-dim T ≡ d) → tree-to-ctx T ‼ zero ≃ty unbiased-type-tree d T
linear-tree-unbiased-lem zero Sing p = refl≃ty
linear-tree-unbiased-lem zero (Join S T) p with .(join-tree-has-non-zero-dim S T (sym p))
... | ()
linear-tree-unbiased-lem (suc d) (Join S Sing) p = begin
  < suspCtx (tree-to-ctx S) ‼ zero >ty
    ≈⟨ susp-‼ (tree-to-ctx S) zero ⟩
  < suspTy (tree-to-ctx S ‼ zero) >ty
    ≈⟨ susp-ty-≃ (linear-tree-unbiased-lem d S (cong pred p)) ⟩
  < suspTy (unbiased-type-tree d S) >ty
    ≈⟨ unbiased-type-tree-susp-lem d S ⟩
  < unbiased-type-tree (suc d) (Join S Sing) >ty ∎
  where
    open Reasoning ty-setoid

unbiased-term-tree-Ty : (d : ℕ) → (T : Tree n) → .(tree-dim T ≡ d) → Typing-Tm (tree-to-ctx T) (unbiased-term-tree d T) (unbiased-type-tree d T)
unbiased-comp-Ty : (d : ℕ) → .⦃ NonZero′ d ⦄ → (T : Tree n) → .(d ≤ tree-dim T) → Typing-Sub (tree-to-ctx T) Γ σ
                 → Typing-Tm Γ (Coh (tree-to-ctx T) (unbiased-type-tree d T) σ) (unbiased-type-tree d T [ σ ]ty)
unbiased-type-tree-Ty : (d : ℕ) → (T : Tree n) → .(d ≤ tree-dim T) → Typing-Ty (tree-to-ctx T) (unbiased-type-tree d T)

unbiased-comp-Ty (suc d) T q σty = TyComp (tree-to-pd T) ⦃ {!!} ⦄ (unbiased-type-tree-Ty (suc d) T q) σty {!!} {!!} refl≈ty

unbiased-term-tree-Ty d T q with is-linear-dec T
... | yes p = TyVarZ (reflexive≈ty (linear-tree-unbiased-lem d T ⦃ p ⦄ q))
... | no p = term-conversion (unbiased-comp-Ty d ⦃ NonZero′-subst q (non-linear-has-no-zero-dim T p) ⦄ T (≤-reflexive (sym q)) id-Ty) (reflexive≈ty (id-on-ty (unbiased-type-tree d T)))
  where
    non-linear-has-no-zero-dim : (T : Tree n) → ¬ is-linear T → NonZero′ (tree-dim T)
    non-linear-has-no-zero-dim Sing p = ⊥-elim (p tt)
    non-linear-has-no-zero-dim (Join S T) p with tree-dim (Join S T) | join-tree-has-non-zero-dim S T
    ... | zero | q = ⊥-elim (q refl)
    ... | suc d | q = it

    NonZero′-subst : n ≡ m → NonZero′ n → NonZero′ m
    NonZero′-subst refl x = x

unbiased-type-tree-Ty zero T q = TyStar
unbiased-type-tree-Ty (suc d) T q = TyArr (apply-sub-tm-typing (unbiased-term-tree-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))) (tree-inc-Ty d T false)) (apply-sub-ty-typing (unbiased-type-tree-Ty d (tree-bd d T) (≤-reflexive (sym (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))))) (tree-inc-Ty d T false)) (term-conversion (apply-sub-tm-typing (unbiased-term-tree-Ty d (tree-bd d T) (tree-dim-bd′ d T (≤-trans (n≤1+n d) q))) (tree-inc-Ty d T true)) (reflexive≈ty (unbiased-type-tree-inc-lem d T)))
