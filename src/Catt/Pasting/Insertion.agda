{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Insertion where

open import Catt.Syntax
-- open import Catt.Dimension
open import Data.Nat
open import Data.Nat.Properties
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Catt.Pasting.Properties
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Unsuspension
open import Data.Empty
open import Data.Unit using (⊤;tt)
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Product renaming (_,_ to _,,_)
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ; inject₁)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles
open import Data.Sum
open import Catt.Variables
open import Catt.Globular
open import Catt.Syntax.Properties

data Path : Tree n → Set where
  PHere : (T : Tree n) → Path T
  PExt : {S : Tree m} {T : Tree n} → Path S → Path (Join S T)
  PShift : {S : Tree m} {T : Tree n} → Path T → Path (Join S T)

path-length : {T : Tree n} → Path T → ℕ
path-length (PHere _) = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P

has-linear-height : ℕ → Tree n → Set
has-linear-height zero T = ⊤
has-linear-height (suc n) Sing = ⊥
has-linear-height (suc n) (Join T Sing) = has-linear-height n T
has-linear-height (suc n) (Join T (Join _ _)) = ⊥

insertion-tree-size :  (S : Tree n) → (P : Path S) → (T : Tree m) → .⦃ has-linear-height (path-length P) T ⦄ → ℕ
insertion-tree : (S : Tree n) → (P : Path S) → (T : Tree m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → Tree (insertion-tree-size S P T)

insertion-tree-size {m = m} S (PHere .S) T = m
insertion-tree-size (Join {m = m} S₁ S₂) (PExt P) (Join T Sing) = m + suc (suc (insertion-tree-size S₁ P T))
insertion-tree-size (Join {n = n} S₁ S₂) (PShift P) T = insertion-tree-size S₂ P T + suc (suc n)

insertion-tree S (PHere .S) T = T
insertion-tree (Join S₁ S₂) (PExt P) (Join T Sing) = Join (insertion-tree S₁ P T) S₂
insertion-tree (Join S₁ S₂) (PShift P) T = Join S₁ (insertion-tree S₂ P T)

interior-sub : (S : Tree n) → (P : Path S) → (T : Tree m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → Sub (suc m) (suc (insertion-tree-size S P T))
interior-sub S (PHere .S) T = idSub (suc _)
interior-sub (Join S₁ S₂) (PExt P) (Join T Sing) = connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ∘ suspSub (interior-sub S₁ P T)
interior-sub (Join S₁ S₂) (PShift P) T = connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (insertion-tree-size S₂ P T) ∘ interior-sub S₂ P T

is-non-empty-path : {T : Tree n} → Path T → Set
is-non-empty-path (PHere _) = ⊥
is-non-empty-path (PExt P) = ⊤
is-non-empty-path (PShift P) = ⊤

is-branching-path : {T : Tree n} → Path T → Set
is-branching-path (PHere T) = is-linear T
is-branching-path (PExt P) = is-branching-path P
is-branching-path (PShift P) = is-branching-path P × is-non-empty-path P

height-of-branching : {T : Tree n} → (P : Path T) → .⦃ is-branching-path P ⦄ → ℕ
height-of-branching (PHere T) = height-of-linear T
height-of-branching (PExt P) = suc (height-of-branching P)
height-of-branching (PShift P) ⦃ bp ⦄ = height-of-branching P ⦃ proj₁ bp ⦄

branching-path-to-var : (T : Tree n) → (P : Path T) → .⦃ bp : is-branching-path P ⦄ → Tm (suc n)
branching-path-to-var T (PHere .T) = 0V
branching-path-to-var (Join S T) (PExt P) = suspTm (branching-path-to-var S P) [ connect-pd-inc-left (susp-pd (tree-to-pd S)) (tree-size T) ]tm
branching-path-to-var (Join S T) (PShift P) ⦃ bp ⦄ = branching-path-to-var T P ⦃ proj₁ bp ⦄ [ connect-pd-inc-right (susp-pd (tree-to-pd S)) (tree-size T) ]tm

type-has-linear-height : (n : ℕ) → (T : Tree m) → .⦃ lh : has-linear-height n T ⦄ → (A : Ty (suc m) d) → Set
type-has-linear-height zero T A = ⊤
type-has-linear-height (suc n) (Join T Sing) A = Σ[ p ∈ is-unsuspendable-ty A ] type-has-linear-height n T (unsuspend-ty A ⦃ p ⦄)

exterior-sub : (S : Tree n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → (A : Ty (suc m) (height-of-branching P))
             → .⦃ type-has-linear-height (path-length P) T A ⦄
             → Sub (suc n) (suc (insertion-tree-size S P T))
exterior-sub S (PHere .S) T A = sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) A (idSub (suc _))) ∘ idSub≃ (linear-tree-compat S)
exterior-sub (Join S₁ S₂) (PExt P) (Join T Sing) A ⦃ tlh ⦄ =
  sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁)))
                       (connect-pd-inc-left (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) ∘ suspSub (exterior-sub S₁ P T (unsuspend-ty A ⦃ proj₁ tlh ⦄) ⦃ proj₂ tlh ⦄))
                       (connect-pd-inc-right (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂))
exterior-sub (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T A =
  sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁)))
                       (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size (insertion-tree S₂ P T)))
                       (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size (insertion-tree S₂ P T)) ∘ exterior-sub S₂ P ⦃ proj₁ bp ⦄ T A)

-- linear-to-var : (T : Tree n) → .⦃ _ : is-linear T ⦄ → Tm (tree-to-ctx T)
-- linear-to-var Sing = 0V
-- linear-to-var (Join T Sing) = suspTm (linear-to-var T)

-- linear-to-var-is-0V : (T : Tree n) → .(l : is-linear T) → linear-to-var T l ≃tm Var {Γ = tree-to-ctx T} zero
-- linear-to-var-is-0V Sing l = refl≃tm
-- linear-to-var-is-0V (Join T Sing) l = trans≃tm (susp-tm-≃ refl≃c (linear-to-var-is-0V T l)) lem
--   where
--     lem : lookupSusp {Γ = Γ} zero ≃tm Var {Γ = suspCtx Γ} zero
--     lem {Γ = Γ , A} = refl≃tm

-- linear-tree-var-height : (T : Tree n) → .⦃ _ : is-linear T ⦄ → height-of-linear T ≡ lookupHeight (tree-to-ctx T) zero
-- linear-tree-var-height Sing = refl
-- linear-tree-var-height (Join S Sing) = trans (cong suc (linear-tree-var-height S)) (lookupHeight-suspCtx (tree-to-ctx S) zero)

-- branching-path-to-var-height : (T : Tree n) → (P : Path T) → .⦃ bp : is-branching-path P ⦄ → height-of-branching P ≡ get-tm-height (branching-path-to-var T P)
-- branching-path-to-var-height T (PHere .T) = linear-tree-var-height T
-- branching-path-to-var-height (Join S T) (PExt P) = {!!}
-- branching-path-to-var-height (Join S T) (PShift P) = {!!}

-- branching-path-to-var-pd : (pd : Γ ⊢pd₀ d) → (P : Path (pd-to-tree pd)) → .(bp : is-branching-path P) → Tm Γ (suc (suc (height-of-branching P bp)))
-- branching-path-to-var-pd pd P bp = lem (pd-to-tree-to-ctx pd) (branching-path-to-var (pd-to-tree pd) P bp)
--   where
--     lem : Δ ≡ Δ′ → Tm Δ d → Tm Δ′ d
--     lem refl t = t

-- disc-to-outer : (T : Tree n) → (P : Path T) → .⦃ _ : is-branching-path P ⦄ → Sub (Disc (height-of-branching P)) (tree-to-ctx T)
-- disc-to-outer T P = sub-from-disc (branching-path-to-var T P) ∘ idSub≃ (disc-≡ {!!})

disc-to-inner : (T : Tree n) → (A : Ty (suc n) d) → Sub (disc-size d) (suc n)
disc-to-inner T A = sub-from-disc (tree-to-ctx T) (Coh (tree-to-ctx T) A (idSub (suc _)))

insertion-var-split : (S : Tree n)
                    → (P : Path S)
                    → .⦃ bp : is-branching-path P ⦄
                    → (T : Tree m)
                    → .⦃ lh : has-linear-height (path-length P) T ⦄
                    → VarSplit (suc (insertion-tree-size S P T)) (suc n) (suc m)
insertion-var-split S (PHere .S) T i = inj₂ i
insertion-var-split (Join S₁ S₂) (PExt P) (Join T Sing) i with connect-pd-var-split (susp-pd (tree-to-pd (insertion-tree S₁ P T))) (tree-size S₂) i
... | inj₂ j = inj₁ (varToVarFunction (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-right-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ j)
... | inj₁ j with susp-var-split (insertion-var-split S₁ P T) j
... | inj₁ k = inj₁ (varToVarFunction (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-left-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ k)
... | inj₂ k = inj₂ k
insertion-var-split (Join S₁ S₂) (PShift P) ⦃ bp ⦄ T i with connect-pd-var-split-right (susp-pd (tree-to-pd S₁)) (tree-size (insertion-tree S₂ P T)) i
... | inj₁ j = inj₁ (varToVarFunction (connect-pd-inc-left (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-left-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ j)
... | inj₂ j with insertion-var-split S₂ P ⦃ proj₁ bp ⦄ T j
... | inj₁ k = inj₁ (varToVarFunction (connect-pd-inc-right (susp-pd (tree-to-pd S₁)) (tree-size S₂)) ⦃ connect-pd-inc-right-var-to-var (susp-pd (tree-to-pd S₁)) (tree-size S₂) ⦄ k)
... | inj₂ k = inj₂ k
{-
insertion-var-split : (S : Tree n)
                    → (P : Path S)
                    → .⦃ bp : is-branching-path P ⦄
                    → (T : Tree m)
                    → .⦃ lh : has-linear-height (path-length P) T ⦄
                    → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                    → .⦃ tlh : type-has-linear-height (path-length P) T lh A ⦄
                    → VarSplit (tree-to-ctx (insertion-tree S P T lh)) (exterior-sub S P T A) (interior-sub S P T)
insertion-var-split S (PHere .S) bp T lh A x tlh i = inj₂ (i ,, (id-on-tm (Var i)))
insertion-var-split (Join S₁ S₂) (PExt P) bp (Join T Sing) lh A x tlh i with connect-pdb-var-split (Restr (susp-pdb (tree-to-pdb 0 (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂) i
... | inj₂ (j ,, p) = inj₁ (varToVarFunction (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) (connect-pdb-inc-right-var-to-var (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) j ,, γ)
  where
    open Reasoning tm-setoid
    lem : (getFocusTerm (Restr (susp-pdb (tree-to-pdb zero S₁ _))) [
             connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂)
             ∘ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)) ]tm)
            ≃tm
            (Var (fromℕ _) [
             connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) _)))
             (tree-to-ctx S₂)
             ]tm)
    lem = begin
      < getFocusTerm (Restr (susp-pdb (tree-to-pdb zero S₁ _)))
          [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂)
            ∘ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm
        >tm ≈⟨ assoc-tm (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂)) (suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh))) (getFocusTerm (Restr (susp-pdb (tree-to-pdb zero S₁ _)))) ⟩
      < getFocusTerm (Restr (susp-pdb (tree-to-pdb zero S₁ _)))
          [ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm
          [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ sub-action-≃-tm (suspSub-preserve-focus-tm (tree-to-pdb zero S₁ _) (tree-to-pdb 0 (insertion-tree S₁ P T _) tt) (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh))) refl≃s ⟩
      < getFocusTerm (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm >tm
        ≈⟨ connect-pdb-inc-fst-var (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ⟩
      < Var (fromℕ _) [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm >tm ∎

    γ : Var (varToVarFunction (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ j)
           [ exterior-sub (Join S₁ S₂) (PExt P) bp (Join T Sing) lh A x tlh ]tm
          ≃tm Var i
    γ = begin
      < Var (varToVarFunction (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ j)
            [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ]tm
        >tm ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ j) refl≃s ⟩
      < Var j [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂) ]tm
              [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ]tm
        >tm ≈˘⟨ assoc-tm (exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh) (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) (Var j) ⟩
      < Var j [ sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       ((connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) ∘ suspSub (exterior-sub S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂))
                ∘ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j}) (sub-from-connect-pdb-inc-right
          (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
          ((connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) ∘ suspSub (exterior-sub S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)))
          (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂))
          lem) ⟩
      < Var j [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ p ⟩
      < Var i >tm ∎
... | inj₁ (j ,, p) with susp-var-split (insertion-var-split S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)) j
... | inj₁ (k ,, q) = inj₁ ((varToVarFunction (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) (connect-pdb-inc-left-var-to-var (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) k) ,, γ)
  where
    open Reasoning tm-setoid
    γ : Var (varToVarFunction (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ k)
           [ exterior-sub (Join S₁ S₂) (PExt P) bp (Join T Sing) lh A x tlh ]tm
          ≃tm Var i
    γ = begin
      < Var (varToVarFunction (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ k)
            [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ]tm
        >tm ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ k) refl≃s ⟩
      < Var k [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂) ]tm
              [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ]tm
        >tm ≈˘⟨ assoc-tm (exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh) (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) (Var k) ⟩
      < Var k [ sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       ((connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) ∘ suspSub (exterior-sub S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂))
                ∘ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ sub-action-≃-tm (refl≃tm {s = Var k}) (sub-from-connect-pdb-inc-left
            (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
            ((connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) ∘ suspSub (exterior-sub S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)))
            (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂))) ⟩
      < Var k [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ∘ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm
        >tm ≈⟨ assoc-tm (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂)) (suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh))) (Var k) ⟩
      < Var k [ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm
              [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ sub-action-≃-tm q refl≃s ⟩
      < Var j [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ p ⟩
      < Var i >tm ∎
... | inj₂ (k ,, q) = inj₂ (k ,, γ)
  where
    open Reasoning tm-setoid
    γ : Var k [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 (insertion-tree S₁ P T _) tt))) (tree-to-ctx S₂) ∘ suspSub (interior-sub S₁ P T _) ]tm
          ≃tm Var i
    γ = begin
      < Var k [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 (insertion-tree S₁ P T _) tt))) (tree-to-ctx S₂) ∘ suspSub (interior-sub S₁ P T _) ]tm
        >tm ≈⟨ assoc-tm (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 (insertion-tree S₁ P T _) tt))) (tree-to-ctx S₂)) (suspSub (interior-sub S₁ P T _)) (Var k) ⟩
      < Var k [ suspSub (interior-sub S₁ P T _) ]tm
              [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ sub-action-≃-tm q refl≃s ⟩
      < Var j [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ p ⟩
      < Var i >tm ∎
insertion-var-split (Join S₁ S₂) (PShift P) bp T lh A x tlh i with connect-pdb-var-split (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T lh)) i
... | inj₁ (j ,, p) = inj₁ (varToVarFunction (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) (connect-pdb-inc-left-var-to-var (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) j ,, γ)
  where
    open Reasoning tm-setoid
    γ : (Var (varToVarFunction
            (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _)))
             (tree-to-ctx S₂))
            _ j)
           [ exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh
           ]tm)
          ≃tm Var i
    γ = begin
      < Var (varToVarFunction (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ j)
        [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ]tm
        >tm ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ j) refl≃s ⟩
      < Var j [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂) ]tm
              [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ]tm
        >tm ≈˘⟨ assoc-tm (exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh) (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) (Var j) ⟩
      < Var j [ sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ exterior-sub S₂ P (proj₁ bp) T lh A x tlh)
                ∘ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂) ]tm >tm
        ≈⟨ sub-action-≃-tm (refl≃tm {s = Var j}) (sub-from-connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
           (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)))
           (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ exterior-sub S₂ P (proj₁ bp) T lh A x tlh)) ⟩
      < Var j [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm
        >tm ≈⟨ p ⟩
      < Var i >tm ∎
... | inj₂ (j ,, p) with insertion-var-split S₂ P (proj₁ bp) T lh A x tlh j
... | inj₁ (k ,, q) = inj₁ ((varToVarFunction (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) (connect-pdb-inc-right-var-to-var (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) k) ,, γ)
  where
    open Reasoning tm-setoid
    lem : (getFocusTerm (Restr (susp-pdb (tree-to-pdb zero S₁ _))) [
             connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ _)))
             (tree-to-ctx (insertion-tree S₂ P T _))
             ]tm)
            ≃tm
            (Var (fromℕ _) [
             connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _)))
             (tree-to-ctx (insertion-tree S₂ P T _))
             ∘ exterior-sub S₂ P _ T _ A _ tlh
             ]tm)
    lem = begin
      < getFocusTerm (Restr (susp-pdb (tree-to-pdb zero S₁ _))) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm >tm
        ≈⟨ connect-pdb-inc-fst-var (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ⟩
      < Var (fromℕ (insertion-tree-size S₂ P T _)) [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm >tm
        ≈⟨ sub-action-≃-tm (exterior-sub-fst-var S₂ P (proj₁ bp) (proj₂ bp) T lh A x tlh) (refl≃s {σ = connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _))}) ⟩
      < (Var (fromℕ _) [ exterior-sub S₂ P _ T _ A _ tlh ]tm) [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm >tm
        ≈˘⟨ assoc-tm (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _))) (exterior-sub S₂ P _ T _ A _ tlh) (Var (fromℕ _)) ⟩
      < Var (fromℕ _) [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ∘ exterior-sub S₂ P _ T _ A _ tlh ]tm >tm ∎

    γ : (Var (varToVarFunction (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) _ k) [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ]tm)
          ≃tm Var i
    γ = begin
      < Var (varToVarFunction (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) _ k)
        [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ]tm
        >tm ≈⟨ sub-action-≃-tm (varToVarFunctionProp (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx S₂)) _ k) refl≃s ⟩
      < Var k [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂) ]tm
              [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ]tm
        >tm ≈˘⟨ assoc-tm (exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh) (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂)) (Var k) ⟩
      < Var k [ sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ exterior-sub S₂ P (proj₁ bp) T lh A x tlh)
                ∘ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx S₂) ]tm
        >tm ≈⟨ sub-action-≃-tm (refl≃tm {s = Var k}) (sub-from-connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
               (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)))
               (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ exterior-sub S₂ P (proj₁ bp) T lh A x tlh)
               lem) ⟩
      < Var k [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ∘ exterior-sub S₂ P (proj₁ bp) T _ A _ tlh ]tm
        >tm ≈⟨ assoc-tm (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _))) (exterior-sub S₂ P (proj₁ bp) T _ A _ tlh) (Var k) ⟩
      < Var k [ exterior-sub S₂ P _ T _ A _ tlh ]tm [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm
        >tm ≈⟨ sub-action-≃-tm q refl≃s ⟩
      < Var j [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm >tm
        ≈⟨ p ⟩
      < Var i >tm ∎
... | inj₂ (k ,, q) = inj₂ (k ,, γ)
  where
    open Reasoning tm-setoid
    γ : (Var k [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T _)) ∘ interior-sub S₂ P T _ ]tm)
          ≃tm Var i
    γ = begin
      < Var k [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ∘ interior-sub S₂ P T _ ]tm
        >tm ≈⟨ assoc-tm (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _))) (interior-sub S₂ P T _) (Var k) ⟩
      < Var k [ interior-sub S₂ P T _ ]tm
              [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb 0 S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm
        >tm ≈⟨ sub-action-≃-tm q refl≃s ⟩
      < Var j [ connect-inc-right (suspCtx (tree-to-ctx S₁)) (ty-tgt (getFocusType (susp-pdb (tree-to-pdb 0 S₁ _)))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm
        >tm ≈⟨ p ⟩
      < Var i >tm ∎
-}

sub-from-insertion-func : (S : Tree n)
                        → (P : Path S)
                        → .⦃ bp : is-branching-path P ⦄
                        → (T : Tree m)
                        → .⦃ lh : has-linear-height (path-length P) T ⦄
                        → (σ : Sub (suc n) l)
                        → (τ : Sub (suc m) l)
                        → (i : Fin (suc (insertion-tree-size S P T)))
                        → Tm l
sub-from-insertion-func S P T σ τ i with insertion-var-split S P T i
... | inj₁ j = Var j [ σ ]tm
... | inj₂ j = Var j [ τ ]tm

sub-from-insertion : (S : Tree n)
                   → (P : Path S)
                   → .⦃ bp : is-branching-path P ⦄
                   → (T : Tree m)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → (σ : Sub (suc n) l)
                   → (τ : Sub (suc m) l)
                   → Sub (suc (insertion-tree-size S P T)) l
sub-from-insertion S P T σ τ = sub-from-function (sub-from-insertion-func S P T σ τ)

{-

insertion-reduces-dim : (S : Tree n)
                      → (P : Path S)
                      → (T : Tree m)
                      → .(bp : is-branching-path P)
                      → .(lh : has-linear-height (path-length P) T)
                      → height-of-branching P bp ≥ tree-dim T
                      → tree-dim (insertion-tree S P T lh) ≤ tree-dim S
insertion-reduces-dim S (PHere .S) T bp lh p = ≤-trans p (≤-reflexive (height-of-linear-is-tree-dim S bp))
insertion-reduces-dim (Join S₁ S₂) (PExt P) (Join T Sing) bp lh p = ⊔-monoˡ-≤ (tree-dim S₂) (s≤s (insertion-reduces-dim S₁ P T bp lh (≤-pred p)))
insertion-reduces-dim (Join S₁ S₂) (PShift P) T bp lh p = ⊔-monoʳ-≤ (suc (tree-dim S₁)) (insertion-reduces-dim S₂ P T (proj₁ bp) lh p)

sub-from-insertion-≃ : (S : Tree n)
                     → (P : Path S)
                     → .(bp : is-branching-path P)
                     → (T : Tree m)
                     → .(lh : has-linear-height (path-length P) T)
                     → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                     → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
                     → (tlh : type-has-linear-height (path-length P) T lh A)
                     → {σ : Sub (tree-to-ctx S) Γ}
                     → {σ′ : Sub (tree-to-ctx S) Δ}
                     → {τ : Sub (tree-to-ctx T) Γ}
                     → {τ′ : Sub (tree-to-ctx T) Δ}
                     → σ ≃s σ′
                     → τ ≃s τ′
                     → sub-from-insertion S P bp T lh A x tlh σ τ ≃s sub-from-insertion S P bp T lh A x tlh σ′ τ′
sub-from-insertion-≃ S P bp T lh A x tlh σeq τeq = sub-from-function-≃ _ _ γ
  where
    γ : (i : Fin (ctxLength (tree-to-ctx (insertion-tree S P T _))))
      → sub-from-insertion-func S P _ T _ A _ tlh _ _ i
        ≃tm sub-from-insertion-func S P _ T _ A _ tlh _ _ i
    γ i with insertion-var-split S P bp T lh A x tlh i
    ... | inj₁ (j ,, p) rewrite sym (≃tm-preserve-dim refl≃c p) = sub-action-≃-tm (refl≃tm {s = Var j}) σeq
    ... | inj₂ (j ,, p) rewrite sym (≃tm-preserve-dim refl≃c p) = sub-action-≃-tm (refl≃tm {s = Var j}) τeq

type-has-linear-height-≃ : (T : Tree m) → {A : Ty (tree-to-ctx T) d} → {B : Ty (tree-to-ctx T) d} → A ≃ty B → .(lh : has-linear-height n T) → type-has-linear-height n T lh A → type-has-linear-height n T lh B
type-has-linear-height-≃ T p lh tlh with ≃ty-to-≡ p
... | refl = tlh

sub-from-insertion-func-susp : (S : Tree n)
                             → (P : Path S)
                             → .(bp : is-branching-path P)
                             → (T : Tree m)
                             → .(lh : has-linear-height (path-length P) T)
                             → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                             → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
                             → (tlh : type-has-linear-height (path-length P) T lh A)
                             → (σ : Sub (tree-to-ctx S) Γ)
                             → (τ : Sub (tree-to-ctx T) Γ)
                             → (i : Fin (ctxLength (tree-to-ctx (insertion-tree (susp-tree S) (PExt P) (susp-tree T) _))))
                             → sub-from-insertion-func (Join S Sing) (PExt P) bp (Join T Sing) lh (suspTy A) (≤-trans (≤-reflexive (ctx-susp-dim (tree-to-ctx T))) (s≤s x)) (type-has-linear-height-susp T lh tlh) (suspSub σ) (suspSub τ) i ≃tm susp-function {Γ = tree-to-ctx (insertion-tree S P T lh)} (sub-from-insertion-func S P bp T lh A x tlh σ τ) i
sub-from-insertion-func-susp S P bp T lh A x tlh σ τ i with suspension-vars (tree-to-ctx (insertion-tree S P T lh)) i
... | inj₁ p = {!!}
... | inj₂ (j ,, refl) = begin
  < (sub-from-insertion-func (Join S Sing) (PExt P) bp (Join T Sing) lh (suspTy A) (≤-trans (≤-reflexive (ctx-susp-dim (tree-to-ctx T))) (s≤s x)) (type-has-linear-height-susp T lh tlh) (suspSub σ) (suspSub τ) (inject₁ (inject₁ j))) >tm ≈⟨ {!!} ⟩
  < suspTm (sub-from-insertion-func S P _ T _ A _ tlh σ τ j) >tm ≈˘⟨ susp-function-prop {Γ = tree-to-ctx (insertion-tree S P T lh)} (sub-from-insertion-func S P bp T lh A x tlh σ τ) j ⟩
  < susp-function {Γ = tree-to-ctx (insertion-tree S P T lh)} (sub-from-insertion-func S P bp T lh A x tlh σ τ) (inject₁ (inject₁ j)) >tm ∎
  where
    open Reasoning tm-setoid

sub-from-insertion-susp : (S : Tree n)
                        → (P : Path S)
                        → .(bp : is-branching-path P)
                        → (T : Tree m)
                        → .(lh : has-linear-height (path-length P) T)
                        → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                        → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
                        → (tlh : type-has-linear-height (path-length P) T lh A)
                        → (σ : Sub (tree-to-ctx S) Γ)
                        → (τ : Sub (tree-to-ctx T) Γ)
                        → sub-from-insertion (susp-tree S) (PExt P) bp (susp-tree T) lh (suspTy A) (≤-trans (≤-reflexive (ctx-susp-dim (tree-to-ctx T))) (s≤s x)) (type-has-linear-height-susp T lh tlh) (suspSub σ) (suspSub τ) ≃s suspSub (sub-from-insertion S P bp T lh A x tlh σ τ)
sub-from-insertion-susp S P bp T lh A x tlh σ τ = trans≃s (sub-from-function-≃ (sub-from-insertion-func (susp-tree S) (PExt P) bp (susp-tree T) lh (suspTy A) (≤-trans (≤-reflexive (ctx-susp-dim (tree-to-ctx T))) (s≤s x)) (type-has-linear-height-susp T _ tlh) (suspSub σ) (suspSub τ)) (susp-function {Γ = tree-to-ctx (insertion-tree S P T lh)} (sub-from-insertion-func S P bp T lh A x tlh σ τ)) (sub-from-insertion-func-susp S P bp T lh A x tlh σ τ)) (sub-from-function-susp (sub-from-insertion-func S P bp T lh A x tlh σ τ))
-}
