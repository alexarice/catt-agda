{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Insertion where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Catt.Dimension
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
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ)
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

insertion-tree-size :  (S : Tree n) → (P : Path S) → (T : Tree m) → .(has-linear-height (path-length P) T) → ℕ
insertion-tree : (S : Tree n) → (P : Path S) → (T : Tree m) → .(lh : has-linear-height (path-length P) T) → Tree (insertion-tree-size S P T lh)

insertion-tree-size {m = m} S (PHere .S) T lh = m
insertion-tree-size (Join {m = m} S₁ S₂) (PExt P) (Join T Sing) lh = m + suc (suc (insertion-tree-size S₁ P T lh))
insertion-tree-size (Join {n = n} S₁ S₂) (PShift P) T lh = insertion-tree-size S₂ P T lh + suc (suc n)

insertion-tree S (PHere .S) T lh = T
insertion-tree (Join S₁ S₂) (PExt P) (Join T Sing) lh = Join (insertion-tree S₁ P T lh) S₂
insertion-tree (Join S₁ S₂) (PShift P) T lh = Join S₁ (insertion-tree S₂ P T lh)

interior-sub : (S : Tree n) → (P : Path S) → (T : Tree m) → .(lh : has-linear-height (path-length P) T) → Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S P T lh))
interior-sub S (PHere .S) T lh = idSub (tree-to-ctx T)
interior-sub (Join S₁ S₂) (PExt P) (Join T Sing) lh = connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂) ∘ suspSub (interior-sub S₁ P T lh)
interior-sub (Join S₁ S₂) (PShift P) T lh = connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ interior-sub S₂ P T lh

is-non-empty-path : {T : Tree n} → Path T → Set
is-non-empty-path (PHere _) = ⊥
is-non-empty-path (PExt P) = ⊤
is-non-empty-path (PShift P) = ⊤

is-branching-path : {T : Tree n} → Path T → Set
is-branching-path (PHere T) = is-linear T
is-branching-path (PExt P) = is-branching-path P
is-branching-path (PShift P) = is-branching-path P × is-non-empty-path P

height-of-branching : {T : Tree n} → (P : Path T) → .(is-branching-path P) → ℕ
height-of-branching (PHere T) bp = height-of-linear T bp
height-of-branching (PExt P) bp = suc (height-of-branching P bp)
height-of-branching (PShift P) bp = height-of-branching P (proj₁ bp)

type-has-linear-height : (n : ℕ) → {d : ℕ} → (T : Tree m) → .(lh : has-linear-height n T) → (A : Ty (tree-to-ctx T) d) → Set
type-has-linear-height zero T lh A = ⊤
type-has-linear-height (suc n) (Join T Sing) lh A = Σ[ p ∈ is-unsuspendable-ty (tree-to-ctx T) A refl≃c ] type-has-linear-height n T lh (unsuspend-ty A (tree-to-ctx T) refl≃c p)

exterior-sub : (S : Tree n)
             → (P : Path S)
             → .(bp : is-branching-path P)
             → (T : Tree m)
             → .(lh : has-linear-height (path-length P) T)
             → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
             → .(ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
             → (type-has-linear-height (path-length P) T lh A)
             → Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S P T lh))
exterior-sub S (PHere .S) bp T lh A x tlh = sub-from-disc (Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T))) ∘ (idSub≃ (linear-tree-compat S bp))
exterior-sub (Join S₁ S₂) (PExt P) bp (Join T Sing) lh A x tlh =
  sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       ((connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) ∘ suspSub (exterior-sub S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂))
exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh =
  sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ exterior-sub S₂ P (proj₁ bp) T lh A x tlh)

exterior-sub-fst-var : (S : Tree n)
                     → (P : Path S)
                     → .(bp : is-branching-path P)
                     → .(is-non-empty-path P)
                     → (T : Tree m)
                     → .(lh : has-linear-height (path-length P) T)
                     → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                     → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
                     → (tlh : type-has-linear-height (path-length P) T lh A)
                     → Var {Γ = tree-to-ctx (insertion-tree S P T lh)} (fromℕ _) ≃tm Var (fromℕ _) [ exterior-sub S P bp T lh A x tlh ]tm
exterior-sub-fst-var (Join S₁ S₂) (PExt P) bp ne (Join T Sing) lh A x tlh = begin
  < Var (fromℕ (insertion-tree-size (Join S₁ S₂) (PExt P) (Join T Sing) _)) >tm ≈˘⟨ connect-pdb-inc-left-fst-var ((Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _)))) (tree-to-ctx S₂) ⟩
  < Var (fromℕ (suc (suc (insertion-tree-size S₁ P T _)))) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (susp-fst-var (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh))) refl≃s ⟩
  < (Var (fromℕ (suc (suc _))) [ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm >tm
    ≈˘⟨ assoc-tm (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) _))) (tree-to-ctx S₂)) (suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh))) (Var (fromℕ _)) ⟩
  < Var (fromℕ _) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) _))) (tree-to-ctx S₂) ∘ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm >tm
    ≈˘⟨ sub-from-connect-pdb-fst-var (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ∘ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh))) (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂)) ⟩
  < Var (fromℕ _) [ sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ _)))
                                          (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ∘ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)))
                                          (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂)) ]tm >tm ≡⟨⟩
  < Var (fromℕ (_ + suc (suc _))) [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ]tm >tm ∎
  where
    open Reasoning tm-setoid
exterior-sub-fst-var (Join S₁ S₂) (PShift P) bp ne T lh A x tlh = begin
  < Var (fromℕ (insertion-tree-size (Join S₁ S₂) (PShift P) T _)) >tm ≈˘⟨ connect-pdb-inc-left-fst-var (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ⟩
  < Var (fromℕ _) [ (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T lh))) ]tm >tm ≈˘⟨ sub-from-connect-pdb-fst-var (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _))) (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ∘ exterior-sub S₂ P _ T _ A _ tlh) ⟩
  < Var (fromℕ _) [ sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ _)))
                                         (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)))
                                         (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ∘ exterior-sub S₂ P (proj₁ bp) T lh A x tlh) ]tm >tm
       ≡⟨⟩
  < Var (fromℕ (_ + suc (suc _))) [ exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh ]tm >tm ∎
  where
    open Reasoning tm-setoid

linear-to-var : (T : Tree n) → .(l : is-linear T) → Tm (tree-to-ctx T) (suc (suc (height-of-linear T l)))
linear-to-var Sing l = 0V
linear-to-var (Join T Sing) l = suspTm (linear-to-var T l)

linear-to-var-is-0V : (T : Tree n) → .(l : is-linear T) → linear-to-var T l ≃tm Var {Γ = tree-to-ctx T} zero
linear-to-var-is-0V Sing l = refl≃tm
linear-to-var-is-0V (Join T Sing) l = trans≃tm (susp-tm-≃ refl≃c (linear-to-var-is-0V T l)) lem
  where
    lem : lookupSusp {Γ = Γ} zero ≃tm Var {Γ = suspCtx Γ} zero
    lem {Γ = Γ , A} = refl≃tm

branching-path-to-var : (T : Tree n) → (P : Path T) → .(bp : is-branching-path P) → Tm (tree-to-ctx T) (suc (suc (height-of-branching P bp)))
branching-path-to-var T (PHere .T) bp = linear-to-var T bp
branching-path-to-var (Join S T) (PExt P) bp = suspTm (branching-path-to-var S P bp) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S tt))) (tree-to-ctx T) ]tm
branching-path-to-var (Join S T) (PShift P) bp = branching-path-to-var T P (proj₁ bp) [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S tt))) (tree-to-ctx T) ]tm

branching-path-to-var-pd : (pd : Γ ⊢pd₀ d) → (P : Path (pd-to-tree pd)) → .(bp : is-branching-path P) → Tm Γ (suc (suc (height-of-branching P bp)))
branching-path-to-var-pd pd P bp = lem (pd-to-tree-to-ctx pd) (branching-path-to-var (pd-to-tree pd) P bp)
  where
    lem : Δ ≡ Δ′ → Tm Δ d → Tm Δ′ d
    lem refl t = t

disc-to-outer : (T : Tree n) → (P : Path T) → .(bp : is-branching-path P) → Sub (Disc (height-of-branching P bp)) (tree-to-ctx T)
disc-to-outer T P bp = sub-from-disc (branching-path-to-var T P bp)

disc-to-inner : (T : Tree n) → .(ctx-dim (tree-to-ctx T) ≤ suc d) → (A : Ty (tree-to-ctx T) (suc d)) → Sub (Disc d) (tree-to-ctx T)
disc-to-inner T x A = sub-from-disc (Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T)))

insertion-comm : (S : Tree n)
               → (P : Path S)
               → .(bp : is-branching-path P)
               → (T : Tree m)
               → .(lh : has-linear-height (path-length P) T)
               → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
               → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
               → (tlh : type-has-linear-height (path-length P) T lh A)
               → 0V [ interior-sub S P T lh ∘ disc-to-inner T x A ]tm ≃tm 0V [ exterior-sub S P bp T lh A x tlh ∘ disc-to-outer S P bp ]tm

insertion-comm S (PHere .S) bp T lh A x tlh = begin
  < 0V [ interior-sub S (PHere S) T _ ∘ disc-to-inner T _ A ]tm >tm ≡⟨⟩
  < 0V [ idSub (tree-to-ctx T) ∘ sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T))) ]tm >tm ≈⟨ assoc-tm (idSub (tree-to-ctx T)) (sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T)))) 0V ⟩
  < (0V [ sub-from-disc (Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T))) ]tm) [ idSub (tree-to-ctx T) ]tm >tm ≈⟨ id-on-tm (0V [ sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T))) ]tm) ⟩
  < 0V [ sub-from-disc (Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T))) ]tm >tm ≡⟨⟩
  < Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T)) >tm ≡⟨⟩
  < 0V [ sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T))) ]tm >tm ≈˘⟨ sub-action-≃-tm (idSub≃-on-tm (linear-tree-compat S bp) (Var≃ refl)) refl≃s ⟩
  < 0V [ idSub≃ (linear-tree-compat S _) ]tm [ sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T))) ]tm >tm ≈˘⟨ assoc-tm (sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T)))) (idSub≃ (linear-tree-compat S _)) 0V ⟩
  < 0V [ sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T))) ∘ idSub≃ (linear-tree-compat S _) ]tm >tm ≈˘⟨ sub-action-≃-tm (linear-to-var-is-0V S bp) refl≃s ⟩
  < linear-to-var S _ [ sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T))) ∘ idSub≃ (linear-tree-compat S _) ]tm >tm ≡⟨⟩
  < 0V [ sub-from-disc (linear-to-var S _) ]tm [ sub-from-disc (Coh (tree-to-ctx T) A _ (idSub (tree-to-ctx T))) ∘ idSub≃ (linear-tree-compat S _) ]tm >tm ≈˘⟨ assoc-tm (sub-from-disc (Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T))) ∘ idSub≃ (linear-tree-compat S _)) (sub-from-disc (linear-to-var S _)) 0V ⟩
  < 0V [ sub-from-disc (Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T))) ∘ idSub≃ (linear-tree-compat S _) ∘ sub-from-disc (linear-to-var S _) ]tm >tm ≡⟨⟩
  < 0V [ exterior-sub S (PHere S) _ T _ A _ tlh ∘ disc-to-outer S (PHere S) _ ]tm >tm ∎
  where
    open Reasoning tm-setoid
insertion-comm (Join S₁ S₂) (PExt P) bp (Join T Sing) lh A x tlh = begin
  < 0V [ interior-sub (Join S₁ S₂) (PExt P) (Join T Sing) _ ∘ disc-to-inner (Join T Sing) _ A ]tm >tm ≡⟨⟩
  < 0V [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂) ∘ suspSub (interior-sub S₁ P T lh) ∘ sub-from-disc (Coh (tree-to-ctx (Join T Sing)) A x (idSub (tree-to-ctx (Join T Sing)))) ]tm >tm ≡⟨⟩
  < Coh (tree-to-ctx (Join T Sing)) A x (idSub (tree-to-ctx (Join T Sing))) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂) ∘ suspSub (interior-sub S₁ P T lh) ]tm >tm
    ≈⟨ assoc-tm (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) (suspSub (interior-sub S₁ P T lh)) (Coh (tree-to-ctx (Join T Sing)) A x (idSub (tree-to-ctx (Join T Sing)))) ⟩
  < Coh (tree-to-ctx (Join T Sing)) A _ (idSub (tree-to-ctx (Join T Sing))) [ suspSub (interior-sub S₁ P T _) ]tm [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm >tm
    ≈⟨ sub-action-≃-tm lem refl≃s ⟩
  < suspTm (branching-path-to-var S₁ P _) [ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ]tm >tm
    ≈˘⟨ assoc-tm (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂)) (suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh))) (suspTm (branching-path-to-var S₁ P _)) ⟩
  < suspTm (branching-path-to-var S₁ P _) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T _) _))) (tree-to-ctx S₂) ∘ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = suspTm (branching-path-to-var S₁ P _)}) (sub-from-connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) ((connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) ∘ suspSub (exterior-sub S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh))) (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂))) ⟩
  < suspTm (branching-path-to-var S₁ P _) [ sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                                                                 ((connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) ∘ suspSub (exterior-sub S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)))
                                                                 (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂))
                                            ∘ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx S₂) ]tm >tm ≡⟨⟩
  < suspTm (branching-path-to-var S₁ P _) [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ∘ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx S₂) ]tm >tm
    ≈⟨ assoc-tm (exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh) (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx S₂)) (suspTm (branching-path-to-var S₁ P bp)) ⟩
  < suspTm (branching-path-to-var S₁ P bp) [ connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx S₂) ]tm [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ]tm >tm ≡⟨⟩
  < branching-path-to-var (Join S₁ S₂) (PExt P) _ [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ]tm >tm ≡⟨⟩
  < 0V [ sub-from-disc (branching-path-to-var (Join S₁ S₂) (PExt P) _) ]tm [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ]tm >tm
    ≈˘⟨ assoc-tm (exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh) (sub-from-disc (branching-path-to-var (Join S₁ S₂) (PExt P) bp)) 0V ⟩
  < 0V [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ∘ sub-from-disc (branching-path-to-var (Join S₁ S₂) (PExt P) bp) ]tm >tm ≡⟨⟩
  < 0V [ exterior-sub (Join S₁ S₂) (PExt P) _ (Join T Sing) _ A x tlh ∘ disc-to-outer (Join S₁ S₂) (PExt P) _ ]tm >tm ∎
  where
    open Reasoning tm-setoid
    lem : (Coh (tree-to-ctx (Join T Sing)) A _ (idSub (tree-to-ctx (Join T Sing))) [ suspSub (interior-sub S₁ P T _) ]tm) ≃tm (suspTm (branching-path-to-var S₁ P _) [ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm)
    lem = begin
      < Coh (suspCtx (tree-to-ctx T)) A _ (suspSub (interior-sub S₁ P T _) ∘ idSub (suspCtx (tree-to-ctx T))) >tm
        ≈˘⟨ Coh≃ refl≃c
                (unsuspend-ty-compat A (tree-to-ctx T) refl≃c (proj₁ tlh))
                (trans≃s (susp-functorial (interior-sub S₁ P T _) (idSub (tree-to-ctx T)))
                         (sub-action-≃-sub (susp-functorial-id (tree-to-ctx T)) refl≃s)) ⟩
      < Coh (suspCtx (tree-to-ctx T)) (suspTy (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh))) _ (suspSub (interior-sub S₁ P T _ ∘ idSub (tree-to-ctx T))) >tm ≡⟨⟩
      < suspTm (0V [ interior-sub S₁ P T _ ∘ disc-to-inner T (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) ]tm)
        >tm ≈⟨ susp-tm-≃ refl≃c (insertion-comm S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred
                                                                                                                   (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)) ⟩
      < suspTm (0V [ exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh) ∘ disc-to-outer S₁ P bp ]tm) >tm ≡⟨⟩
      < suspTm (branching-path-to-var S₁ P _ [ exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh) ]tm) >tm
        ≈⟨ susp-functorial-tm (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) (branching-path-to-var S₁ P _) ⟩
      < suspTm (branching-path-to-var S₁ P _) [ suspSub (exterior-sub S₁ P _ T _ (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) _ (proj₂ tlh)) ]tm >tm ∎

insertion-comm (Join S₁ S₂) (PShift P) bp T lh A x tlh = begin
  < 0V [ interior-sub (Join S₁ S₂) (PShift P) T _ ∘ disc-to-inner T _ A ]tm >tm ≡⟨⟩
  < 0V [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ interior-sub S₂ P T lh ∘
       disc-to-inner T x A ]tm >tm ≈⟨ sub-action-≃-tm (refl≃tm {s = 0V}) (∘-assoc (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh))) (interior-sub S₂ P T lh) (disc-to-inner T x A)) ⟩
  < 0V [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ (interior-sub S₂ P T lh ∘
       disc-to-inner T x A) ]tm >tm ≈⟨ assoc-tm (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh))) (interior-sub S₂ P T lh ∘ disc-to-inner T x A) 0V ⟩
  < 0V [ interior-sub S₂ P T _ ∘ disc-to-inner T _ A ]tm [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm >tm ≈⟨ sub-action-≃-tm (insertion-comm S₂ P (proj₁ bp) T lh A x tlh) (refl≃s {σ = connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _))}) ⟩
  < 0V [ exterior-sub S₂ P (proj₁ bp) T lh A x tlh ∘ disc-to-outer S₂ P (proj₁ bp) ]tm [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm >tm ≈˘⟨ sub-action-≃-tm (assoc-tm (exterior-sub S₂ P (proj₁ bp) T lh A x tlh) (disc-to-outer S₂ P (proj₁ bp)) 0V) refl≃s ⟩
  < 0V [ disc-to-outer S₂ P (proj₁ bp) ]tm [ exterior-sub S₂ P _ T _ A _ tlh ]tm [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ]tm >tm ≈˘⟨ assoc-tm (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _))) (exterior-sub S₂ P _ T _ A _ tlh) (0V [ disc-to-outer S₂ P (proj₁ bp) ]tm) ⟩
  < 0V [ disc-to-outer S₂ P (proj₁ bp) ]tm [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ∘ exterior-sub S₂ P _ T _ A _ tlh ]tm >tm ≡⟨⟩
  < branching-path-to-var S₂ P _ [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx (insertion-tree S₂ P T _)) ∘ exterior-sub S₂ P _ T _ A _ tlh ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = branching-path-to-var S₂ P _}) (sub-from-connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx  (insertion-tree S₂ P T lh))) ((connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ exterior-sub S₂ P (proj₁ bp) T lh A x tlh)) lem) ⟩
  < branching-path-to-var S₂ P _ [
      sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ exterior-sub S₂ P (proj₁ bp) T lh A x tlh)
      ∘ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx S₂) ]tm >tm ≡⟨⟩
  < branching-path-to-var S₂ P _ [ exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh ∘ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx S₂) ]tm >tm ≈⟨ assoc-tm (exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh) (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx S₂)) (branching-path-to-var S₂ P (proj₁ bp)) ⟩
  < branching-path-to-var S₂ P _ [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx S₂) ]tm [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ]tm >tm ≡⟨⟩
  < 0V [ sub-from-disc (branching-path-to-var S₂ P _ [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ _))) (tree-to-ctx S₂) ]tm) ]tm [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ]tm >tm ≈˘⟨ assoc-tm (exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh) (sub-from-disc (branching-path-to-var S₂ P (proj₁ bp) [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx S₂) ]tm)) 0V ⟩
  < 0V [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ∘ sub-from-disc (branching-path-to-var S₂ P (proj₁ bp) [ connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx S₂) ]tm) ]tm >tm ≡⟨⟩
  < 0V [ exterior-sub (Join S₁ S₂) (PShift P) bp T _ A _ tlh ∘ disc-to-outer (Join S₁ S₂) (PShift P) bp ]tm >tm ∎
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

insertion-var-split : (S : Tree n)
                    → (P : Path S)
                    → .(bp : is-branching-path P)
                    → (T : Tree m)
                    → .(lh : has-linear-height (path-length P) T)
                    → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                    → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
                    → (tlh : type-has-linear-height (path-length P) T lh A)
                    → VarSplit (tree-to-ctx (insertion-tree S P T lh)) (exterior-sub S P bp T lh A x tlh) (interior-sub S P T lh)
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

sub-from-insertion-func : (S : Tree n)
                       → (P : Path S)
                       → .(bp : is-branching-path P)
                       → (T : Tree m)
                       → .(lh : has-linear-height (path-length P) T)
                       → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                       → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
                       → (tlh : type-has-linear-height (path-length P) T lh A)
                       → (σ : Sub (tree-to-ctx S) Γ)
                       → (τ : Sub (tree-to-ctx T) Γ)
                       → (i : Fin (ctxLength (tree-to-ctx (insertion-tree S P T _))))
                       → Tm _ (suc (lookupDim (tree-to-ctx (insertion-tree S P T _)) i))
sub-from-insertion-func S P bp T lh A x tlh σ τ i with insertion-var-split S P bp T lh A x tlh i
... | inj₁ (j ,, p) rewrite sym (≃tm-preserve-dim refl≃c p) = Var j [ σ ]tm
... | inj₂ (j ,, p) rewrite sym (≃tm-preserve-dim refl≃c p) = Var j [ τ ]tm

sub-from-insertion : (S : Tree n)
                   → (P : Path S)
                   → .(bp : is-branching-path P)
                   → (T : Tree m)
                   → .(lh : has-linear-height (path-length P) T)
                   → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                   → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
                   → (tlh : type-has-linear-height (path-length P) T lh A)
                   → (σ : Sub (tree-to-ctx S) Γ)
                   → (τ : Sub (tree-to-ctx T) Γ)
                   → Sub (tree-to-ctx (insertion-tree S P T lh)) Γ
sub-from-insertion S P bp T lh A x tlh σ τ = sub-from-function (sub-from-insertion-func S P bp T lh A x tlh σ τ)



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

lift-sub-from-insertion : (S : Tree n)
                        → (P : Path S)
                        → .(bp : is-branching-path P)
                        → (T : Tree m)
                        → .(lh : has-linear-height (path-length P) T)
                        → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
                        → .(x : ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
                        → (tlh : type-has-linear-height (path-length P) T lh A)
                        → (σ : Sub (tree-to-ctx S) Γ)
                        → (τ : Sub (tree-to-ctx T) Γ)
                        → liftSub {A = B} (sub-from-insertion S P bp T lh A x tlh σ τ) ≃s sub-from-insertion S P bp T lh A x tlh (liftSub {A = B} σ) (liftSub τ)
lift-sub-from-insertion S P bp T lh A x tlh σ τ = trans≃s (lift-sub-from-function _) (sub-from-function-≃ _ _ γ)
  where
    γ : (i : Fin (ctxLength (tree-to-ctx (insertion-tree S P T _))))
      → liftTerm (sub-from-insertion-func S P _ T _ A _ tlh σ τ i)
        ≃tm sub-from-insertion-func S P _ T _ A _ tlh (liftSub σ) (liftSub τ) i
    γ i with insertion-var-split S P bp T lh A x tlh i
    ... | inj₁ (j ,, p) rewrite sym (≃tm-preserve-dim refl≃c p) = sym≃tm (apply-lifted-sub-tm-≃ (Var j) σ)
    ... | inj₂ (j ,, p) rewrite sym (≃tm-preserve-dim refl≃c p) = sym≃tm (apply-lifted-sub-tm-≃ (Var j) τ)

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
