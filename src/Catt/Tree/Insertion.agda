module Catt.Tree.Insertion where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Tree.Substitution

data Path {Xr : ISet} : Tree Xr l n → Set where
  PHere : {S : Tree Xr l m} → {x : Xr l} → {T : Tree Xr l n} → Path (Join x S T)
  PExt : {S : Tree Xr l m} → {x : Xr l} → {T : Tree Xr l n} → Path S → Path (Join x S T)
  PShift : {S : Tree Xr l m} → {x : Xr l} → {T : Tree Xr l n} → Path T → Path (Join x S T)

path-length : {T : Tree Xr l n} → Path T → ℕ
path-length PHere = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P

has-linear-height : ℕ → Tree Xr l n → Set
has-linear-height zero T = ⊤
has-linear-height (suc n) (Sing _) = ⊥
has-linear-height (suc n) (Join _ T (Sing _)) = has-linear-height n T
has-linear-height (suc n) (Join _ T (Join _ _ _)) = ⊥

insertion-tree-size : (S : Tree Xr l n) → (P : Path S) → (T : Tree Xr l m) → .⦃ has-linear-height (path-length P) T ⦄ → ℕ
insertion-tree : (S : Tree Xr l n) → (P : Path S) → (T : Tree Xr l m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → Tree Xr l (insertion-tree-size S P T)

insertion-tree-size {m = m} (Join _ S₁ S₂) PHere T = connect-tree-length T S₂
insertion-tree-size (Join {m = m} _ S₁ S₂) (PExt P) (Join _ T (Sing _)) = m + suc (suc (insertion-tree-size S₁ P T))
insertion-tree-size (Join {n = n} _ S₁ S₂) (PShift P) T = insertion-tree-size S₂ P T + suc (suc n)

insertion-tree (Join x S₁ S₂) PHere T = connect-tree T S₂
insertion-tree (Join x S₁ S₂) (PExt P) (Join y T (Sing z)) = Join y (insertion-tree S₁ P T) (replace-label z S₂)
insertion-tree (Join x S₁ S₂) (PShift P) T = Join x S₁ (insertion-tree S₂ P T)

interior-sub : (S : Tree⊤ n) → (P : Path S) → (T : Tree⊤ m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → Sub (suc m) (suc (insertion-tree-size S P T)) ⋆
interior-sub (Join⊤ S₁ S₂) PHere T = idSub≃ (sym≃c (connect-tree-to-ctx T S₂)) ∘ connect-inc-left (tree-last-var T) _
interior-sub (Join⊤ S₁ S₂) (PExt P) (Join⊤ T Sing⊤) = connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂) ∘ suspSub (interior-sub S₁ P T)
interior-sub (Join⊤ S₁ S₂) (PShift P) T = connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T) ∘ interior-sub S₂ P T

interior-treeSub : (S : Tree⊤ n) → (P : Path S) → (T : Tree⊤ m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → TreeSub m (suc (insertion-tree-size S P T))
interior-treeSub (Join⊤ S₁ S₂) PHere T = connect-tree-inc-left T S₂
interior-treeSub (Join⊤ S₁ S₂) (PExt P) (Join⊤ T Sing⊤) = suspTreeSub (interior-treeSub S₁ P T) [ connect-susp-inc-left (insertion-tree-size S₁ P T) (tree-size S₂) ]ts
interior-treeSub (Join⊤ S₁ S₂) (PShift P) T = (interior-treeSub S₂ P T) [ (connect-susp-inc-right (tree-size S₁) (insertion-tree-size S₂ P T)) ]ts

is-branching-path : {T : Tree Xr l n} → Path T → Set
is-branching-path {T = Join _ S T} PHere = is-linear S
is-branching-path (PExt P) = is-branching-path P
is-branching-path (PShift P) = is-branching-path P

height-of-branching : {T : Tree Xr l n} → (P : Path T) → .⦃ is-branching-path P ⦄ → ℕ
height-of-branching {T = Join _ S T} PHere = suc (tree-dim S)
height-of-branching (PExt P) = suc (height-of-branching P)
height-of-branching (PShift P) = height-of-branching P

branching-path-to-var : (T : Tree Xr l n) → (P : Path T) → .⦃ bp : is-branching-path P ⦄ → Tm (suc n)
branching-path-to-var (Join _ S T) (PHere) = 0V [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var (Join _ S T) (PExt P) = suspTm (branching-path-to-var S P) [ connect-susp-inc-left (tree-size S) (tree-size T) ]tm
branching-path-to-var (Join _ S T) (PShift P) ⦃ bp ⦄ = branching-path-to-var T P ⦃ bp ⦄ [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm

exterior-sub : (S : Tree⊤ n)
             → (P : Path S)
             → .⦃ _ : is-branching-path P ⦄
             → (T : Tree⊤ m)
             → .⦃ _ : has-linear-height (path-length P) T ⦄
             → Sub (suc n) (suc (insertion-tree-size S P T)) ⋆
exterior-sub (Join⊤ S₁ S₂) PHere T
  = idSub≃ (sym≃c (connect-tree-to-ctx T S₂))
    ∘ sub-between-connects (sub-from-linear-tree-unbiased (suspTree⊤ S₁) T 0)
                           idSub
                           (tree-last-var T)
exterior-sub (Join⊤ S₁ S₂) (PExt P) (Join⊤ T Sing⊤) =
  sub-between-connect-susps (exterior-sub S₁ P T)
                            idSub
exterior-sub (Join⊤ S₁ S₂) (PShift P) T =
  sub-between-connect-susps idSub
                            (exterior-sub S₂ P T)

exterior-treeSub : (S : Tree⊤ n)
                 → (P : Path S)
                 → .⦃ _ : is-branching-path P ⦄
                 → (T : Tree⊤ m)
                 → .⦃ _ : has-linear-height (path-length P) T ⦄
                 → TreeSub n (suc (insertion-tree-size S P T))
exterior-treeSub (Join⊤ S₁ S₂) PHere T = connect-tree ((sub-to-treeSub (suspTree⊤ S₁) (sub-from-linear-tree-unbiased (suspTree⊤ S₁) T 0)) [ (TreeSub-to-Sub (connect-tree-inc-left T S₂) ⋆) ]ts) (connect-tree-inc-right T S₂)
exterior-treeSub (Join⊤ S₁ S₂) (PExt P) (Join⊤ T Sing⊤) = connect-tree (suspTreeSub (exterior-treeSub S₁ P T) [ connect-susp-inc-left (insertion-tree-size S₁ P T) _ ]ts) (connect-tree-inc-right (suspTree⊤ (insertion-tree S₁ P T)) S₂)
exterior-treeSub (Join⊤ S₁ S₂) (PShift P) T = connect-tree (connect-tree-inc-left (suspTree⊤ S₁) (insertion-tree S₂ P T)) (exterior-treeSub S₂ P T [ connect-susp-inc-right _ (insertion-tree-size S₂ P T) ]ts)

sub-from-insertion : (S : Tree⊤ n)
                   → (P : Path S)
                   → .⦃ bp : is-branching-path P ⦄
                   → (T : Tree⊤ m)
                   → .⦃ lh : has-linear-height (path-length P) T ⦄
                   → (σ : Sub (suc n) l A)
                   → (τ : Sub (suc m) l A)
                   → Sub (suc (insertion-tree-size S P T)) l A
sub-from-insertion (Join⊤ S₁ S₂) PHere T σ τ
  = sub-from-connect τ
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) ∘ (idSub≃ (connect-tree-to-ctx T S₂))
sub-from-insertion (Join⊤ S₁ S₂) (PExt P) (Join⊤ T Sing⊤) σ τ
  = sub-from-connect (unrestrict (sub-from-insertion S₁ P T (restrict (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂)) (getFst [ τ ]tm) (getSnd [ τ ]tm))
                                                             (restrict τ (getFst [ τ ]tm) (getSnd [ τ ]tm))))
                     (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂))
sub-from-insertion (Join⊤ S₁ S₂) (PShift P) T σ τ
  = sub-from-connect (σ ∘ connect-susp-inc-left (tree-size S₁) (tree-size S₂))
                     (sub-from-insertion S₂ P T (σ ∘ connect-susp-inc-right (tree-size S₁) (tree-size S₂)) τ)

treeSub-from-insertion : (S : Tree⊤ n)
                       → (P : Path S)
                       → .⦃ bp : is-branching-path P ⦄
                       → (T : Tree⊤ m)
                       → .⦃ lh : has-linear-height (path-length P) T ⦄
                       → (σ : TreeSub n l)
                       → (τ : TreeSub m l)
                       → TreeSub (insertion-tree-size S P T) l
treeSub-from-insertion S P T σ τ = insertion-tree {!!} {!!} {!!}
