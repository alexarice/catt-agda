module Catt.Tree.Substitution where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Tree
open import Catt.Suspension
open import Catt.Connection

TreeSub : ℕ → ℕ → Set
TreeSub n m = Tree Tm m n

TreeSub-to-Sub : (T : TreeSub n m) → (A : Ty m) → Sub (suc n) m A
TreeSub-to-Sub (Sing x) A = ⟨ ⟨⟩ , x ⟩
TreeSub-to-Sub (Join x S T) A = sub-from-connect (unrestrict (TreeSub-to-Sub S (x ─⟨ A ⟩⟶ (first-label T)))) (TreeSub-to-Sub T A)

_[_]ts : TreeSub n m → (σ : Sub m l B) → TreeSub n l
Sing x [ σ ]ts = Sing (x [ σ ]tm)
Join x S T [ σ ]ts = Join (x [ σ ]tm) (S [ σ ]ts) (T [ σ ]ts)

suspTreeSub : TreeSub n m → TreeSub (2 + n) (2 + m)
suspTreeSub T = suspTree getFst getSnd (map-tree suspTm T)

idTreeSub : (T : Tree⊤ n) → TreeSub n (suc n)
idTreeSub Sing⊤ = Sing 0V
idTreeSub (Join _ S T) = Join (getFst [ connect-susp-inc-left _ _ ]tm)
                              (map-tree suspTm (idTreeSub S) [ connect-susp-inc-left _ _ ]ts)
                              (idTreeSub T [ connect-susp-inc-right _ _ ]ts)

sub-to-treeSub : (T : Tree⊤ n) → (σ : Sub (suc n) m A) → TreeSub n m
sub-to-treeSub T σ = idTreeSub T [ σ ]ts

connect-tree-inc-left : (S : Tree⊤ n) → (T : Tree⊤ m) → TreeSub n (suc (connect-tree-length S T))
connect-tree-inc-left Sing⊤ T = Sing (Var (fromℕ _))
connect-tree-inc-left (Join⊤ S₁ S₂) T = connect-tree ((suspTreeSub (idTreeSub S₁)) [ (connect-susp-inc-left _ (connect-tree-length S₂ T)) ]ts) (connect-tree-inc-left S₂ T [ connect-susp-inc-right _ (connect-tree-length S₂ T) ]ts)

connect-tree-inc-right : (S : Tree⊤ n) → (T : Tree⊤ m) → TreeSub m (suc (connect-tree-length S T))
connect-tree-inc-right Sing⊤ T = idTreeSub T
connect-tree-inc-right (Join⊤ S₁ S₂) T = (connect-tree-inc-right S₂ T) [ (connect-susp-inc-right _ (connect-tree-length S₂ T)) ]ts
