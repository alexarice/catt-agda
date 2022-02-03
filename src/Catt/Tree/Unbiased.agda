{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Tree.Unbiased where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Globular
open import Relation.Nullary

unbiased-type : (d : ℕ) → (T : Tree n) → Ty (suc n)
unbiased-term : (d : ℕ) → (T : Tree n) → Tm (suc n)
unbiased-comp : (d : ℕ) → (T : Tree n) → Tm (suc n)

unbiased-term d T with is-linear-dec T
... | yes p = 0V
... | no p = unbiased-comp d T

unbiased-comp d T = Coh (tree-to-ctx T) (unbiased-type d T) idSub

unbiased-type zero T = ⋆
unbiased-type (suc d) T = (unbiased-term d (tree-bd d T) [ tree-inc d T false ]tm) ─⟨ unbiased-type d T ⟩⟶ (unbiased-term d (tree-bd d T) [ tree-inc d T true ]tm)

sub-from-linear-tree-unbiased : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → Sub (suc n) (suc m) (unbiased-type d T)
sub-from-linear-tree-unbiased Sing T d = ⟨ ⟨⟩ , (unbiased-comp d T) ⟩
sub-from-linear-tree-unbiased (Join S Sing) T d = unrestrict (sub-from-linear-tree-unbiased S T (suc d))

sub-from-linear-tree : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (t : Tm m) → (A : Ty m) → .(ty-dim A ≡ tree-dim S) → Sub (suc n) m ⋆
sub-from-linear-tree Sing t A p = ⟨ ⟨⟩ , t ⟩
sub-from-linear-tree (Join S Sing) t (s ─⟨ A ⟩⟶ s′) p = ⟨ ⟨ (sub-from-linear-tree S s A (trans (cong pred p) (max-lem (tree-dim S)))) , s′ ⟩ , t ⟩

identity : (t : Tm n) → (A : Ty n) → Tm n
identity t A = Coh (tree-to-ctx (n-disk (ty-dim A))) (unbiased-type (suc (ty-dim A)) (n-disk (ty-dim A))) (sub-from-linear-tree (n-disk (ty-dim A)) ⦃ n-disk-is-linear (ty-dim A) ⦄ t A (sym (tree-dim-n-disk (ty-dim A))))
