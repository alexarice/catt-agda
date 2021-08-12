{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Tree where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Patterns
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
open import Catt.Connection
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality

singleton-ctx : Ctx 1 1
singleton-ctx = ∅ , ⋆

singleton-pd : singleton-ctx ⊢pd₀ 0
singleton-pd = Finish Base

data Tree : Set where
  Sing : Tree
  Join : (S : Tree) → (T : Tree) → Tree

-- Tree to pd conversion
tree-to-ctx-len-1 : Tree → ℕ
tree-to-ctx-dim : Tree → ℕ
tree-to-ctx : (T : Tree) → Ctx (suc (tree-to-ctx-len-1 T)) (tree-to-ctx-dim T)
tree-to-pd-dim : Tree → ℕ
tree-to-pd : (T : Tree) → tree-to-ctx T ⊢pd₀ tree-to-pd-dim T

tree-to-ctx-len-1 Sing = 0
tree-to-ctx-len-1 (Join S T) = suc (suc (tree-to-ctx-len-1 T + tree-to-ctx-len-1 S))

tree-to-ctx-dim Sing = 1
tree-to-ctx-dim (Join S T) = connect-dim (tree-to-ctx S) (pd-focus-tm (tree-to-pd S)) (suspCtx (tree-to-ctx T))

tree-to-ctx Sing = singleton-ctx
tree-to-ctx (Join S T) = connect-pd (tree-to-pd S) (suspCtx (tree-to-ctx T))

tree-to-pd-dim Sing = 0
tree-to-pd-dim (Join S T) = connected-dim (tree-to-pd S) (susp-pd (tree-to-pd T))

tree-to-pd Sing = singleton-pd
tree-to-pd (Join S T) = connect-pd-pd (tree-to-pd S) (susp-pd (tree-to-pd T))

-- Pd to tree conversion
n-extendable : ℕ → Tree → Set
n-extendable zero T = ⊤
n-extendable (suc n) Sing = ⊥
n-extendable (suc n) (Join S T) = n-extendable n T

extend-tree : (n : ℕ) → (T : Tree) → .(n-extendable n T) → Tree
extend-tree zero T p = Join T Sing
extend-tree (suc n) (Join S T) p = Join S (extend-tree n T p)

extended-tree-is-more-extendable : (n : ℕ) → (T : Tree) → (p : n-extendable n T) → n-extendable (suc n) (extend-tree n T p)
extended-tree-is-more-extendable zero T p = tt
extended-tree-is-more-extendable (suc n) (Join S T) p = extended-tree-is-more-extendable n T p

pred-n-extendable : (n : ℕ) → (T : Tree) → n-extendable (suc n) T → n-extendable n T
pred-n-extendable zero T p = tt
pred-n-extendable (suc n) (Join S T) p = pred-n-extendable n T p

pdb-to-tree : Γ ⊢pd[ submax ][ d ] → Tree
pdb-to-tree-is-n-extendable : (pdb : Γ ⊢pd[ submax ][ d ]) → n-extendable d (pdb-to-tree pdb)

pdb-to-tree Base = Sing
pdb-to-tree (Extend {d = d} pdb) = extend-tree d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)
pdb-to-tree (Restr pdb) = pdb-to-tree pdb

pdb-to-tree-is-n-extendable Base = tt
pdb-to-tree-is-n-extendable (Extend {d = d} pdb) = extended-tree-is-more-extendable d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)
pdb-to-tree-is-n-extendable (Restr {d = d} pdb) = pred-n-extendable d (pdb-to-tree (Restr pdb)) (pdb-to-tree-is-n-extendable pdb)

pd-to-tree : Γ ⊢pd₀ d → Tree
pd-to-tree (Finish pdb) = pdb-to-tree pdb

-- Tree to Pd to Tree

pdb-to-tree-extend-pd : (pdb : Γ ⊢pd[ submax ][ d ]) → pdb-to-tree (Extend pdb) ≡ extend-tree d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)
pdb-to-tree-extend-pd {submax = zero} pdb = refl
pdb-to-tree-extend-pd {submax = suc submax} pdb = refl

pdb-to-tree-extend-pd-eq : (pdb : Γ ⊢pd[ submax ][ d ])
                         → (p : A ≡ getFocusType pdb)
                         → (q : B ≡ liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                         → pdb-to-tree (extend-pd-eq pdb p q) ≡ extend-tree d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)
pdb-to-tree-extend-pd-eq pdb refl refl = pdb-to-tree-extend-pd pdb

extend-tree-eq : (S T : Tree) → (p : S ≡ T) → (ex : n-extendable d S)
               → extend-tree d S ex ≡ extend-tree d T (subst (n-extendable d) p ex)
extend-tree-eq S .S refl ex = refl

connect-tree : (S T : Tree) → Tree
connect-tree S Sing = S
connect-tree S (Join T T′) = Join (connect-tree S T) T′

connect-tree-unit-right : (T : Tree) → T ≡ connect-tree T Sing
connect-tree-unit-right T = refl

connect-tree-is-extendable : (n : ℕ) → (S T : Tree) → n-extendable n T → n-extendable n (connect-tree S T)
connect-tree-is-extendable zero S T ex = tt
connect-tree-is-extendable (suc n) S (Join T T′) ex = ex

extend-connect-tree : (S T : Tree)
                    → (ex : n-extendable n T)
                    → extend-tree n (connect-tree S T) (connect-tree-is-extendable n S T ex)
                      ≡ connect-tree S (extend-tree n T ex)
extend-connect-tree {n = zero} S T ex = refl
extend-connect-tree {n = suc n} S (Join T T′) ex = refl

connect-pdb-tree-compat : (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → pdb-to-tree (connect-pdb-pdb pdb pdb2) ≡ connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2)
connect-pdb-tree-compat pdb Base = refl
connect-pdb-tree-compat {Γ = Γ} pdb (Extend {Γ = Γ′ , A} pdb2)
  = trans (pdb-to-tree-extend-pd-eq
            (connect-pdb-pdb pdb pdb2)
            (connect-pdb-foc-ty pdb pdb2)
            (arr-equality (trans (lift-subbed-tm (getFocusTerm pdb2)
                                                 (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                 (cong liftTerm (connect-pdb-foc-tm pdb pdb2)))
                          (trans (lift-subbed-ty (getFocusType pdb2)
                                                 (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                 (cong liftType (connect-pdb-foc-ty pdb pdb2)))
                          refl))
          (trans (extend-tree-eq (pdb-to-tree (connect-pdb-pdb pdb pdb2))
                                 (connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2))
                                 (connect-pdb-tree-compat pdb pdb2)
                                 (pdb-to-tree-is-n-extendable (connect-pdb-pdb pdb pdb2)))
                 (extend-connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2) (pdb-to-tree-is-n-extendable pdb2)))
connect-pdb-tree-compat pdb (Restr pdb2) = connect-pdb-tree-compat pdb pdb2

connect-pd-tree-compat : (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → pd-to-tree (connect-pd-pd pd pd2) ≡ connect-tree (pd-to-tree pd) (pd-to-tree pd2)
connect-pd-tree-compat (Finish pdb) (Finish pdb2) = connect-pdb-tree-compat pdb pdb2

susp-tree : Tree → Tree
susp-tree T = Join Sing T

susp-pdb-tree-compat : (pdb : Γ ⊢pd[ submax ][ d ]) → pdb-to-tree (susp-pdb pdb) ≡ susp-tree (pdb-to-tree pdb)
susp-pdb-tree-compat Base = refl
susp-pdb-tree-compat (Extend pdb)
  = trans (pdb-to-tree-extend-pd-eq
            (susp-pdb pdb)
            (susp-pdb-foc-ty pdb)
            (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
                                 (cong liftTerm (susp-pdb-foc-tm pdb)))
                          (trans (suspLiftTy (getFocusType pdb))
                                 (cong liftType (susp-pdb-foc-ty pdb)))
                          refl))
          (extend-tree-eq (pdb-to-tree (susp-pdb pdb))
                          (susp-tree (pdb-to-tree pdb))
                          (susp-pdb-tree-compat pdb)
                          (pdb-to-tree-is-n-extendable (susp-pdb pdb)))
susp-pdb-tree-compat (Restr pdb) = susp-pdb-tree-compat pdb

susp-pd-tree-compat : (pd : Γ ⊢pd₀ d) → pd-to-tree (susp-pd pd) ≡ susp-tree (pd-to-tree pd)
susp-pd-tree-compat (Finish pdb) = susp-pdb-tree-compat pdb

tree-to-pd-to-tree : (T : Tree) → pd-to-tree (tree-to-pd T) ≡ T
tree-to-pd-to-tree Sing = refl
tree-to-pd-to-tree (Join S T)
  = trans (connect-pd-tree-compat (tree-to-pd S) (susp-pd (tree-to-pd T)))
          (cong₂ connect-tree
                 (tree-to-pd-to-tree S)
                 (trans (susp-pd-tree-compat (tree-to-pd T))
                        (cong susp-tree (tree-to-pd-to-tree T))))
