{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Tree where

open import Catt.Syntax
open import Catt.Syntax.Bundles
-- open import Catt.Syntax.Properties
open import Catt.Syntax.SyntacticEquality
-- open import Catt.Globular
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Catt.Variables
import Relation.Binary.Reasoning.Setoid as Reasoning
-- open import Data.Vec

singleton-ctx : Ctx 1
singleton-ctx = ∅ , ⋆

singleton-pd : singleton-ctx ⊢pd₀ 0
singleton-pd = Finish Base

data Tree : ℕ → Set where
  Sing : Tree 0
  Join : (S : Tree n) → (T : Tree m) → Tree (m + (2 + n))

tree-size : Tree n → ℕ
tree-size {n = n} T = n

-- Extendability
n-extendable : ℕ → Tree n → Set
n-extendable zero T = ⊤
n-extendable (suc n) Sing = ⊥
n-extendable (suc n) (Join S Sing) = n-extendable n S
n-extendable (suc n) (Join S T@(Join _ _)) = n-extendable (suc n) T

extend-tree : (n : ℕ) → (T : Tree m) → .⦃ n-extendable n T ⦄ → Tree (2 + m)
extend-tree zero Sing = Join Sing Sing
extend-tree zero (Join S Sing) = Join S (Join Sing Sing)
extend-tree zero (Join S T@(Join _ _)) = Join S (extend-tree zero T)
extend-tree (suc n) (Join S Sing) = Join (extend-tree n S) Sing
extend-tree (suc n) (Join S T@(Join _ _)) = Join S (extend-tree (suc n) T)

join-tree-preserves-extendable : (n : ℕ) → (S : Tree m) → (T : Tree m′) → ⦃ n-extendable n T ⦄ → n-extendable n (Join S T)
join-tree-preserves-extendable zero S T = it
join-tree-preserves-extendable (suc n) S (Join _ _) = it

extended-tree-is-more-extendable : (n : ℕ) → (T : Tree m) → ⦃ _ : n-extendable n T ⦄ → n-extendable (suc n) (extend-tree n T)
extended-tree-is-more-extendable zero Sing = it
extended-tree-is-more-extendable zero (Join S Sing) = it
extended-tree-is-more-extendable zero (Join S T@(Join _ _)) ⦃ x ⦄ = join-tree-preserves-extendable 1 S (extend-tree zero T) ⦃ extended-tree-is-more-extendable zero T ⦄
extended-tree-is-more-extendable (suc n) (Join S Sing) = extended-tree-is-more-extendable n S
extended-tree-is-more-extendable (suc n) (Join S T@(Join _ _)) = join-tree-preserves-extendable (suc (suc n)) S (extend-tree (suc n) T) ⦃ extended-tree-is-more-extendable (suc n) T ⦄

pred-n-extendable : (n : ℕ) → (T : Tree m) → ⦃ n-extendable (suc n) T ⦄ → n-extendable n T
pred-n-extendable zero T = tt
pred-n-extendable (suc n) (Join S Sing) = pred-n-extendable n S
pred-n-extendable (suc n) (Join S T@(Join _ _)) = pred-n-extendable (suc n) T

-- Tree to pd conversion
tree-to-ctx : (T : Tree m) → Ctx (suc m)
tree-to-pd-dim : Tree n → ℕ
tree-to-pd : (T : Tree n) → tree-to-ctx T ⊢pd₀ tree-to-pd-dim T
tree-to-pdb-submax : (d : ℕ) → (T : Tree n) → .⦃ n-extendable d T ⦄ → ℕ
tree-to-pdb : (d : ℕ) → (T : Tree n) → .⦃ _ : n-extendable d T ⦄ → tree-to-ctx T ⊢pd[ tree-to-pdb-submax d T ][ d ]

tree-to-ctx Sing = singleton-ctx
tree-to-ctx (Join S T) = connect-pdb (Restr (susp-pdb (tree-to-pdb zero S))) (tree-to-ctx T)

tree-to-pdb-submax zero Sing = zero
tree-to-pdb-submax zero (Join S T) = new-submax (Restr (susp-pdb (tree-to-pdb zero S))) (tree-to-pdb zero T)
tree-to-pdb-submax (suc d) (Join S Sing) = tree-to-pdb-submax d S
tree-to-pdb-submax (suc d) (Join S T@(Join _ _)) = new-submax (Restr (susp-pdb (tree-to-pdb zero S))) (tree-to-pdb (suc d) T)

tree-to-pdb zero Sing = Base
tree-to-pdb zero (Join S T) = connect-pdb-pdb (Restr (susp-pdb (tree-to-pdb zero S))) (tree-to-pdb zero T)
tree-to-pdb (suc d) (Join S Sing) = susp-pdb (tree-to-pdb d S)
tree-to-pdb (suc d) (Join S T@(Join _ _)) = connect-pdb-pdb (Restr (susp-pdb (tree-to-pdb zero S))) (tree-to-pdb (suc d) T)

tree-to-pd-dim T = tree-to-pdb-submax zero T

tree-to-pd T = Finish (tree-to-pdb zero T)

-- Pd to tree conversion
pdb-to-tree : {Γ : Ctx (suc n)} → Γ ⊢pd[ submax ][ d ] → Tree n
pdb-to-tree-is-n-extendable : (pdb : Γ ⊢pd[ submax ][ d ]) → n-extendable d (pdb-to-tree pdb)

pdb-to-tree Base = Sing
pdb-to-tree (Extend {d = d} pdb p q) = extend-tree d (pdb-to-tree pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄
pdb-to-tree (Restr pdb) = pdb-to-tree pdb

pdb-to-tree-is-n-extendable Base = tt
pdb-to-tree-is-n-extendable (Extend {d = d} pdb p q) = extended-tree-is-more-extendable d (pdb-to-tree pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄
pdb-to-tree-is-n-extendable (Restr {d = d} pdb) = pred-n-extendable d (pdb-to-tree (Restr pdb)) ⦃ pdb-to-tree-is-n-extendable pdb ⦄

pd-to-tree : {Γ : Ctx (suc n)} → Γ ⊢pd₀ d → Tree n
pd-to-tree (Finish pdb) = pdb-to-tree pdb
-- Tree to Pd to Tree

subst-extendable-≃ : (n : ℕ) → {S : Tree m} → {T : Tree m′} → S ≃ T → ⦃ n-extendable n S ⦄ → n-extendable n T
subst-extendable-≃ zero p = it
subst-extendable-≃ (suc n) (Join≃ p Sing≃) = subst-extendable-≃ n p
subst-extendable-≃ (suc n) (Join≃ p q@(Join≃ _ _)) = subst-extendable-≃ (suc n) q

-- subst-pdb-tree : (pdb : Γ ⊢pd[ submax ][ d ]) → (p : Δ ≃c Γ) → pdb-to-tree (subst-pdb pdb p) ≃ pdb-to-tree pdb
-- subst-pdb-tree pdb p with ≃c-to-≡ p
-- ... | refl = refl≃

-- pdb-to-tree-extend-pd-eq : (pdb : Γ ⊢pd[ submax ][ d ])
--                          → (p : A ≃ty getFocusType pdb)
--                          → (q : B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
--                          → pdb-to-tree (extend-pd-eq pdb p q) ≃ extend-tree d (pdb-to-tree pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄
-- pdb-to-tree-extend-pd-eq pdb p q = subst-pdb-tree (Extend pdb) (Add≃ (Add≃ refl≃c p) q)

extend-tree-eq : {S : Tree n} → {T : Tree m} → (p : S ≃ T) → .⦃ ex : n-extendable d S ⦄
               → extend-tree d S ≃ extend-tree d T ⦃ subst-extendable-≃ d p ⦄
extend-tree-eq {d = zero} Sing≃ = refl≃
extend-tree-eq {d = zero} (Join≃ p Sing≃) = Join≃ p refl≃
extend-tree-eq {d = zero} (Join≃ p q@(Join≃ _ _)) = Join≃ p (extend-tree-eq q)
extend-tree-eq {d = suc d} (Join≃ p Sing≃) = Join≃ (extend-tree-eq p) Sing≃
extend-tree-eq {d = suc d} (Join≃ p q@(Join≃ _ _)) = Join≃ p (extend-tree-eq q)

connect-tree-length : (S : Tree n) → (T : Tree m) → ℕ
connect-tree-length {m = m} Sing T = m
connect-tree-length (Join {x} S S′) T = connect-tree-length S′ T + (2 + x)

connect-tree : (S : Tree n) → (T : Tree m) → Tree (connect-tree-length S T)
connect-tree Sing T = T
connect-tree (Join S S′) T = Join S (connect-tree S′ T)

connect-tree-≃ : {S : Tree n} {S′ : Tree n′} {T : Tree m} {T′ : Tree m′} → S ≃ S′ → T ≃ T′ → connect-tree S T ≃ connect-tree S′ T′
connect-tree-≃ Sing≃ q = q
connect-tree-≃ (Join≃ p q) r = Join≃ p (connect-tree-≃ q r)

connect-tree-unit-right : (T : Tree n) → T ≃ connect-tree T Sing
connect-tree-unit-right Sing = refl≃
connect-tree-unit-right (Join S T) = Join≃ refl≃ (connect-tree-unit-right T)

connect-tree-is-extendable : (n : ℕ) → (S : Tree m) → (T : Tree m′) → ⦃ _ : n-extendable n T ⦄ → n-extendable n (connect-tree S T)
connect-tree-is-extendable n Sing T = it
connect-tree-is-extendable n (Join S S′) T = join-tree-preserves-extendable n S (connect-tree S′ T) ⦃ connect-tree-is-extendable n S′ T ⦄


join-extend-tree : (S : Tree m)
                 → (T : Tree m′)
                 → .⦃ _ : n-extendable n T ⦄
                 → extend-tree n (Join S T) ⦃ join-tree-preserves-extendable n S T ⦄ ≃ Join S (extend-tree n T)
join-extend-tree {n = zero} S Sing = refl≃
join-extend-tree {n = zero} S (Join _ _) = refl≃
join-extend-tree {n = suc n} S (Join T Sing) = refl≃
join-extend-tree {n = suc n} S (Join T (Join _ _)) = refl≃

extend-connect-tree : (S : Tree m)
                    → (T : Tree m′)
                    → .⦃ _ : n-extendable n T ⦄
                    → extend-tree n (connect-tree S T) ⦃ connect-tree-is-extendable n S T ⦄
                      ≃ connect-tree S (extend-tree n T)
extend-connect-tree Sing T = refl≃
extend-connect-tree {n = n} (Join S S′) T ⦃ ex ⦄ = let
  instance _ = connect-tree-is-extendable n S′ T
  in trans≃ (join-extend-tree S (connect-tree S′ T))
            (Join≃ refl≃ (extend-connect-tree S′ T))

connect-pdb-tree-compat : (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → pdb-to-tree (connect-pdb-pdb pdb pdb2) ≃ connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2)
connect-pdb-tree-compat pdb Base = connect-tree-unit-right (pdb-to-tree (connect-pdb-pdb pdb Base))
connect-pdb-tree-compat {Γ = Γ} pdb (Extend {Γ = Γ′ , A} {d = d} pdb2 p q) = let
  instance _ = pdb-to-tree-is-n-extendable (connect-pdb-pdb pdb pdb2)
  instance _ = pdb-to-tree-is-n-extendable pdb2
  in trans≃ (extend-tree-eq (connect-pdb-tree-compat pdb pdb2))
            (extend-connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2))
connect-pdb-tree-compat pdb (Restr pdb2) = connect-pdb-tree-compat pdb pdb2

connect-pd-tree-compat : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → pd-to-tree (connect-pd-pd pd pd2) ≃ connect-tree (pd-to-tree pd) (pd-to-tree pd2)
connect-pd-tree-compat (Finish pdb) (Finish pdb2) = connect-pdb-tree-compat pdb pdb2

susp-tree : Tree n → Tree (2 + n)
susp-tree T = Join T Sing

susp-tree-≃ : {S : Tree n} → {T : Tree m} → S ≃ T → susp-tree S ≃ susp-tree T
susp-tree-≃ p = Join≃ p Sing≃

susp-pdb-tree-compat : (pdb : Γ ⊢pd[ submax ][ d ]) → pdb-to-tree (susp-pdb pdb) ≃ susp-tree (pdb-to-tree pdb)
susp-pdb-tree-compat Base = refl≃
susp-pdb-tree-compat (Extend pdb p q) = let
  instance _ = pdb-to-tree-is-n-extendable (susp-pdb pdb)
  in extend-tree-eq (susp-pdb-tree-compat pdb)
susp-pdb-tree-compat (Restr pdb) = susp-pdb-tree-compat pdb

susp-pd-tree-compat : (pd : Γ ⊢pd₀ d) → pd-to-tree (susp-pd pd) ≃ susp-tree (pd-to-tree pd)
susp-pd-tree-compat (Finish pdb) = susp-pdb-tree-compat pdb


tree-to-pd-to-tree : (T : Tree n) → pd-to-tree (tree-to-pd T) ≡ T
tree-to-pd-to-tree T = ≃-to-≡ (γ T)
  where
    γ : (T : Tree n) → pd-to-tree (tree-to-pd T) ≃ T
    γ Sing = refl≃
    γ (Join S T)
      = trans≃ (connect-pd-tree-compat (susp-pd (tree-to-pd S)) (tree-to-pd T))
               (connect-tree-≃ (trans≃ (susp-pd-tree-compat (tree-to-pd S)) (susp-tree-≃ (γ S))) (γ T))


-- Pd to tree to Pd

tree-to-ctx-extend-tree : (d : ℕ) → (T : Tree n) → .⦃ _ : n-extendable d T ⦄ → tree-to-ctx (extend-tree d T) ≃c extend (tree-to-pdb d T)
tree-to-ctx-extend-tree zero Sing = refl≃c
tree-to-ctx-extend-tree zero (Join S Sing) = Add≃ (Add≃ refl≃c ⋆-is-only-0-d-ty) (Arr≃ (lift-tm-≃ refl≃tm) (lift-ty-≃ ⋆-is-only-0-d-ty) (Var≃ refl refl))
tree-to-ctx-extend-tree zero (Join S T@(Join _ _))
  = trans≃c (connect-≃ refl≃c refl≃tm (tree-to-ctx-extend-tree zero T))
            (Add≃ (trans≃c (lem (tree-to-ctx T))
                           (Add≃ refl≃c
                                 (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb zero S)))
                                                     (tree-to-pdb 0 T))))
                  (Arr≃ (trans≃tm (lift-subbed-tm-≃ (pd-focus-tm (tree-to-pd T)) (connect-pd-inc-right (susp-pd (tree-to-pd S)) _))
                                  (lift-tm-≃ (connect-pdb-foc-tm (Restr (susp-pdb (tree-to-pdb 0 S))) (tree-to-pdb 0 T))))
                        (trans≃ty (lift-subbed-ty-≃ (pd-focus-ty (tree-to-pd T)) (connect-pd-inc-right (susp-pd (tree-to-pd S)) _))
                                  (lift-ty-≃ (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S))) (tree-to-pdb 0 T))))
                        refl≃tm))
  where
    lem : (Δ : Ctx (suc n)) → {A : Ty (suc n) m} → connect Γ t (Δ , A) ≃c (connect Γ t Δ) , A [ connect-inc-right t n ]ty
    lem (Δ , B) = refl≃c

tree-to-ctx-extend-tree (suc d) (Join S Sing)
  = trans≃c (susp-ctx-≃ (tree-to-ctx-extend-tree d S))
            (Add≃ (Add≃ refl≃c
                        (susp-pdb-foc-ty (tree-to-pdb d S)))
                  (Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm (tree-to-pdb d S)))
                                  (lift-tm-≃ (susp-pdb-foc-tm (tree-to-pdb d S))))
                        (trans≃ty (susp-ty-lift (getFocusType (tree-to-pdb d S)))
                                  (lift-ty-≃ (susp-pdb-foc-ty (tree-to-pdb d S))))
                        (Var≃ refl refl)))
tree-to-ctx-extend-tree (suc d) (Join S T@(Join T₁ _))
  = trans≃c (connect-≃ refl≃c refl≃tm (tree-to-ctx-extend-tree (suc d) T))
            (Add≃ (trans≃c (lem (tree-to-ctx T))
                           (Add≃ refl≃c
                                 (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S)))
                                                     (tree-to-pdb (suc d) T))))
                  (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm (tree-to-pdb (suc d) T)) (connect-pd-inc-right (susp-pd (tree-to-pd S)) _))
                                  (lift-tm-≃ (connect-pdb-foc-tm (Restr (susp-pdb (tree-to-pdb 0 S)))
                                                                 (tree-to-pdb (suc d) T))))
                        (trans≃ty (lift-subbed-ty-≃ (getFocusType (tree-to-pdb (suc d) T)) (connect-pd-inc-right (susp-pd (tree-to-pd S)) _))
                                  (lift-ty-≃ (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S)))
                                                                 (tree-to-pdb (suc d) T))))
                        refl≃tm))
  where
    lem : (Δ : Ctx (suc n)) → {A : Ty (suc n) m} → connect Γ t (Δ , A) ≃c (connect Γ t Δ) , A [ connect-inc-right t n ]ty
    lem (Δ , B) = refl≃c

extend-lem : (pdb : Γ ⊢pd[ submax ][ d ]) → (pdb2 : Γ′ ⊢pd[ submax′ ][ d′ ]) → < pdb > ≡ < pdb2 > → extend pdb ≃c extend pdb2
extend-lem pdb .pdb refl = refl≃c

pdb-to-tree-to-ctx : (pdb : Γ ⊢pd[ submax ][ d ]) → tree-to-ctx (pdb-to-tree pdb) ≃c Γ
pdb-to-tree-to-ctx Base = refl≃c
pdb-to-tree-to-ctx (Extend {d = d} pdb p q) = let
  instance _ = pdb-to-tree-is-n-extendable pdb
  in trans≃c (tree-to-ctx-extend-tree d (pdb-to-tree pdb)) (trans≃c (extend-lem (tree-to-pdb d (pdb-to-tree pdb)) pdb (PDB-irrel < tree-to-pdb d (pdb-to-tree pdb) > < pdb > (pdb-to-tree-to-ctx pdb) refl)) (sym≃c (Add≃ (Add≃ refl≃c p) q)))
pdb-to-tree-to-ctx (Restr pdb) = pdb-to-tree-to-ctx pdb

pd-to-tree-to-ctx : (pd : Γ ⊢pd₀ d) → tree-to-ctx (pd-to-tree pd) ≃c Γ
pd-to-tree-to-ctx (Finish pdb) = pdb-to-tree-to-ctx pdb

-- Ctx dimensions

tree-dim : (Tree n) → ℕ
tree-dim Sing = 0
tree-dim (Join S T) = suc (tree-dim S) ⊔ tree-dim T

connect-tree-to-ctx : (S : Tree n) → (T : Tree m)
                    → tree-to-ctx (connect-tree S T) ≃c connect-pd (tree-to-pd S) (tree-to-ctx T)
connect-tree-to-ctx Sing T = sym≃c (connect-pdb-left-unit (tree-to-ctx T))
connect-tree-to-ctx (Join S S₁) T = begin
  < connect-pd (susp-pd (tree-to-pd S)) (tree-to-ctx (connect-tree S₁ T)) >c
    ≈⟨ connect-≃ refl≃c refl≃tm (connect-tree-to-ctx S₁ T) ⟩
  < connect-pd (susp-pd (tree-to-pd S)) (connect-pd (tree-to-pd S₁) (tree-to-ctx T)) >c
    ≈˘⟨ connect-pd-assoc (susp-pd (tree-to-pd S)) (tree-to-pd S₁) (tree-to-ctx T) ⟩
  < connect-pd (connect-pd-pd (susp-pd (tree-to-pd S)) (tree-to-pd S₁)) (tree-to-ctx T) >c ∎
  where
    open Reasoning ctx-setoid
