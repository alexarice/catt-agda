{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Tree where

open import Catt.Syntax
-- open import Catt.Syntax.Properties
open import Catt.Syntax.SyntacticEquality
-- open import Catt.Globular
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
-- open import Catt.Suspension.Properties
open import Catt.Connection
-- open import Catt.Connection.Properties
open import Data.Nat
-- open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
-- open import Data.Vec

singleton-ctx : Ctx
singleton-ctx = ∅ , ⋆

singleton-pd : singleton-ctx ⊢pd₀ 0
singleton-pd = Finish Base

data Tree : Set where
  Sing : Tree
  Join : (S : Tree) → (T : Tree) → Tree

-- Extendability
n-extendable : ℕ → Tree → Set
n-extendable zero T = ⊤
n-extendable (suc n) Sing = ⊥
n-extendable (suc n) (Join S Sing) = n-extendable n S
n-extendable (suc n) (Join S T@(Join _ _)) = n-extendable (suc n) T

-- record N-Extendable (n : ℕ) (T : Tree) : Set where
--   field
--     n-Extendable : n-extendable n T

-- instance
--   .n-extendable-Z : {T : Tree} → N-Extendable zero T
--   n-extendable-Z = record { n-Extendable = tt }

--   .n-extendable-S : {S : Tree} → ⦃ N-Extendable n S ⦄ → N-Extendable (suc n) (Join S Sing)
--   n-extendable-S ⦃ x ⦄ = record { n-Extendable = N-Extendable.n-Extendable x }

--   .n-extendable-J : ∀ {S} {T} {T′} → ⦃ N-Extendable (suc n) (Join T T′) ⦄ → N-Extendable (suc n) (Join S (Join T T′))
--   n-extendable-J ⦃ x ⦄ = record { n-Extendable = N-Extendable.n-Extendable x }


extend-tree : (n : ℕ) → (T : Tree) → .⦃ n-extendable n T ⦄ → Tree
extend-tree zero Sing = Join Sing Sing
extend-tree zero (Join S Sing) = Join S (Join Sing Sing)
extend-tree zero (Join S T@(Join _ _)) = Join S (extend-tree zero T)
extend-tree (suc n) (Join S Sing) = Join (extend-tree n S) Sing
extend-tree (suc n) (Join S T@(Join _ _)) = Join S (extend-tree (suc n) T)


join-tree-preserves-extendable : (n : ℕ) → (S : Tree) → (T : Tree) → ⦃ n-extendable n T ⦄ → n-extendable n (Join S T)
join-tree-preserves-extendable zero S T = it
join-tree-preserves-extendable (suc n) S (Join _ _) = it

extended-tree-is-more-extendable : (n : ℕ) → (T : Tree) → ⦃ _ : n-extendable n T ⦄ → n-extendable (suc n) (extend-tree n T)
extended-tree-is-more-extendable zero Sing = it
extended-tree-is-more-extendable zero (Join S Sing) = it
extended-tree-is-more-extendable zero (Join S T@(Join _ _)) ⦃ x ⦄ = join-tree-preserves-extendable 1 S (extend-tree zero T) ⦃ extended-tree-is-more-extendable zero T ⦄
extended-tree-is-more-extendable (suc n) (Join S Sing) = extended-tree-is-more-extendable n S
extended-tree-is-more-extendable (suc n) (Join S T@(Join _ _)) = join-tree-preserves-extendable (suc (suc n)) S (extend-tree (suc n) T) ⦃ extended-tree-is-more-extendable (suc n) T ⦄

pred-n-extendable : (n : ℕ) → (T : Tree) → ⦃ n-extendable (suc n) T ⦄ → n-extendable n T
pred-n-extendable zero T = tt
pred-n-extendable (suc n) (Join S Sing) = pred-n-extendable n S
pred-n-extendable (suc n) (Join S T@(Join _ _)) = pred-n-extendable (suc n) T

-- Tree to pd conversion
tree-to-ctx : (T : Tree) → Ctx
tree-to-ctx-non-empty : (T : Tree) → NonZero′ (ctxLength (tree-to-ctx T))
tree-to-pd-dim : Tree → ℕ
tree-to-pd : (T : Tree) → tree-to-ctx T ⊢pd₀ tree-to-pd-dim T
tree-to-pdb-submax : (d : ℕ) → (T : Tree) → .⦃ ex : n-extendable d T ⦄ → ℕ
tree-to-pdb : (d : ℕ) → (T : Tree) → .⦃ ex : n-extendable d T ⦄ → tree-to-ctx T ⊢pd[ tree-to-pdb-submax d T ][ d ]

tree-to-ctx Sing = singleton-ctx
tree-to-ctx (Join S T) = connect-pdb (Restr (susp-pdb (tree-to-pdb zero S))) (tree-to-ctx T) ⦃ tree-to-ctx-non-empty T ⦄

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

tree-to-ctx-non-empty T = pd-is-non-empty (tree-to-pd T)

-- Pd to tree conversion
pdb-to-tree : Γ ⊢pd[ submax ][ d ] → Tree
pdb-to-tree-is-n-extendable : (pdb : Γ ⊢pd[ submax ][ d ]) → n-extendable d (pdb-to-tree pdb)

pdb-to-tree Base = Sing
pdb-to-tree (Extend {d = d} pdb) = extend-tree d (pdb-to-tree pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄
pdb-to-tree (Restr pdb) = pdb-to-tree pdb

pdb-to-tree-is-n-extendable Base = tt
pdb-to-tree-is-n-extendable (Extend {d = d} pdb) = extended-tree-is-more-extendable d (pdb-to-tree pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄
pdb-to-tree-is-n-extendable (Restr {d = d} pdb) = pred-n-extendable d (pdb-to-tree (Restr pdb)) ⦃ pdb-to-tree-is-n-extendable pdb ⦄

pd-to-tree : Γ ⊢pd₀ d → Tree
pd-to-tree (Finish pdb) = pdb-to-tree pdb
-- Tree to Pd to Tree

subst-pdb-tree : (pdb : Γ ⊢pd[ submax ][ d ]) → (p : Δ ≃c Γ) → pdb-to-tree (subst-pdb pdb p) ≡ pdb-to-tree pdb
subst-pdb-tree pdb p with ≃c-to-≡ p
... | refl = refl

pdb-to-tree-extend-pd-eq : (pdb : Γ ⊢pd[ submax ][ d ])
                         → (p : A ≃ty getFocusType pdb)
                         → (q : B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                         → pdb-to-tree (extend-pd-eq pdb p q) ≡ extend-tree d (pdb-to-tree pdb) ⦃ pdb-to-tree-is-n-extendable pdb ⦄
pdb-to-tree-extend-pd-eq pdb p q = subst-pdb-tree  (Extend pdb) (Add≃ (Add≃ refl≃c p) q)

extend-tree-eq : {S : Tree} → {T : Tree} → (p : S ≡ T) → .⦃ ex : n-extendable d S ⦄
               → extend-tree d S ≡ extend-tree d T ⦃ subst (n-extendable d) p ex ⦄
extend-tree-eq refl = refl

connect-tree : (S : Tree) → (T : Tree) → Tree
connect-tree Sing T = T
connect-tree (Join S S′) T = Join S (connect-tree S′ T)

connect-tree-unit-right : (T : Tree) → T ≡ connect-tree T Sing
connect-tree-unit-right Sing = refl
connect-tree-unit-right (Join S T) = cong (Join S) (connect-tree-unit-right T)

connect-tree-is-extendable : (n : ℕ) → (S : Tree) → (T : Tree) → ⦃ _ : n-extendable n T ⦄ → n-extendable n (connect-tree S T)
connect-tree-is-extendable n Sing T = it
connect-tree-is-extendable n (Join S S′) T = join-tree-preserves-extendable n S (connect-tree S′ T) ⦃ connect-tree-is-extendable n S′ T ⦄

join-extend-tree : (S : Tree)
                 → (T : Tree)
                 → .⦃ _ : n-extendable n T ⦄
                 → extend-tree n (Join S T) ⦃ join-tree-preserves-extendable n S T ⦄ ≡ Join S (extend-tree n T)
join-extend-tree {n = zero} S Sing = refl
join-extend-tree {n = zero} S (Join _ _) = refl
join-extend-tree {n = suc n} S (Join T Sing) = refl
join-extend-tree {n = suc n} S (Join T (Join _ _)) = refl

extend-connect-tree : (S : Tree)
                    → (T : Tree)
                    → .⦃ _ : n-extendable n T ⦄
                    → extend-tree n (connect-tree S T) ⦃ connect-tree-is-extendable n S T ⦄
                      ≡ connect-tree S (extend-tree n T)
extend-connect-tree Sing T = refl
extend-connect-tree {n = n} (Join S S′) T ⦃ ex ⦄ = let
  instance _ = connect-tree-is-extendable n S′ T
  in begin
  extend-tree n (connect-tree (Join S S′) T) ⦃ join-tree-preserves-extendable n S (connect-tree S′ T) ⦄
    ≡⟨ join-extend-tree S (connect-tree S′ T) ⟩
  Join S (extend-tree n (connect-tree S′ T))
    ≡⟨ cong (Join S) (extend-connect-tree S′ T) ⟩
  connect-tree (Join S S′) (extend-tree n T) ∎
  where
    open ≡-Reasoning

connect-pdb-tree-compat : (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → pdb-to-tree (connect-pdb-pdb pdb pdb2) ≡ connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2)
connect-pdb-tree-compat pdb Base = connect-tree-unit-right (pdb-to-tree (connect-pdb-pdb pdb Base))
connect-pdb-tree-compat {Γ = Γ} pdb (Extend {Γ = Γ′} pdb2) with pdb-is-non-empty pdb2
connect-pdb-tree-compat {Γ = Γ} pdb (Extend {Γ = Γ′ , A} {d = d} pdb2) | ne = let
  instance _ = pdb-to-tree-is-n-extendable (connect-pdb-pdb pdb pdb2)
  instance _ = pdb-to-tree-is-n-extendable pdb
  instance _ = pdb-to-tree-is-n-extendable pdb2
  instance _ = connect-tree-is-extendable d (pdb-to-tree pdb) (pdb-to-tree pdb2)
  in begin
  pdb-to-tree (extend-pd-eq (connect-pdb-pdb pdb pdb2)
                            (connect-pdb-foc-ty pdb pdb2)
                            (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm pdb2)
                                                              (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                            (lift-tm-≃ (connect-pdb-foc-tm pdb pdb2)))
                                  (trans≃ty (lift-subbed-ty-≃ (getFocusType pdb2)
                                                              (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                            (lift-ty-≃ (connect-pdb-foc-ty pdb pdb2)))
                                  (Var≃ refl)))
    ≡⟨ pdb-to-tree-extend-pd-eq (connect-pdb-pdb pdb pdb2)
                                (connect-pdb-foc-ty pdb pdb2)
                                (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm pdb2)
                                                                  (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                                (lift-tm-≃ (connect-pdb-foc-tm pdb pdb2)))
                                      (trans≃ty (lift-subbed-ty-≃ (getFocusType pdb2)
                                                                  (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                                (lift-ty-≃ (connect-pdb-foc-ty pdb pdb2)))
                                      (Var≃ refl)) ⟩
  extend-tree d (pdb-to-tree (connect-pdb-pdb pdb pdb2))
    ≡⟨ extend-tree-eq (connect-pdb-tree-compat pdb pdb2)
                      ⦃ pdb-to-tree-is-n-extendable (connect-pdb-pdb pdb pdb2) ⦄ ⟩
  extend-tree d (connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2))
    ≡⟨ extend-connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2) ⦃ pdb-to-tree-is-n-extendable pdb2 ⦄ ⟩
  connect-tree (pdb-to-tree pdb) (extend-tree _ (pdb-to-tree pdb2)) ∎
  where
    open ≡-Reasoning

connect-pdb-tree-compat pdb (Restr pdb2) = connect-pdb-tree-compat pdb pdb2

connect-pd-tree-compat : (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → pd-to-tree (connect-pd-pd pd pd2) ≡ connect-tree (pd-to-tree pd) (pd-to-tree pd2)
connect-pd-tree-compat (Finish pdb) (Finish pdb2) = connect-pdb-tree-compat pdb pdb2

susp-tree : Tree → Tree
susp-tree T = Join T Sing

susp-pdb-tree-compat : (pdb : Γ ⊢pd[ submax ][ d ]) → pdb-to-tree (susp-pdb pdb) ≡ susp-tree (pdb-to-tree pdb)
susp-pdb-tree-compat Base = refl
susp-pdb-tree-compat (Extend pdb) = let
  instance _ = pdb-to-tree-is-n-extendable (susp-pdb pdb)
  in begin
  pdb-to-tree (susp-pdb (Extend pdb)) ≡⟨⟩
  pdb-to-tree (extend-pd-eq (susp-pdb pdb) (susp-pdb-foc-ty pdb)
                            (Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm pdb))
                                            (lift-tm-≃ (susp-pdb-foc-tm pdb)))
                                  (trans≃ty (susp-ty-lift (getFocusType pdb))
                                            (lift-ty-≃ (susp-pdb-foc-ty pdb)))
                                  (Var≃ refl)))
      ≡⟨ pdb-to-tree-extend-pd-eq (susp-pdb pdb) (susp-pdb-foc-ty pdb)
                                  (Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm pdb))
                                                  (lift-tm-≃ (susp-pdb-foc-tm pdb)))
                                        (trans≃ty (susp-ty-lift (getFocusType pdb))
                                                  (lift-ty-≃ (susp-pdb-foc-ty pdb)))
                                        (Var≃ refl)) ⟩
  extend-tree (suc _) (pdb-to-tree (susp-pdb pdb))
    ≡⟨ extend-tree-eq (susp-pdb-tree-compat pdb) ⟩
  susp-tree (pdb-to-tree (Extend pdb)) ∎
  where
    open ≡-Reasoning

susp-pdb-tree-compat (Restr pdb) = susp-pdb-tree-compat pdb

susp-pd-tree-compat : (pd : Γ ⊢pd₀ d) → pd-to-tree (susp-pd pd) ≡ susp-tree (pd-to-tree pd)
susp-pd-tree-compat (Finish pdb) = susp-pdb-tree-compat pdb

tree-to-pd-to-tree : (T : Tree) → pd-to-tree (tree-to-pd T) ≡ T
tree-to-pd-to-tree Sing = refl
tree-to-pd-to-tree (Join S T) = begin
  pd-to-tree (tree-to-pd (Join S T)) ≡⟨⟩
  pd-to-tree (connect-pd-pd (susp-pd (tree-to-pd S)) (tree-to-pd T))
    ≡⟨ connect-pd-tree-compat (susp-pd (tree-to-pd S)) (tree-to-pd T) ⟩
  connect-tree (pd-to-tree (susp-pd (tree-to-pd S))) (pd-to-tree (tree-to-pd T))
    ≡⟨ cong₂ connect-tree (trans (susp-pd-tree-compat (tree-to-pd S))
                                 (cong susp-tree (tree-to-pd-to-tree S)))
                          (tree-to-pd-to-tree T) ⟩
  connect-tree (susp-tree S) T ≡⟨⟩
  Join S T ∎
  where
    open ≡-Reasoning


-- Pd to tree to Pd


tree-to-ctx-extend-tree : (d : ℕ) → (T : Tree) → .⦃ _ : n-extendable d T ⦄ → tree-to-ctx (extend-tree d T) ≃c extend (tree-to-pdb d T)
tree-to-ctx-extend-tree zero Sing = refl≃c
tree-to-ctx-extend-tree zero (Join S Sing) = Add≃ (Add≃ refl≃c {!!}) {!!}
  -- rewrite ≃ty-to-≡ (⋆-is-only-1-d-ty {A = ty-base (getFocusType (susp-pdb (tree-to-pdb 0 S _)))})
        -- = ≃c-to-≡ (Add≃ refl≃c (Arr≃ refl≃tm ⋆-is-only-1-d-ty refl≃tm))
tree-to-ctx-extend-tree zero (Join S T@(Join _ _)) = {!!}
  -- rewrite tree-to-ctx-extend-tree zero T
  -- = ≃c-to-≡ (Add≃ (trans≃c (lem (tree-to-ctx T))
  --                          (Add≃ refl≃c
  --                                (reflexive≃ty (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S tt)))
  --                                                                  (tree-to-pdb 0 T tt)))))
  --                 (Arr≃ (trans≃tm (lem2 (getFocusTerm (tree-to-pdb 0 T tt))) (lift-tm-≃ (reflexive≃tm (connect-pdb-foc-tm (Restr (susp-pdb (tree-to-pdb 0 S tt))) (tree-to-pdb 0 T tt)))))
  --                       (trans≃ty (lem3 (getFocusType (tree-to-pdb 0 T tt))) (lift-ty-≃ (reflexive≃ty (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S tt))) (tree-to-pdb 0 T tt)))))
  --                       (trans≃tm (lem4 (tree-to-ctx T , getFocusType (tree-to-pdb 0 T tt))) (Var≃ refl))))
  -- where
  --   lem : (Δ : Ctx (suc n)) {A : Ty Δ m} → connect Γ t (Δ , A) ≃c (connect Γ t Δ) , A [ connect-inc-right Γ t Δ ]ty
  --   lem (Δ , B) = refl≃c

  --   lem2 : ∀ {d} {Δ : Ctx (suc n)} (t : Tm Δ d) {A : Ty Δ d′} → liftTerm t [ connect-inc-right Γ s (Δ , A) ]tm ≃tm liftTerm {A = A [ connect-inc-right Γ s Δ ]ty} (t [ connect-inc-right Γ s Δ ]tm)
  --   lem2 {Δ = Δ , B} t = lift-subbed-tm-≃ t (connect-inc-right _ _ (Δ , B))

  --   lem3 : ∀ {d} {Δ : Ctx (suc n)} (B : Ty Δ d) {A : Ty Δ d′} → liftType B [ connect-inc-right Γ s (Δ , A) ]ty ≃ty liftType {A = A [ connect-inc-right Γ s Δ ]ty} (B [ connect-inc-right Γ s Δ ]ty)
  --   lem3 {Δ = Δ , C} B = lift-subbed-ty-≃ B (connect-inc-right _ _ (Δ , C))

  --   lem4 : (Δ : Ctx (suc (suc n))) → _≃tm_ {Γ′ = connect Γ s Δ} (0V [ connect-inc-right Γ s Δ ]tm) 0V
  --   lem4 (Δ , A , B) = Var≃ refl

tree-to-ctx-extend-tree (suc d) (Join S Sing) = {!!}
  -- rewrite tree-to-ctx-extend-tree d S ex = ≃c-to-≡ (Add≃ (Add≃ refl≃c (reflexive≃ty (susp-pdb-foc-ty (tree-to-pdb d S ex)))) (Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm (tree-to-pdb d S ex))) (lift-tm-≃ (reflexive≃tm (susp-pdb-foc-tm (tree-to-pdb d S ex))))) (trans≃ty (susp-ty-lift (getFocusType (tree-to-pdb d S ex))) (lift-ty-≃ (reflexive≃ty (susp-pdb-foc-ty (tree-to-pdb d S ex))))) (Var≃ refl)))
tree-to-ctx-extend-tree (suc d) (Join S T@(Join T₁ _)) = {!!}
  -- rewrite tree-to-ctx-extend-tree (suc d) T ex
  -- = ≃c-to-≡ (Add≃ (trans≃c (lem (tree-to-ctx T))
  --                          (Add≃ refl≃c
  --                                (reflexive≃ty (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S tt)))
  --                                                                  (tree-to-pdb (suc d) T ex)))))
  --                 (Arr≃ (trans≃tm (lem2 (getFocusTerm (tree-to-pdb (suc d) T ex))) (lift-tm-≃ (reflexive≃tm (connect-pdb-foc-tm (Restr (susp-pdb (tree-to-pdb 0 S tt))) (tree-to-pdb (suc d) T ex)))))
  --                       (trans≃ty (lem3 (getFocusType (tree-to-pdb (suc d) T ex))) (lift-ty-≃ (reflexive≃ty (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S tt))) (tree-to-pdb (suc d) T ex)))))
  --                       (trans≃tm (lem4 (tree-to-ctx T , getFocusType (tree-to-pdb (suc d) T ex))) (Var≃ refl))))
  -- where
  --   lem : (Δ : Ctx (suc n)) {A : Ty Δ m} → connect Γ t (Δ , A) ≃c (connect Γ t Δ) , A [ connect-inc-right Γ t Δ ]ty
  --   lem (Δ , B) = refl≃c

  --   lem2 : ∀ {d} {Δ : Ctx (suc n)} (t : Tm Δ d) {A : Ty Δ d′} → liftTerm t [ connect-inc-right Γ s (Δ , A) ]tm ≃tm liftTerm {A = A [ connect-inc-right Γ s Δ ]ty} (t [ connect-inc-right Γ s Δ ]tm)
  --   lem2 {Δ = Δ , B} t = lift-subbed-tm-≃ t (connect-inc-right _ _ (Δ , B))

  --   lem3 : ∀ {d} {Δ : Ctx (suc n)} (B : Ty Δ d) {A : Ty Δ d′} → liftType B [ connect-inc-right Γ s (Δ , A) ]ty ≃ty liftType {A = A [ connect-inc-right Γ s Δ ]ty} (B [ connect-inc-right Γ s Δ ]ty)
  --   lem3 {Δ = Δ , C} B = lift-subbed-ty-≃ B (connect-inc-right _ _ (Δ , C))

  --   lem4 : (Δ : Ctx (suc (suc n))) → _≃tm_ {Γ′ = connect Γ s Δ} (0V [ connect-inc-right Γ s Δ ]tm) 0V
  --   lem4 (Δ , A , B) = Var≃ refl

{-
extend-lem : (pdb : Γ ⊢pd[ submax ][ d ]) → (pdb2 : Γ′ ⊢pd[ submax′ ][ d′ ]) → < pdb > ≡ < pdb2 > → extend pdb ≃c extend pdb2
extend-lem pdb .pdb refl = refl≃c

pdb-to-tree-to-ctx : (pdb : Γ ⊢pd[ submax ][ d ]) → tree-to-ctx (pdb-to-tree pdb) ≡ Γ
pdb-to-tree-to-ctx Base = refl
pdb-to-tree-to-ctx (Extend {d = d} pdb)
  = trans (tree-to-ctx-extend-tree d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)) (≃c-to-≡ (extend-lem (tree-to-pdb d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)) pdb (PDB-irrel < tree-to-pdb d (pdb-to-tree pdb) _ > < pdb > (reflexive≃c (pdb-to-tree-to-ctx pdb)) refl)))
pdb-to-tree-to-ctx (Restr pdb) = pdb-to-tree-to-ctx pdb

pd-to-tree-to-ctx : (pd : Γ ⊢pd₀ d) → tree-to-ctx (pd-to-tree pd) ≡ Γ
pd-to-tree-to-ctx (Finish pdb) = pdb-to-tree-to-ctx pdb

-- Ctx dimensions

tree-dim : (Tree n) → ℕ
tree-dim Sing = 0
tree-dim (Join S T) = suc (tree-dim S) ⊔ tree-dim T

tree-to-ctx-dim : (T : Tree n) → ctx-dim (tree-to-ctx T) ≡ suc (tree-dim T)
tree-to-ctx-dim Sing = refl
tree-to-ctx-dim (Join S T) = begin
  ctx-dim (connect-pdb (Restr (susp-pdb (tree-to-pdb zero S _))) (tree-to-ctx T)) ≡⟨ connect-pdb-ctx-dim (Restr (susp-pdb (tree-to-pdb zero S tt))) (tree-to-ctx T) ⟩
  ctx-dim (suspCtx (tree-to-ctx S)) ⊔ ctx-dim (tree-to-ctx T) ≡⟨ cong (_⊔ ctx-dim (tree-to-ctx T)) (ctx-susp-dim (tree-to-ctx S)) ⟩
  suc (ctx-dim (tree-to-ctx S)) ⊔ ctx-dim (tree-to-ctx T) ≡⟨ cong₂ (λ a b → suc a ⊔ b) (tree-to-ctx-dim S) (tree-to-ctx-dim T) ⟩
  suc (suc (tree-dim S) ⊔ tree-dim T) ∎
  where
    open ≡-Reasoning

pd-to-tree-dim : (pd : Γ ⊢pd₀ d) → suc (tree-dim (pd-to-tree pd)) ≡ ctx-dim Γ
pd-to-tree-dim {Γ = Γ} pd = begin
  suc (tree-dim (pd-to-tree pd)) ≡˘⟨ tree-to-ctx-dim (pd-to-tree pd) ⟩
  ctx-dim (tree-to-ctx (pd-to-tree pd)) ≡⟨ cong ctx-dim (pd-to-tree-to-ctx pd) ⟩
  ctx-dim Γ ∎
  where
    open ≡-Reasoning
-}
