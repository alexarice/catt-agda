{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Tree where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Patterns
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Vec

singleton-ctx : Ctx 1
singleton-ctx = ∅ , ⋆

singleton-pd : singleton-ctx ⊢pd₀ 0
singleton-pd = Finish Base

data Tree : ℕ → Set where
  Sing : Tree 0
  Join : (S : Tree n) → (T : Tree m) → Tree (m + suc (suc n))

-- Extendability
n-extendable : ℕ → Tree n → Set
n-extendable zero T = ⊤
n-extendable (suc n) Sing = ⊥
n-extendable (suc n) (Join S Sing) = n-extendable n S
n-extendable (suc n) (Join S T@(Join _ _)) = n-extendable (suc n) T

extend-tree : (n : ℕ) → (T : Tree m) → .(n-extendable n T) → Tree (suc (suc m))
extend-tree zero Sing p = Join Sing Sing
extend-tree zero (Join S Sing) p = Join S (Join Sing Sing)
extend-tree zero (Join S T@(Join _ _)) p = Join S (extend-tree zero T p)
extend-tree (suc n) (Join S Sing) p = Join (extend-tree n S p) Sing
extend-tree (suc n) (Join S T@(Join _ _)) p = Join S (extend-tree (suc n) T p)

join-tree-preserves-extendable : (n : ℕ) → (S : Tree m) → (T : Tree m′) → (p : n-extendable n T) → n-extendable n (Join S T)
join-tree-preserves-extendable zero S T p = tt
join-tree-preserves-extendable (suc n) S T@(Join _ _) p = p

extended-tree-is-more-extendable : (n : ℕ) → (T : Tree m) → (p : n-extendable n T) → n-extendable (suc n) (extend-tree n T p)
extended-tree-is-more-extendable zero Sing p = tt
extended-tree-is-more-extendable zero (Join S Sing) p = tt
extended-tree-is-more-extendable zero (Join S T@(Join _ _)) p = join-tree-preserves-extendable 1 S (extend-tree zero T p) (extended-tree-is-more-extendable zero T p)
extended-tree-is-more-extendable (suc n) (Join S Sing) p = extended-tree-is-more-extendable n S p
extended-tree-is-more-extendable (suc n) (Join S T@(Join _ _)) p = join-tree-preserves-extendable (suc (suc n)) S (extend-tree (suc n) T p) (extended-tree-is-more-extendable (suc n) T p)

pred-n-extendable : (n : ℕ) → (T : Tree m) → n-extendable (suc n) T → n-extendable n T
pred-n-extendable zero T p = tt
pred-n-extendable (suc n) (Join S Sing) p = pred-n-extendable n S p
pred-n-extendable (suc n) (Join S T@(Join _ _)) p = pred-n-extendable (suc n) T p


-- Tree to pd conversion
tree-to-ctx : (T : Tree n) → Ctx (suc n)
tree-to-pd-dim : Tree n → ℕ
tree-to-pd : (T : Tree n) → tree-to-ctx T ⊢pd₀ tree-to-pd-dim T
tree-to-pdb-submax : (d : ℕ) → (T : Tree n) → .(ex : n-extendable d T) → ℕ
tree-to-pdb : (d : ℕ) → (T : Tree n) → .(ex : n-extendable d T) → tree-to-ctx T ⊢pd[ tree-to-pdb-submax d T ex ][ d ]

tree-to-ctx Sing = singleton-ctx
tree-to-ctx (Join S T) = connect-pdb (Restr (susp-pdb (tree-to-pdb zero S tt))) (tree-to-ctx T)

tree-to-pdb-submax zero Sing ex = zero
tree-to-pdb-submax zero (Join S T) ex = new-submax (Restr (susp-pdb (tree-to-pdb zero S ex))) (tree-to-pdb zero T ex)
tree-to-pdb-submax (suc d) (Join S Sing) ex = tree-to-pdb-submax d S ex
tree-to-pdb-submax (suc d) (Join S T@(Join _ _)) ex = new-submax (Restr (susp-pdb (tree-to-pdb zero S tt))) (tree-to-pdb (suc d) T ex)

tree-to-pdb zero Sing ex = Base
tree-to-pdb zero (Join S T) ex = connect-pdb-pdb (Restr (susp-pdb (tree-to-pdb zero S tt))) (tree-to-pdb zero T ex)
tree-to-pdb (suc d) (Join S Sing) ex = susp-pdb (tree-to-pdb d S ex)
tree-to-pdb (suc d) (Join S T@(Join _ _)) ex = connect-pdb-pdb (Restr (susp-pdb (tree-to-pdb zero S tt))) (tree-to-pdb (suc d) T ex)

tree-to-pd-dim T = tree-to-pdb-submax zero T tt

tree-to-pd T = Finish (tree-to-pdb zero T tt)

-- Pd to tree conversion
pdb-to-tree : {Γ : Ctx (suc n)} → Γ ⊢pd[ submax ][ d ] → Tree n
pdb-to-tree-is-n-extendable : (pdb : Γ ⊢pd[ submax ][ d ]) → n-extendable d (pdb-to-tree pdb)

pdb-to-tree Base = Sing
pdb-to-tree (Extend {d = d} pdb) = extend-tree d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)
pdb-to-tree (Restr pdb) = pdb-to-tree pdb

pdb-to-tree-is-n-extendable Base = tt
pdb-to-tree-is-n-extendable (Extend {d = d} pdb) = extended-tree-is-more-extendable d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)
pdb-to-tree-is-n-extendable (Restr {d = d} pdb) = pred-n-extendable d (pdb-to-tree (Restr pdb)) (pdb-to-tree-is-n-extendable pdb)

pd-to-tree : {Γ : Ctx (suc n)} → Γ ⊢pd₀ d → Tree n
pd-to-tree (Finish pdb) = pdb-to-tree pdb

-- Tree to Pd to Tree

data _≃_ : Tree n → Tree m → Set where
  Sing≃ : Sing ≃ Sing
  Join≃ : {S : Tree n} → {S′ : Tree n′} → {T : Tree m} → {T′ : Tree m′} → S ≃ S′ → T ≃ T′ → Join S T ≃ Join S′ T′

refl≃ : {T : Tree n} → T ≃ T
refl≃ {T = Sing} = Sing≃
refl≃ {T = Join S T} = Join≃ refl≃ refl≃

trans≃ : {S : Tree n} → {T : Tree m} → {U : Tree m′} → S ≃ T → T ≃ U → S ≃ U
trans≃ Sing≃ Sing≃ = Sing≃
trans≃ (Join≃ p q) (Join≃ r s) = Join≃ (trans≃ p r) (trans≃ q s)

subst-extendable-≃ : (n : ℕ) → {S : Tree m} → {T : Tree m′} → S ≃ T → n-extendable n S → n-extendable n T
subst-extendable-≃ zero p ex = ex
subst-extendable-≃ (suc n) (Join≃ p Sing≃) ex = subst-extendable-≃ n p ex
subst-extendable-≃ (suc n) (Join≃ p q@(Join≃ _ _)) ex = subst-extendable-≃ (suc n) q ex

≃-to-same-n : {S : Tree n} → {T : Tree m} → S ≃ T → n ≡ m
≃-to-same-n Sing≃ = refl
≃-to-same-n (Join≃ p q) = cong₂ (λ a b → (a + suc (suc b))) (≃-to-same-n q) (≃-to-same-n p)

≃-to-≡ : {S T : Tree n} → S ≃ T → S ≡ T
≃-to-≡ {S = S} {T = T} q = subst (λ - → subst Tree - S ≡ T) (≡-irrelevant (≃-to-same-n q) refl) (γ q)
  where
    subst-Tree : (p : n ≡ n′) → (q : m ≡ m′) → (S : Tree n) → (T : Tree m) → subst Tree (cong₂ (λ a b → (a + suc (suc b))) q p) (Join S T) ≡ Join (subst Tree p S) (subst Tree q T)
    subst-Tree refl refl S T = refl
    γ : {S : Tree n} → {T : Tree m} → (p : S ≃ T) → subst Tree (≃-to-same-n p) S ≡ T
    γ Sing≃ = refl
    γ (Join≃ q r) = trans (subst-Tree (≃-to-same-n q) (≃-to-same-n r) _ _) (cong₂ Join (γ q) (γ r))



pdb-to-tree-extend-pd : (pdb : Γ ⊢pd[ submax ][ d ]) → pdb-to-tree (Extend pdb) ≡ extend-tree d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)
pdb-to-tree-extend-pd {submax = zero} pdb = refl
pdb-to-tree-extend-pd {submax = suc submax} pdb = refl

pdb-to-tree-extend-pd-eq : (pdb : Γ ⊢pd[ submax ][ d ])
                         → (p : A ≡ getFocusType pdb)
                         → (q : B ≡ liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                         → pdb-to-tree (extend-pd-eq pdb p q) ≃ extend-tree d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)
pdb-to-tree-extend-pd-eq pdb refl refl = refl≃

extend-tree-eq : {S : Tree n} → {T : Tree m} → (p : S ≃ T) → (ex : n-extendable d S)
               → extend-tree d S ex ≃ extend-tree d T (subst-extendable-≃ d p ex)
extend-tree-eq {d = zero} Sing≃ ex = refl≃
extend-tree-eq {d = zero} (Join≃ p Sing≃) ex = Join≃ p (refl≃)
extend-tree-eq {d = zero} (Join≃ p q@(Join≃ _ _)) ex = Join≃ p (extend-tree-eq q ex)
extend-tree-eq {d = suc d} (Join≃ p Sing≃) ex = Join≃ (extend-tree-eq p ex) Sing≃
extend-tree-eq {d = suc d} (Join≃ p q@(Join≃ _ _)) ex = Join≃ p (extend-tree-eq q ex)


connect-tree-length : (S : Tree n) → (T : Tree m) → ℕ
connect-tree-length {m = m} Sing T = m
connect-tree-length (Join {x} S S′) T = connect-tree-length S′ T + suc (suc x)

connect-tree : (S : Tree n) → (T : Tree m) → Tree (connect-tree-length S T)
connect-tree Sing T = T
connect-tree (Join S S′) T = Join S (connect-tree S′ T)


connect-tree-≃ : {S : Tree n} {S′ : Tree n′} {T : Tree m} {T′ : Tree m′} → S ≃ S′ → T ≃ T′ → connect-tree S T ≃ connect-tree S′ T′
connect-tree-≃ Sing≃ q = q
connect-tree-≃ (Join≃ p q) r = Join≃ p (connect-tree-≃ q r)

connect-tree-unit-right : (T : Tree n) → T ≃ connect-tree T Sing
connect-tree-unit-right Sing = Sing≃
connect-tree-unit-right (Join S T) = Join≃ refl≃ (connect-tree-unit-right T)

connect-tree-is-extendable : (n : ℕ) → (S : Tree m) → (T : Tree m′) → n-extendable n T → n-extendable n (connect-tree S T)
connect-tree-is-extendable n Sing T ex = ex
connect-tree-is-extendable n (Join S S′) T ex = join-tree-preserves-extendable n S (connect-tree S′ T) (connect-tree-is-extendable n S′ T ex)

join-extend-tree : (S : Tree m)
                 → (T : Tree m′)
                 → (ex : n-extendable n T)
                 → extend-tree n (Join S T) (join-tree-preserves-extendable n S T ex) ≃ Join S (extend-tree n T ex)
join-extend-tree {n = zero} S Sing ex = refl≃
join-extend-tree {n = zero} S (Join _ _) ex = refl≃
join-extend-tree {n = suc n} S (Join T Sing) ex = refl≃
join-extend-tree {n = suc n} S (Join T (Join _ _)) ex = refl≃

extend-connect-tree : (S : Tree m)
                    → (T : Tree m′)
                    → (ex : n-extendable n T)
                    → extend-tree n (connect-tree S T) (connect-tree-is-extendable n S T ex)
                      ≃ connect-tree S (extend-tree n T ex)
extend-connect-tree Sing T ex = refl≃
extend-connect-tree {n = n} (Join S S′) T ex = trans≃ (join-extend-tree S (connect-tree S′ T) (connect-tree-is-extendable n S′ T ex)) (Join≃ refl≃ (extend-connect-tree S′ T ex))

connect-pdb-tree-compat : (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → pdb-to-tree (connect-pdb-pdb pdb pdb2) ≃ connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2)
connect-pdb-tree-compat pdb Base = connect-tree-unit-right (pdb-to-tree (connect-pdb-pdb pdb Base))
connect-pdb-tree-compat {Γ = Γ} pdb (Extend {Γ = Γ′ , A} pdb2)
  = trans≃ (pdb-to-tree-extend-pd-eq
            (connect-pdb-pdb pdb pdb2)
            (connect-pdb-foc-ty pdb pdb2)
            (arr-equality (trans (lift-subbed-tm (getFocusTerm pdb2)
                                                 (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                 (cong liftTerm (connect-pdb-foc-tm pdb pdb2)))
                          (trans (lift-subbed-ty (getFocusType pdb2)
                                                 (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                 (cong liftType (connect-pdb-foc-ty pdb pdb2)))
                          refl))
          (trans≃ (extend-tree-eq (connect-pdb-tree-compat pdb pdb2)
                                  (pdb-to-tree-is-n-extendable (connect-pdb-pdb pdb pdb2)))
                  (extend-connect-tree (pdb-to-tree pdb) (pdb-to-tree pdb2) (pdb-to-tree-is-n-extendable pdb2)))
connect-pdb-tree-compat pdb (Restr pdb2) = connect-pdb-tree-compat pdb pdb2

connect-pd-tree-compat : (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → pd-to-tree (connect-pd-pd pd pd2) ≃ connect-tree (pd-to-tree pd) (pd-to-tree pd2)
connect-pd-tree-compat (Finish pdb) (Finish pdb2) = connect-pdb-tree-compat pdb pdb2



susp-tree : Tree n → Tree (suc (suc n))
susp-tree T = Join T Sing

susp-tree-≃ : {S : Tree n} → {T : Tree m} → S ≃ T → susp-tree S ≃ susp-tree T
susp-tree-≃ p = Join≃ p Sing≃


susp-pdb-tree-compat : (pdb : Γ ⊢pd[ submax ][ d ]) → pdb-to-tree (susp-pdb pdb) ≃ susp-tree (pdb-to-tree pdb)
susp-pdb-tree-compat Base = refl≃
susp-pdb-tree-compat (Extend pdb)
  = trans≃ (pdb-to-tree-extend-pd-eq
            (susp-pdb pdb)
            (susp-pdb-foc-ty pdb)
            (arr-equality (trans (suspLiftTm (getFocusTerm pdb))
                                 (cong liftTerm (susp-pdb-foc-tm pdb)))
                          (trans (suspLiftTy (getFocusType pdb))
                                 (cong liftType (susp-pdb-foc-ty pdb)))
                          refl))
          (extend-tree-eq (susp-pdb-tree-compat pdb)
                          (pdb-to-tree-is-n-extendable (susp-pdb pdb)))
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


tree-to-ctx-extend-tree : (d : ℕ) → (T : Tree n) → (ex : n-extendable d T) → tree-to-ctx (extend-tree d T ex) ≡ extend (tree-to-pdb d T ex)
tree-to-ctx-extend-tree zero Sing ex = refl
tree-to-ctx-extend-tree zero (Join S Sing) ex
  rewrite ≃ty-to-≡ (⋆-is-only-1-d-ty {A = ty-base (getFocusType (susp-pdb (tree-to-pdb 0 S _)))})
        = ≃c-to-≡ (Add≃ refl≃c (Arr≃ refl≃tm ⋆-is-only-1-d-ty refl≃tm))
tree-to-ctx-extend-tree zero (Join S T@(Join _ _)) ex
  rewrite tree-to-ctx-extend-tree zero T ex
  = ≃c-to-≡ (Add≃ (trans≃c (lem (tree-to-ctx T))
                           (Add≃ refl≃c
                                 (reflexive≃ty (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S tt)))
                                                                   (tree-to-pdb 0 T tt)))))
                  (Arr≃ (trans≃tm (lem2 (getFocusTerm (tree-to-pdb 0 T tt))) (lift-tm-≃ (reflexive≃tm (connect-pdb-foc-tm (Restr (susp-pdb (tree-to-pdb 0 S tt))) (tree-to-pdb 0 T tt)))))
                        (trans≃ty (lem3 (getFocusType (tree-to-pdb 0 T tt))) (lift-ty-≃ (reflexive≃ty (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S tt))) (tree-to-pdb 0 T tt)))))
                        (trans≃tm (lem4 (tree-to-ctx T , getFocusType (tree-to-pdb 0 T tt))) (Var≃ refl))))
  where
    lem : (Δ : Ctx (suc n)) {A : Ty Δ m} → connect Γ t (Δ , A) ≃c (connect Γ t Δ) , A [ connect-inc-right Γ t Δ ]ty
    lem (Δ , B) = refl≃c

    lem2 : ∀ {d} {Δ : Ctx (suc n)} (t : Tm Δ d) {A : Ty Δ d′} → liftTerm t [ connect-inc-right Γ s (Δ , A) ]tm ≃tm liftTerm {A = A [ connect-inc-right Γ s Δ ]ty} (t [ connect-inc-right Γ s Δ ]tm)
    lem2 {Δ = Δ , B} t = lift-subbed-tm-≃ t (connect-inc-right _ _ (Δ , B))

    lem3 : ∀ {d} {Δ : Ctx (suc n)} (B : Ty Δ d) {A : Ty Δ d′} → liftType B [ connect-inc-right Γ s (Δ , A) ]ty ≃ty liftType {A = A [ connect-inc-right Γ s Δ ]ty} (B [ connect-inc-right Γ s Δ ]ty)
    lem3 {Δ = Δ , C} B = lift-subbed-ty-≃ B (connect-inc-right _ _ (Δ , C))

    lem4 : (Δ : Ctx (suc (suc n))) → _≃tm_ {Γ′ = connect Γ s Δ} (0V [ connect-inc-right Γ s Δ ]tm) 0V
    lem4 (Δ , A , B) = Var≃ refl

tree-to-ctx-extend-tree (suc d) (Join S Sing) ex
  rewrite tree-to-ctx-extend-tree d S ex = ≃c-to-≡ (Add≃ (Add≃ refl≃c (reflexive≃ty (susp-pdb-foc-ty (tree-to-pdb d S ex)))) (Arr≃ (trans≃tm (susp-tm-lift (getFocusTerm (tree-to-pdb d S ex))) (lift-tm-≃ (reflexive≃tm (susp-pdb-foc-tm (tree-to-pdb d S ex))))) (trans≃ty (susp-ty-lift (getFocusType (tree-to-pdb d S ex))) (lift-ty-≃ (reflexive≃ty (susp-pdb-foc-ty (tree-to-pdb d S ex))))) (Var≃ refl)))
tree-to-ctx-extend-tree (suc d) (Join S T@(Join T₁ _)) ex
  rewrite tree-to-ctx-extend-tree (suc d) T ex
  = ≃c-to-≡ (Add≃ (trans≃c (lem (tree-to-ctx T))
                           (Add≃ refl≃c
                                 (reflexive≃ty (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S tt)))
                                                                   (tree-to-pdb (suc d) T ex)))))
                  (Arr≃ (trans≃tm (lem2 (getFocusTerm (tree-to-pdb (suc d) T ex))) (lift-tm-≃ (reflexive≃tm (connect-pdb-foc-tm (Restr (susp-pdb (tree-to-pdb 0 S tt))) (tree-to-pdb (suc d) T ex)))))
                        (trans≃ty (lem3 (getFocusType (tree-to-pdb (suc d) T ex))) (lift-ty-≃ (reflexive≃ty (connect-pdb-foc-ty (Restr (susp-pdb (tree-to-pdb 0 S tt))) (tree-to-pdb (suc d) T ex)))))
                        (trans≃tm (lem4 (tree-to-ctx T , getFocusType (tree-to-pdb (suc d) T ex))) (Var≃ refl))))
  where
    lem : (Δ : Ctx (suc n)) {A : Ty Δ m} → connect Γ t (Δ , A) ≃c (connect Γ t Δ) , A [ connect-inc-right Γ t Δ ]ty
    lem (Δ , B) = refl≃c

    lem2 : ∀ {d} {Δ : Ctx (suc n)} (t : Tm Δ d) {A : Ty Δ d′} → liftTerm t [ connect-inc-right Γ s (Δ , A) ]tm ≃tm liftTerm {A = A [ connect-inc-right Γ s Δ ]ty} (t [ connect-inc-right Γ s Δ ]tm)
    lem2 {Δ = Δ , B} t = lift-subbed-tm-≃ t (connect-inc-right _ _ (Δ , B))

    lem3 : ∀ {d} {Δ : Ctx (suc n)} (B : Ty Δ d) {A : Ty Δ d′} → liftType B [ connect-inc-right Γ s (Δ , A) ]ty ≃ty liftType {A = A [ connect-inc-right Γ s Δ ]ty} (B [ connect-inc-right Γ s Δ ]ty)
    lem3 {Δ = Δ , C} B = lift-subbed-ty-≃ B (connect-inc-right _ _ (Δ , C))

    lem4 : (Δ : Ctx (suc (suc n))) → _≃tm_ {Γ′ = connect Γ s Δ} (0V [ connect-inc-right Γ s Δ ]tm) 0V
    lem4 (Δ , A , B) = Var≃ refl

extend-lem : (pdb : Γ ⊢pd[ submax ][ d ]) → (pdb2 : Γ′ ⊢pd[ submax′ ][ d′ ]) → < pdb > ≡ < pdb2 > → extend pdb ≃c extend pdb2
extend-lem pdb .pdb refl = refl≃c

pdb-to-tree-to-ctx : (pdb : Γ ⊢pd[ submax ][ d ]) → tree-to-ctx (pdb-to-tree pdb) ≡ Γ
pdb-to-tree-to-ctx Base = refl
pdb-to-tree-to-ctx (Extend {d = d} pdb)
  = trans (tree-to-ctx-extend-tree d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)) (≃c-to-≡ (extend-lem (tree-to-pdb d (pdb-to-tree pdb) (pdb-to-tree-is-n-extendable pdb)) pdb (PDB-irrel < tree-to-pdb d (pdb-to-tree pdb) _ > < pdb > (reflexive≃c (pdb-to-tree-to-ctx pdb)) refl)))
pdb-to-tree-to-ctx (Restr pdb) = pdb-to-tree-to-ctx pdb

pd-to-tree-to-ctx : (pd : Γ ⊢pd₀ d) → tree-to-ctx (pd-to-tree pd) ≡ Γ
pd-to-tree-to-ctx (Finish pdb) = pdb-to-tree-to-ctx pdb
