{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Unbiased where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Relation.Nullary
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false; not)
open import Data.Fin using (Fin; zero; suc; fromℕ)
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Syntax.SyntacticEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality
open import Catt.Discs

pdb-is-extends : (Γ ⊢pd[ submax ][ d ]) → Set
pdb-is-extends Base = ⊤
pdb-is-extends (Extend pdb p q) = pdb-is-extends pdb
pdb-is-extends (Restr pdb) = ⊥

pdb-is-linear : (Γ ⊢pd[ submax ][ d ]) → Set
pdb-is-linear Base = ⊤
pdb-is-linear (Extend pdb p q) = pdb-is-extends pdb
pdb-is-linear (Restr pdb) = pdb-is-linear pdb

pdb-is-extends-dec : (pdb : Γ ⊢pd[ submax ][ d ]) → Dec (pdb-is-extends pdb)
pdb-is-extends-dec Base = yes tt
pdb-is-extends-dec (Extend pdb p q) = pdb-is-extends-dec pdb
pdb-is-extends-dec (Restr pdb) = no (λ x → x)

pdb-is-linear-dec : (pdb : Γ ⊢pd[ submax ][ d ]) → Dec (pdb-is-linear pdb)
pdb-is-linear-dec Base = yes tt
pdb-is-linear-dec (Extend pdb p q) = pdb-is-extends-dec pdb
pdb-is-linear-dec (Restr pdb) = pdb-is-linear-dec pdb

pd-is-linear : Γ ⊢pd₀ d → Set
pd-is-linear (Finish pdb) = pdb-is-linear pdb

pd-is-linear-dec : (pd : Γ ⊢pd₀ d) → Dec (pd-is-linear pd)
pd-is-linear-dec (Finish pdb) = pdb-is-linear-dec pdb

unbiased-term : (Γ ⊢pd₀ d) → Tm (ctxLength Γ)
unbiased-type : (Γ ⊢pd₀ d) → Ty (ctxLength Γ) d

unbiased-term {Γ = Γ} pd with pd-is-linear-dec pd
... | yes p = 0V
... | no p = Coh Γ (unbiased-type pd) (idSub _)

unbiased-type {d = zero} pd = ⋆
unbiased-type {d = suc d} pd = (unbiased-term (pd-bd-pd pd) [ pd-src pd ]tm) ─⟨ unbiased-type (pd-bd-pd pd) [ pd-src pd ]ty ⟩⟶ (unbiased-term (pd-bd-pd pd) [ pd-tgt pd ]tm)

-- try two

tree-last-var : (T : Tree n) → Tm (suc (tree-size T))
tree-last-var Sing = Var zero
tree-last-var (Join S T) = tree-last-var T [ connect-pd-inc-right (susp-pd (tree-to-pd S)) (tree-size T) ]tm

tree-inc : (d : ℕ) → (T : Tree n) → (b : Bool) → Sub (suc (tree-bd-len d T)) (suc n)
tree-inc zero T false = ⟨ ⟨⟩ , (Var (fromℕ _)) ⟩
tree-inc zero T true = ⟨ ⟨⟩ , (tree-last-var T) ⟩
tree-inc (suc d) Sing b = ⟨ ⟨⟩ , 0V ⟩
tree-inc (suc d) (Join S T) b = sub-between-connect-pds (susp-pd (tree-to-pd (tree-bd d S))) (susp-pd (tree-to-pd S)) (suspSub (tree-inc d S b)) (tree-inc (suc d) T b)

tree-inc-preserve-fst-var : (d : ℕ) → (T : Tree n) → (b : Bool) → Var (fromℕ _) [ tree-inc (suc d) T b ]tm ≃tm Var {suc (tree-size T)} (fromℕ _)
tree-inc-preserve-fst-var d Sing b = refl≃tm
tree-inc-preserve-fst-var d (Join S T) b = sub-between-connect-pds-fst-var (susp-pd (tree-to-pd (tree-bd d S))) (susp-pd (tree-to-pd S)) (suspSub (tree-inc d S b)) (tree-inc (suc d) T b) (sym≃tm (susp-sub-preserve-getFst (tree-inc d S b)))

tree-inc-preserve-last-var : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-last-var (tree-bd (suc d) T) [ tree-inc (suc d) T b ]tm ≃tm tree-last-var T
tree-inc-preserve-last-var d Sing b = refl≃tm
tree-inc-preserve-last-var d (Join S T) b = begin
  < tree-last-var (tree-bd (suc d) T)
    [ connect-pd-inc-right (susp-pd (tree-to-pd (tree-bd d S))) (tree-size (tree-bd (suc d) T)) ]tm
    [ sub-between-connect-pds (susp-pd (tree-to-pd (tree-bd d S)))
                              (susp-pd (tree-to-pd S))
                              (suspSub (tree-inc d S b))
                              (tree-inc (suc d) T b) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (tree-last-var (tree-bd (suc d) T)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ sub-between-connect-pds (susp-pd (tree-to-pd (tree-bd d S)))
                              (susp-pd (tree-to-pd S))
                              (suspSub (tree-inc d S b))
                              (tree-inc (suc d) T b)
      ∘ connect-pd-inc-right (susp-pd (tree-to-pd (tree-bd d S))) (tree-size (tree-bd (suc d) T)) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var (tree-bd (suc d) T)})
       (sub-between-connect-pds-inc-right (susp-pd (tree-to-pd (tree-bd d S)))
                                          (susp-pd (tree-to-pd S))
                                          (suspSub (tree-inc d S b))
                                          (tree-inc (suc d) T b)
                                          (suspSub-preserve-focus-tm (tree-to-pd (tree-bd d S)) (tree-to-pd S) (tree-inc d S b))
                                          (tree-inc-preserve-fst-var d T b)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ connect-pd-inc-right (susp-pd (tree-to-pd S)) (tree-size T) ∘ tree-inc (suc d) T b ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var (tree-bd (suc d) T)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ tree-inc (suc d) T b ]tm
    [ connect-pd-inc-right (susp-pd (tree-to-pd S)) (tree-size T) ]tm >tm
    ≈⟨ sub-action-≃-tm (tree-inc-preserve-last-var d T b) refl≃s ⟩
  < tree-last-var T [ connect-pd-inc-right (susp-pd (tree-to-pd S)) (tree-size T) ]tm >tm ∎
  where
    open Reasoning tm-setoid

tree-bd-glob : (d₁ d₂ : ℕ) → (T : Tree n) → d₁ < d₂ → tree-bd d₁ (tree-bd d₂ T) ≃ tree-bd d₁ T
tree-bd-glob zero d₂ T p = Sing≃
tree-bd-glob (suc d₁) (suc d₂) Sing p = Sing≃
tree-bd-glob (suc d₁) (suc d₂) (Join S T) p = Join≃ (tree-bd-glob d₁ d₂ S (≤-pred p)) (tree-bd-glob (suc d₁) (suc d₂) T p)

tree-inc-glob : (d₁ d₂ : ℕ) → (T : Tree n) → (b₁ b₂ : Bool) → d₁ < d₂ → tree-inc d₂ T b₂ ∘ tree-inc d₁ (tree-bd d₂ T) b₁ ≃s tree-inc d₁ T b₁
tree-inc-glob zero (suc d₂) T false b₂ p = Ext≃ (Null≃ refl) (tree-inc-preserve-fst-var d₂ T b₂)
tree-inc-glob zero (suc d₂) T true b₂ p = Ext≃ (Null≃ refl) (tree-inc-preserve-last-var d₂ T b₂)
tree-inc-glob (suc d₁) (suc d₂) Sing b₁ b₂ p = refl≃s
tree-inc-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ p = trans≃s (sub-between-connect-pds-comp (susp-pd (tree-to-pd (tree-bd d₁ (tree-bd d₂ S)))) (susp-pd (tree-to-pd (tree-bd d₂ S))) (susp-pd (tree-to-pd S)) (suspSub (tree-inc d₁ (tree-bd d₂ S) b₁)) (tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁) (suspSub (tree-inc d₂ S b₂)) (tree-inc (suc d₂) T b₂) (suspSub-preserve-focus-tm (tree-to-pd (tree-bd d₂ S)) (tree-to-pd S) (tree-inc d₂ S b₂)) (tree-inc-preserve-fst-var d₂ T b₂)) (lem (susp-tree (tree-bd d₁ (tree-bd d₂ S))) (susp-tree (tree-bd d₁ S)) (susp-tree S) (suspSub (tree-inc d₂ S b₂) ∘ suspSub (tree-inc d₁ (tree-bd d₂ S) b₁)) (suspSub (tree-inc d₁ S b₁)) (tree-inc (suc d₂) T b₂ ∘ tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁) (tree-inc (suc d₁) T b₁) (susp-tree-≃ (tree-bd-glob d₁ d₂ S (≤-pred p))) (≃-to-same-n (tree-bd-glob (suc d₁) (suc d₂) T p)) (trans≃s (sym≃s (susp-functorial (tree-inc d₂ S b₂) (tree-inc d₁ (tree-bd d₂ S) b₁))) (susp-sub-≃ (tree-inc-glob d₁ d₂ S b₁ b₂ (≤-pred p)))) (tree-inc-glob (suc d₁) (suc d₂) T b₁ b₂ p))
  where
    lem : (S : Tree n) → (S′ : Tree n′) → (T : Tree l)
        → (σ : Sub (suc n) (suc l)) → (σ′ : Sub (suc n′) (suc l))
        → (τ : Sub (suc m) (suc l′)) → (τ′ : Sub (suc m′) (suc l′))
        → S ≃ S′ → m ≡ m′ → σ ≃s σ′ → τ ≃s τ′
        → sub-between-connect-pds (tree-to-pd S) (tree-to-pd T) σ τ ≃s sub-between-connect-pds (tree-to-pd S′) (tree-to-pd T) σ′ τ′
    lem S S′ T σ σ′ τ τ′ p refl q r with ≃-to-same-n p
    ... | refl with ≃-to-≡ p | ≃s-to-≡ q | ≃s-to-≡ r
    ... | refl | refl | refl = refl≃s

tree-inc-glob-step : (d : ℕ) → (T : Tree n) (b₁ b₂ : Bool) → tree-inc (suc d) T b₁ ∘ tree-inc d (tree-bd (suc d) T) b₂ ≃s tree-inc (suc d) T (not b₁) ∘ tree-inc d (tree-bd (suc d) T) b₂
tree-inc-glob-step d T b₁ b₂ = begin
  < tree-inc (suc d) T b₁ ∘ tree-inc d (tree-bd (suc d) T) b₂ >s
    ≈⟨ tree-inc-glob d (suc d) T b₂ b₁ (s≤s ≤-refl) ⟩
  < tree-inc d T b₂ >s
    ≈˘⟨ tree-inc-glob d (suc d) T b₂ (not b₁) (s≤s ≤-refl)  ⟩
  < tree-inc (suc d) T (not b₁) ∘ tree-inc d (tree-bd (suc d) T) b₂
    >s ∎
  where
    open Reasoning sub-setoid

tree-dim-bd : (d : ℕ) → (T : Tree n) → tree-dim (tree-bd d T) ≡ d ⊓ tree-dim T
tree-dim-bd zero T = refl
tree-dim-bd (suc d) Sing = refl
tree-dim-bd (suc d) (Join S T) = trans (cong₂ _⊔_ (cong suc (tree-dim-bd d S)) (tree-dim-bd (suc d) T)) (sym (⊓-distribˡ-⊔ (suc d) (suc (tree-dim S)) (tree-dim T)))

tree-dim-bd′ : (d : ℕ) → (T : Tree n) → d ≤ tree-dim T → tree-dim (tree-bd d T) ≡ d
tree-dim-bd′ d T p = trans (tree-dim-bd d T) (m≤n⇒m⊓n≡m p)

unbiased-type-tree : (d : ℕ) → (T : Tree n) → Ty (suc n) d
unbiased-term-tree : (d : ℕ) → (T : Tree n) → Tm (suc n)

unbiased-type-tree zero T = ⋆
unbiased-type-tree (suc d) T = (unbiased-term-tree d (tree-bd d T) [ tree-inc d T false ]tm) ─⟨ unbiased-type-tree d (tree-bd d T) [ tree-inc d T false ]ty ⟩⟶ (unbiased-term-tree d (tree-bd d T) [ tree-inc d T true ]tm)

unbiased-term-tree d T with is-linear-dec T
... | yes p = 0V
... | no p = Coh (tree-to-ctx T) (unbiased-type-tree d T) (idSub _)
