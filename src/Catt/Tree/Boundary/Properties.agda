module Catt.Tree.Boundary.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Boundary

tree-inc-label-phere : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-inc-label′ (suc d) T b PHere ≃p PHere {S = T}
tree-inc-label-phere d Sing b = refl≃p
tree-inc-label-phere d (Join S T) b = refl≃p

tree-inc-label-last-path : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-inc-label′ (suc d) T b (last-path (tree-bd (suc d) T)) ≃p (last-path T)
tree-inc-label-last-path d Sing b = refl≃p
tree-inc-label-last-path d (Join S T) b = Shift≃ refl≃ (tree-inc-label-last-path d T b)

tree-inc-not-here : (d : ℕ) → (T : Tree n) → (b : Bool) → (Z : Path (tree-bd d T)) → .⦃ not-here Z ⦄ → not-here (tree-inc-label′ d T b Z)
tree-inc-not-here zero T b PHere = ⊥-elim it
tree-inc-not-here (suc d) Sing b PHere = ⊥-elim it
tree-inc-not-here (suc d) (Join S T) b (PExt Z) = tt
tree-inc-not-here (suc d) (Join S T) b (PShift Z) = tt

++t-bd : (d : ℕ)
                → (S : Tree n)
                → (T : Tree m)
                → tree-bd (suc d) S ++t tree-bd (suc d) T
                ≃′ tree-bd (suc d) (S ++t T)
++t-bd d Sing T = refl≃′
++t-bd d (Join S₁ S₂) T = Join≃′ refl≃′ (++t-bd d S₂ T)

tree-inc-inc-left : (d : ℕ) → (S : Tree n) → (T : Tree m) → (b : Bool)
                  → (Z : Path (tree-bd (suc d) S))
                  → ++t-inc-left′ S T (tree-inc-label′ (suc d) S b Z)
                  ≃p tree-inc-label′ (suc d) (S ++t T) b (ppath-≃ (++t-bd d S T) (++t-inc-left′ (tree-bd (suc d) S) (tree-bd (suc d) T) Z))
tree-inc-inc-left d Sing T b Z = sym≃p (tree-inc-label-phere d T b)
tree-inc-inc-left d (Join S₁ S₂) T b PHere = refl≃p
tree-inc-inc-left d (Join S₁ S₂) T b (PExt Z) = refl≃p
tree-inc-inc-left d (Join S₁ S₂) T b (PShift Z) = Shift≃ refl≃ (tree-inc-inc-left d S₂ T b Z)

tree-inc-inc-right : (d : ℕ) → (S : Tree n) → (T : Tree m) → (b : Bool)
                   → (Z : Path (tree-bd (suc d) T))
                   → ++t-inc-right′ S T (tree-inc-label′ (suc d) T b Z)
                   ≃p tree-inc-label′ (suc d) (S ++t T) b (ppath-≃ (++t-bd d S T) (++t-inc-right′ (tree-bd (suc d) S) (tree-bd (suc d) T) Z))
tree-inc-inc-right d Sing T b Z = refl≃p
tree-inc-inc-right d (Join S₁ S₂) T b Z = Shift≃ refl≃ (tree-inc-inc-right d S₂ T b Z)

tree-bd-≃ : d ≡ d′ → S ≃ T → tree-bd d S ≃ tree-bd d′ T
tree-bd-≃ {d = zero} refl p = Sing≃
tree-bd-≃ {d = suc d} refl Sing≃ = Sing≃
tree-bd-≃ {d = suc d} refl (Join≃ p q) = Join≃ (tree-bd-≃ refl p) (tree-bd-≃ refl q)

tree-bd-glob : (d₁ d₂ : ℕ) → (T : Tree n) → d₁ < d₂ → tree-bd d₁ (tree-bd d₂ T) ≃′ tree-bd d₁ T
tree-bd-glob zero d₂ T p = Refl≃′
tree-bd-glob (suc d₁) (suc d₂) Sing p = Refl≃′
tree-bd-glob (suc d₁) (suc d₂) (Join S T) p = Join≃′ (tree-bd-glob d₁ d₂ S (≤-pred p)) (tree-bd-glob (suc d₁) (suc d₂) T p)

tree-bd-full : (d : ℕ) → (T : Tree n) → .(tree-dim T ≤ d) → tree-bd d T ≃′ T
tree-bd-full zero Sing p = Refl≃′
tree-bd-full zero (Join S T) ()
tree-bd-full (suc d) Sing p = Refl≃′
tree-bd-full (suc d) (Join S T) p = Join≃′ (tree-bd-full d S (≤-trans (m≤n⊔m (pred (tree-dim T)) (tree-dim S)) (≤-pred p))) (tree-bd-full (suc d) T (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p))

tree-inc-label-glob : (d₁ d₂ : ℕ) → (T : Tree n) → (b₁ b₂ : Bool) → (p : d₁ < d₂)
                    → (tree-inc-label′ d₂ T b₂ ∘ (tree-inc-label′ d₁ (tree-bd d₂ T) b₁)) ≃lp (tree-inc-label′ d₁ T b₁ ∘ ppath-≃ (tree-bd-glob d₁ d₂ T p))
tree-inc-label-glob zero (suc d₂) T false b₂ p .get P = tree-inc-label-phere d₂ T b₂
tree-inc-label-glob zero (suc d₂) T true b₂ p .get P = tree-inc-label-last-path d₂ T b₂
tree-inc-label-glob (suc d₁) (suc d₂) Sing b₁ b₂ p .get PHere = refl≃p
tree-inc-label-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ p .get PHere = refl≃p
tree-inc-label-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ (s≤s p) .get (PExt P) = Ext≃ (tree-inc-label-glob d₁ d₂ S b₁ b₂ p .get P) refl≃
tree-inc-label-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ p .get (PShift P) = Shift≃ refl≃ (tree-inc-label-glob (suc d₁) (suc d₂) T b₁ b₂ p .get P)

tree-inc-glob : (d₁ d₂ : ℕ) → (T : Tree n) → (b₁ b₂ : Bool) → d₁ < d₂ → tree-inc d₂ T b₂ ● tree-inc d₁ (tree-bd d₂ T) b₁ ≃s tree-inc d₁ T b₁
tree-inc-glob d₁ d₂ T b₁ b₂ p = begin
  < tree-inc d₂ T b₂ ● tree-inc d₁ (tree-bd d₂ T) b₁ >s
    ≈⟨ label-comp-to-sub (tree-inc-label d₁ (tree-bd d₂ T) b₁) (tree-inc-label d₂ T b₂) ⟩
  < label-to-sub (tree-inc-label d₁ (tree-bd d₂ T) b₁ ●lt tree-inc-label d₂ T b₂) >s
    ≈⟨ label-to-sub-≃′ (tree-inc-label d₁ (tree-bd d₂ T) b₁ ●lt tree-inc-label d₂ T b₂) (tree-inc-label d₁ T b₁) ((tree-bd-glob d₁ d₂ T p) ,, [ (λ P → SPath≃ (tree-inc-label-glob d₁ d₂ T b₁ b₂ p .get P)) ]) refl≃sty ⟩
  < tree-inc d₁ T b₁ >s ∎
  where
    open Reasoning sub-setoid

tree-inc-label-full : (d : ℕ) → (T : Tree n) → (b : Bool) → .(p : tree-dim T ≤ d) → tree-inc-label′ d T b ≃lp ppath-≃ (tree-bd-full d T p)
tree-inc-label-full zero Sing false p .get PHere = refl≃p
tree-inc-label-full zero Sing true p .get PHere = refl≃p
tree-inc-label-full (suc d) Sing b p .get PHere = refl≃p
tree-inc-label-full (suc d) (Join S T) b p .get PHere = refl≃p
tree-inc-label-full (suc d) (Join S T) b p .get (PExt Z) = Ext≃ (tree-inc-label-full d S b (m⊔n≤o⇒n≤o (pred (tree-dim T)) (tree-dim S) (≤-pred p)) .get Z) refl≃
tree-inc-label-full (suc d) (Join S T) b p .get (PShift Z) = Shift≃ refl≃ (tree-inc-label-full (suc d) T b (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p) .get Z)

tree-inc-label-full-is-id : (d : ℕ) → (T : Tree n) → (b : Bool) → .(p : tree-dim T ≤ d) → ap (tree-inc-label d T b) ≃l id-label (tree-bd d T)
tree-inc-label-full-is-id d T b p .get Z = SPath≃ (trans≃p (tree-inc-label-full d T b p .get Z) (sym≃p (ppath-≃-≃p (tree-bd-full d T p) Z)))

tree-inc-full-preserve-max : (d : ℕ) → (T : Tree n) → (b : Bool) → .(p : tree-dim T ≤ d) → (Z : Path (tree-bd d T)) → .⦃ is-maximal Z ⦄ → is-maximal (tree-inc-label′ d T b Z)
tree-inc-full-preserve-max d T b p Z = maximal-≃ (trans≃p (ppath-≃-≃p (tree-bd-full d T p) Z) (sym≃p (tree-inc-label-full d T b p .get Z)))

tree-inc-full : (d : ℕ) → (T : Tree n) → (b : Bool) → (p : tree-dim T ≤ d) → tree-inc d T b ≃s idSub {suc (tree-size T)}
tree-inc-full d T b p = begin
  < tree-inc d T b >s
    ≈⟨ label-to-sub-≃′ (tree-inc-label d T b) (id-label-wt T) ((tree-bd-full d T p) ,, [ (λ P → SPath≃ (tree-inc-label-full d T b p .get P)) ]) refl≃sty ⟩
  < label-to-sub (id-label-wt T) >s
    ≈⟨ id-label-to-sub T ⟩
  < idSub >s ∎
  where
    open Reasoning sub-setoid

tree-inc-glob-step : (d : ℕ) → (T : Tree n) (b₁ b₂ : Bool) → tree-inc (suc d) T b₁ ● tree-inc d (tree-bd (suc d) T) b₂ ≃s tree-inc (suc d) T (not b₁) ● tree-inc d (tree-bd (suc d) T) b₂
tree-inc-glob-step d T b₁ b₂ = begin
  < tree-inc (suc d) T b₁ ● tree-inc d (tree-bd (suc d) T) b₂ >s
    ≈⟨ tree-inc-glob d (suc d) T b₂ b₁ (s≤s ≤-refl) ⟩
  < tree-inc d T b₂ >s
    ≈˘⟨ tree-inc-glob d (suc d) T b₂ (not b₁) (s≤s ≤-refl)  ⟩
  < tree-inc (suc d) T (not b₁) ● tree-inc d (tree-bd (suc d) T) b₂
    >s ∎
  where
    open Reasoning sub-setoid


tree-dim-bd : (d : ℕ) → (T : Tree n) → tree-dim (tree-bd d T) ≡ d ⊓ tree-dim T
tree-dim-bd zero T = refl
tree-dim-bd (suc d) Sing = refl
tree-dim-bd (suc d) (Join S T) = cong suc (begin
  pred (tree-dim (tree-bd (suc d) T)) ⊔ tree-dim (tree-bd d S)
    ≡⟨ cong₂ (λ a → (pred a) ⊔_) (tree-dim-bd (suc d) T) (tree-dim-bd d S) ⟩
  pred (suc d ⊓ tree-dim T) ⊔ (d ⊓ tree-dim S)
    ≡⟨ cong (_⊔ (d ⊓ tree-dim S)) (∸-distribʳ-⊓ 1 (suc d) (tree-dim T)) ⟩
  (d ⊓ pred (tree-dim T)) ⊔ (d ⊓ tree-dim S)
    ≡˘⟨ ⊓-distribˡ-⊔ d (pred (tree-dim T)) (tree-dim S) ⟩
  d ⊓ (pred (tree-dim T) ⊔ tree-dim S) ∎)
  where
    open ≡-Reasoning

tree-dim-bd′ : (d : ℕ) → (T : Tree n) → d ≤ tree-dim T → tree-dim (tree-bd d T) ≡ d
tree-dim-bd′ d T p = trans (tree-dim-bd d T) (m≤n⇒m⊓n≡m p)

tree-dim-bd″ : (d : ℕ) → (T : Tree n) → tree-dim (tree-bd d T) ≤ d
tree-dim-bd″ d T = ≤-trans (≤-reflexive (tree-dim-bd d T)) (m⊓n≤m d (tree-dim T))

bd-trunk-height : (d : ℕ) → (T : Tree n) → .(d ≤ trunk-height T) → is-linear (tree-bd d T)
bd-trunk-height zero T p = tt
bd-trunk-height (suc d) (Join T Sing) p = inst ⦃ bd-trunk-height d T (≤-pred p) ⦄
