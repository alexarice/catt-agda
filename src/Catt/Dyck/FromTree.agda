module Catt.Dyck.FromTree where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Wedge.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties

-- Extendability
n-extendable : ℕ → Tree n → Set
n-extendable zero T = ⊤
n-extendable (suc n) Sing = ⊥
n-extendable (suc n) (Join S Sing) = n-extendable n S
n-extendable (suc n) (Join S T@(Join _ _)) = n-extendable (suc n) T

extend-tree : (n : ℕ) → (T : Tree m) → .⦃ n-extendable n T ⦄ → Tree (2 + m)
extend-tree zero Sing = Join Sing Sing
extend-tree zero (Join S T) = Join S (extend-tree zero T)
extend-tree (suc n) (Susp S) = Susp (extend-tree n S)
extend-tree (suc n) (Join S T@(Join _ _)) = Join S (extend-tree (suc n) T)

join-tree-preserves-extendable : (n : ℕ) → (S : Tree m) → (T : Tree m′) → ⦃ n-extendable n T ⦄ → n-extendable n (Join S T)
join-tree-preserves-extendable zero S T = it
join-tree-preserves-extendable (suc n) S (Join _ _) = it

extend-tree-is-join : (n : ℕ) → (T : Tree m) → .⦃ _ : n-extendable n T ⦄ → is-join (extend-tree n T)
extend-tree-is-join zero Sing = tt
extend-tree-is-join zero (Join S T) = tt
extend-tree-is-join (suc n) (Join S Sing) = tt
extend-tree-is-join (suc n) (Join S (Join T₁ T₂)) = tt

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

dyck-to-tree : Dyck n d → Tree (n * 2)
dyck-to-tree-is-n-extendable : (dy : Dyck n d) → n-extendable d (dyck-to-tree dy)

dyck-to-tree ⊝ = Sing
dyck-to-tree (⇑ {d = d} dy) = extend-tree d (dyck-to-tree dy) ⦃ dyck-to-tree-is-n-extendable dy ⦄
dyck-to-tree (⇓ dy) = dyck-to-tree dy

dyck-to-tree-is-n-extendable ⊝ = tt
dyck-to-tree-is-n-extendable (⇑ {d = d} dy) = extended-tree-is-more-extendable d (dyck-to-tree dy) ⦃ dyck-to-tree-is-n-extendable dy ⦄
dyck-to-tree-is-n-extendable (⇓ {d = d} dy) = pred-n-extendable d (dyck-to-tree dy) ⦃ dyck-to-tree-is-n-extendable dy ⦄

tree-to-dyck-len : (d : ℕ) → (T : Tree n) → .⦃ n-extendable d T ⦄ → ℕ
tree-to-dyck-len zero Sing = 0
tree-to-dyck-len zero (Join S T) = tree-to-dyck-len 0 T + suc (tree-to-dyck-len zero S)
tree-to-dyck-len (suc d) (Susp S) = suc (tree-to-dyck-len d S)
tree-to-dyck-len (suc d) (Join S T@(Join _ _)) = tree-to-dyck-len (suc d) T + suc (tree-to-dyck-len zero S)

tree-to-dyck-len-prop : (d : ℕ) → (T : Tree n) → .⦃ _ : n-extendable d T ⦄
                      → double (tree-to-dyck-len d T) ≡ n
tree-to-dyck-len-prop zero Sing = refl
tree-to-dyck-len-prop zero (Join S T) = begin
  double (tree-to-dyck-len 0 T + suc (tree-to-dyck-len zero S))
    ≡⟨ double-+ (tree-to-dyck-len 0 T) (suc (tree-to-dyck-len 0 S)) ⟩
  double (tree-to-dyck-len 0 T) + 2+ (double (tree-to-dyck-len zero S))
    ≡⟨ cong₂ _+_ (tree-to-dyck-len-prop 0 T) (cong 2+ (tree-to-dyck-len-prop 0 S)) ⟩
  _ ∎
  where
    open ≡-Reasoning
tree-to-dyck-len-prop (suc d) (Susp T) = cong 2+ (tree-to-dyck-len-prop d T)
tree-to-dyck-len-prop (suc d) (Join S T@(Join _ _)) = begin
  double (tree-to-dyck-len (suc d) T + suc (tree-to-dyck-len zero S))
    ≡⟨ double-+ (tree-to-dyck-len (suc d) T) (suc (tree-to-dyck-len 0 S)) ⟩
  double (tree-to-dyck-len (suc d) T) + 2+ (double (tree-to-dyck-len zero S))
    ≡⟨ cong₂ _+_ (tree-to-dyck-len-prop (suc d) T) (cong 2+ (tree-to-dyck-len-prop 0 S)) ⟩
  _ ∎
  where
    open ≡-Reasoning

tree-to-dyck : (d : ℕ) → (T : Tree n) → .⦃ _ : n-extendable d T ⦄ → Dyck (tree-to-dyck-len d T) d
tree-to-dyck zero Sing = ⊝
tree-to-dyck zero (Join S T) = wedge-dyck (⇓ (susp-dyck (tree-to-dyck zero S))) (tree-to-dyck zero T)
tree-to-dyck (suc d) (Join S Sing) = susp-dyck (tree-to-dyck d S)
tree-to-dyck (suc d) (Join S T@(Join _ _)) = wedge-dyck (⇓ (susp-dyck (tree-to-dyck zero S))) (tree-to-dyck (suc d) T)

tree-to-dyck-join : (d : ℕ) → (S : Tree m) → (T : Tree n) → .⦃ is-join T ⦄ → .⦃ _ : n-extendable d T ⦄ → tree-to-dyck d (Join S T) ⦃ join-tree-preserves-extendable d S T ⦄ ≃d wedge-dyck (⇓ (susp-dyck (tree-to-dyck 0 S))) (tree-to-dyck d T)
tree-to-dyck-join zero S T = refl≃d
tree-to-dyck-join (suc d) S (Join T₁ T₂) = refl≃d

-- tree to dyck to tree

subst-extendable-≃ : (n : ℕ) → {S : Tree m} → {T : Tree m′} → S ≃ T → ⦃ n-extendable n S ⦄ → n-extendable n T
subst-extendable-≃ zero p = it
subst-extendable-≃ (suc n) (Join≃ p Sing≃) = subst-extendable-≃ n p
subst-extendable-≃ (suc n) (Join≃ p q@(Join≃ _ _)) = subst-extendable-≃ (suc n) q

extend-tree-eq : {S : Tree n} → {T : Tree m} → (p : S ≃ T) → .⦃ ex : n-extendable d S ⦄
               → extend-tree d S ≃ extend-tree d T ⦃ subst-extendable-≃ d p ⦄
extend-tree-eq {d = zero} Sing≃ = refl≃
extend-tree-eq {d = zero} (Join≃ p q) = Join≃ p (extend-tree-eq q)
extend-tree-eq {d = suc d} (Join≃ p Sing≃) = Join≃ (extend-tree-eq p) Sing≃
extend-tree-eq {d = suc d} (Join≃ p q@(Join≃ _ _)) = Join≃ p (extend-tree-eq q)

++t-is-extendable : (n : ℕ) → (S : Tree m) → (T : Tree m′) → ⦃ _ : n-extendable n T ⦄ → n-extendable n (S ++t T)
++t-is-extendable n Sing T = it
++t-is-extendable n (Join S S′) T = join-tree-preserves-extendable n S (S′ ++t T) ⦃ ++t-is-extendable n S′ T ⦄

join-extend-tree : (S : Tree m)
                 → (T : Tree m′)
                 → .⦃ _ : n-extendable n T ⦄
                 → extend-tree n (Join S T) ⦃ join-tree-preserves-extendable n S T ⦄ ≃ Join S (extend-tree n T)
join-extend-tree {n = zero} S Sing = refl≃
join-extend-tree {n = zero} S (Join _ _) = refl≃
join-extend-tree {n = suc n} S (Join T Sing) = refl≃
join-extend-tree {n = suc n} S (Join T (Join _ _)) = refl≃

extend-wedge-tree : (S : Tree m)
                    → (T : Tree m′)
                    → .⦃ _ : n-extendable n T ⦄
                    → extend-tree n (S ++t T) ⦃ ++t-is-extendable n S T ⦄
                      ≃ S ++t (extend-tree n T)
extend-wedge-tree Sing T = refl≃
extend-wedge-tree {n = n} (Join S S′) T ⦃ ex ⦄ = let
  instance _ = ++t-is-extendable n S′ T
  in trans≃ (join-extend-tree S (S′ ++t T))
            (Join≃ refl≃ (extend-wedge-tree S′ T))

wedge-dyck-tree : (dy : Dyck n 0) → (ey : Dyck m d) → dyck-to-tree (wedge-dyck dy ey) ≃ dyck-to-tree dy ++t dyck-to-tree ey
wedge-dyck-tree dy ⊝ = ≃′-to-≃ (sym≃′ (++t-right-unit (dyck-to-tree dy)))
wedge-dyck-tree dy (⇑ ey) = let
  instance _ = dyck-to-tree-is-n-extendable (wedge-dyck dy ey)
  instance _ = dyck-to-tree-is-n-extendable ey
  in trans≃ (extend-tree-eq (wedge-dyck-tree dy ey)) (extend-wedge-tree (dyck-to-tree dy) (dyck-to-tree ey))
wedge-dyck-tree dy (⇓ ey) = wedge-dyck-tree dy ey

susp-dyck-tree : (dy : Dyck n d) → dyck-to-tree (susp-dyck dy) ≃ Susp (dyck-to-tree dy)
susp-dyck-tree ⊝ = refl≃
susp-dyck-tree (⇑ dy) = let
  instance _ = dyck-to-tree-is-n-extendable (susp-dyck dy)
  in extend-tree-eq (susp-dyck-tree dy)
susp-dyck-tree (⇓ dy) = susp-dyck-tree dy

tree-to-dyck-to-tree : (T : Tree n) → dyck-to-tree (tree-to-dyck 0 T) ≃ T
tree-to-dyck-to-tree Sing = Sing≃
tree-to-dyck-to-tree (Join S T) = begin
  < dyck-to-tree (wedge-dyck (⇓ (susp-dyck (tree-to-dyck zero S))) (tree-to-dyck zero T)) >t
    ≈⟨ wedge-dyck-tree (⇓ (susp-dyck (tree-to-dyck zero S))) (tree-to-dyck zero T) ⟩
  < dyck-to-tree (⇓ (susp-dyck (tree-to-dyck zero S))) ++t dyck-to-tree (tree-to-dyck zero T) >t
    ≈⟨ ++t-≃ (trans≃ (susp-dyck-tree (tree-to-dyck 0 S)) (Susp-≃ (tree-to-dyck-to-tree S))) (tree-to-dyck-to-tree T) ⟩
  < Susp S ++t T >t
    ≡⟨⟩
  < Join S T >t ∎
  where
    open Reasoning tree-setoid

-- Dyck to tree to dyck

tree-to-dyck-extend-tree : (d : ℕ) → (T : Tree n) → .⦃ _ : n-extendable d T ⦄ → tree-to-dyck (suc d) (extend-tree d T) ⦃ extended-tree-is-more-extendable d T ⦄ ≃d ⇑ (tree-to-dyck d T)
tree-to-dyck-extend-tree zero Sing = refl≃d
tree-to-dyck-extend-tree zero (Join S Sing) = refl≃d
tree-to-dyck-extend-tree zero (Join S (Join T₁ T₂)) = wedge-dyck-≃ refl≃d (tree-to-dyck-extend-tree 0 (Join T₁ T₂))
tree-to-dyck-extend-tree (suc d) (Join S Sing) = susp-dyck-≃ (tree-to-dyck-extend-tree d S)
tree-to-dyck-extend-tree (suc d) (Join S (Join T₁ T₂)) = trans≃d (tree-to-dyck-join (2 + d) S (extend-tree (suc d) (Join T₁ T₂)) ⦃ extend-tree-is-join (suc d) (Join T₁ T₂) ⦄ ⦃ extended-tree-is-more-extendable (suc d) (Join T₁ T₂) ⦄) (wedge-dyck-≃ refl≃d (tree-to-dyck-extend-tree (suc d) (Join T₁ T₂)))

tree-to-dyck-restrict : (d : ℕ) → (T : Tree n) → .⦃ _ : n-extendable (suc d) T ⦄ → tree-to-dyck d T ⦃ pred-n-extendable d T ⦄ ≃d ⇓ (tree-to-dyck (suc d) T)
tree-to-dyck-restrict zero (Join S Sing) = refl≃d
tree-to-dyck-restrict zero (Join S T@(Join _ _)) = wedge-dyck-≃ refl≃d (tree-to-dyck-restrict zero T)
tree-to-dyck-restrict (suc d) (Join S Sing) = susp-dyck-≃ (tree-to-dyck-restrict d S)
tree-to-dyck-restrict (suc d) (Join S T@(Join _ _)) = let
  instance _ = pred-n-extendable (suc d) T
  in wedge-dyck-≃ refl≃d (tree-to-dyck-restrict (suc d) T)

dyck-to-tree-to-dyck : (dy : Dyck n d) → tree-to-dyck d (dyck-to-tree dy) ⦃ dyck-to-tree-is-n-extendable dy ⦄ ≃d dy
dyck-to-tree-to-dyck ⊝ = refl≃d
dyck-to-tree-to-dyck {d = suc d} (⇑ dy) = let
  instance _ = dyck-to-tree-is-n-extendable dy
  instance _ = extended-tree-is-more-extendable d (dyck-to-tree dy)
  in begin
  < tree-to-dyck (suc d) (extend-tree d (dyck-to-tree dy)) >d
    ≈⟨ tree-to-dyck-extend-tree d (dyck-to-tree dy) ⟩
  < ⇑ (tree-to-dyck d (dyck-to-tree dy)) >d
    ≈⟨ ⇑≃ (dyck-to-tree-to-dyck dy) ⟩
  < ⇑ dy >d ∎
  where
    open Reasoning dyck-setoid
dyck-to-tree-to-dyck {d = d} (⇓ dy) = let
  instance _ = dyck-to-tree-is-n-extendable dy
  instance _ = dyck-to-tree-is-n-extendable (⇓ dy)
  in begin
  < tree-to-dyck d (dyck-to-tree (⇓ dy)) >d
    ≈⟨ tree-to-dyck-restrict d (dyck-to-tree dy) ⟩
  < ⇓ (tree-to-dyck (suc d) (dyck-to-tree dy)) >d
    ≈⟨ ⇓≃ (dyck-to-tree-to-dyck dy) ⟩
  < ⇓ dy >d ∎
  where
    open Reasoning dyck-setoid

-- Compat

⌊⌋-to-dyck-compat : (S : Tree n)
                  → ⌊ tree-to-dyck 0 S ⌋d ≃c ⌊ S ⌋
⌊⌋-to-dyck-compat Sing = refl≃c
⌊⌋-to-dyck-compat (Join S T) = begin
  < ⌊ wedge-dyck (⇓ (susp-dyck (tree-to-dyck zero S))) (tree-to-dyck zero T) ⌋d >c
    ≈⟨ wedge-⌊⌋d (⇓ (susp-dyck (tree-to-dyck zero S))) (tree-to-dyck zero T) ⟩
  < wedge ⌊ susp-dyck (tree-to-dyck zero S) ⌋d
          (dyck-term (⇓ (susp-dyck (tree-to-dyck zero S))))
          ⌊ tree-to-dyck zero T ⌋d >c
    ≈⟨ wedge-≃ l1 (ty-tgt′-≃ lem) (⌊⌋-to-dyck-compat T) ⟩
  < wedge-susp ⌊ S ⌋ ⌊ T ⌋ >c ∎
  where
    lem : dyck-type (susp-dyck (tree-to-dyck zero S)) ≃ty susp-ty ⋆
    lem = begin
      < dyck-type (susp-dyck (tree-to-dyck zero S)) >ty
        ≈⟨ susp-dyck-type (tree-to-dyck zero S) ⟩
      < susp-ty (dyck-type (tree-to-dyck zero S)) >ty
        ≈⟨ susp-ty-≃ (⋆-is-only-0-d-ty ⦃ IsZero-subst (sym (dyck-type-dim (tree-to-dyck zero S))) it ⦄) ⟩
      < susp-ty ⋆ >ty
        ≈⟨ susp-ty-≃ (Star≃ (cong suc (tree-to-dyck-len-prop 0 S))) ⟩
      < susp-ty ⋆ >ty ∎
      where
        open Reasoning ty-setoid

    open Reasoning ctx-setoid

    l1 : ⌊ susp-dyck (tree-to-dyck zero S) ⌋d ≃c susp-ctx ⌊ S ⌋
    l1 = begin
      < ⌊ susp-dyck (tree-to-dyck zero S) ⌋d >c
        ≈⟨ susp-⌊⌋d (tree-to-dyck zero S) ⟩
      < susp-ctx ⌊ tree-to-dyck zero S ⌋d >c
        ≈⟨ susp-ctx-≃ (⌊⌋-to-dyck-compat S) ⟩
      < susp-ctx ⌊ S ⌋ >c ∎
