module Catt.Tree.Boundary.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Tree
open import Catt.Tree.Boundary
open import Catt.Tree.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Variables
open import Catt.Variables.Properties

tree-inc-label-pphere : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-inc-label (suc d) T b .ap PPHere ≃p (PHere {S = T})
tree-inc-label-pphere d Sing b = refl≃p
tree-inc-label-pphere d (Join S T) b = refl≃p

tree-inc-label-last-path : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-inc-label (suc d) T b .ap (last-path (tree-bd (suc d) T)) ≃p carrier (last-path T)
tree-inc-label-last-path d Sing b = refl≃p
tree-inc-label-last-path d (Join S T) b = ≃Shift refl≃ (tree-inc-label-last-path d T b)



-- tree-inc-preserve-fst-var : (d : ℕ) → (T : Tree n) → (b : Bool) → Var (fromℕ _) [ tree-inc (suc d) T b ]tm ≃tm Var {suc (tree-size T)} (fromℕ _)
-- tree-inc-preserve-fst-var d Sing b = refl≃tm
-- tree-inc-preserve-fst-var d (Join S T) b = sub-between-connect-susps-fst-var (tree-inc d S b) (tree-inc (suc d) T b)

-- tree-inc-preserve-last-var : (d : ℕ) → (T : Tree n) → (b : Bool) → tree-last-var (tree-bd (suc d) T) [ tree-inc (suc d) T b ]tm ≃tm tree-last-var T
-- tree-inc-preserve-last-var d Sing b = refl≃tm
-- tree-inc-preserve-last-var d (Join S T) b = begin
--   < tree-last-var (tree-bd (suc d) T)
--     [ connect-susp-inc-right (tree-bd-len d S) (tree-bd-len (suc d) T) ]tm
--     [ sub-between-connect-susps (tree-inc d S b)
--                                 (tree-inc (suc d) T b) ]tm >tm
--     ≈˘⟨ assoc-tm _ _ (tree-last-var (tree-bd (suc d) T)) ⟩
--   < tree-last-var (tree-bd (suc d) T)
--     [ sub-between-connect-susps (tree-inc d S b)
--                                 (tree-inc (suc d) T b)
--       ∘ connect-susp-inc-right (tree-bd-len d S) (tree-bd-len (suc d) T) ]tm >tm
--     ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var (tree-bd (suc d) T)})
--        (sub-between-connect-susps-inc-right (tree-inc d S b)
--                                             (tree-inc (suc d) T b)
--                                             (tree-inc-preserve-fst-var d T b)) ⟩
--   < tree-last-var (tree-bd (suc d) T)
--     [ connect-susp-inc-right (tree-size S) (tree-size T) ∘ tree-inc (suc d) T b ]tm >tm
--     ≈⟨ assoc-tm _ _ (tree-last-var (tree-bd (suc d) T)) ⟩
--   < tree-last-var (tree-bd (suc d) T)
--     [ tree-inc (suc d) T b ]tm
--     [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm
--     ≈⟨ sub-action-≃-tm (tree-inc-preserve-last-var d T b) refl≃s ⟩
--   < tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm ∎
--   where
--     open Reasoning tm-setoid

tree-bd-glob : (d₁ d₂ : ℕ) → (T : Tree n) → d₁ < d₂ → tree-bd d₁ (tree-bd d₂ T) ≃ tree-bd d₁ T
tree-bd-glob zero d₂ T p = Sing≃
tree-bd-glob (suc d₁) (suc d₂) Sing p = Sing≃
tree-bd-glob (suc d₁) (suc d₂) (Join S T) p = Join≃ (tree-bd-glob d₁ d₂ S (≤-pred p)) (tree-bd-glob (suc d₁) (suc d₂) T p)

tree-bd-full : (d : ℕ) → (T : Tree n) → (tree-dim T ≤ d) → tree-bd d T ≃ T
tree-bd-full zero Sing p = Sing≃
tree-bd-full zero (Join S T) ()
tree-bd-full (suc d) Sing p = Sing≃
tree-bd-full (suc d) (Join S T) p = Join≃ (tree-bd-full d S (≤-trans (m≤n⊔m (pred (tree-dim T)) (tree-dim S)) (≤-pred p))) (tree-bd-full (suc d) T (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p))

tree-inc-label-glob : (d₁ d₂ : ℕ) → (T : Tree n) → (b₁ b₂ : Bool) → (p : d₁ < d₂)
                    → (P : PPath (tree-bd d₁ (tree-bd d₂ T)))
                    → carrier (tree-inc-label′ d₂ T b₂ (tree-inc-label′ d₁ (tree-bd d₂ T) b₁ P)) ≃p tree-inc-label d₁ T b₁ .ap (ppath-≃ (tree-bd-glob d₁ d₂ T p) P)
tree-inc-label-glob zero (suc d₂) T false b₂ p P = tree-inc-label-pphere d₂ T b₂
tree-inc-label-glob zero (suc d₂) T true b₂ p P = tree-inc-label-last-path d₂ T b₂
tree-inc-label-glob (suc d₁) (suc d₂) Sing b₁ b₂ p ⟦ PHere ⟧ = refl≃p
tree-inc-label-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ p ⟦ PHere ⟧ = refl≃p
tree-inc-label-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ (s≤s p) ⟦ PExt P ⟧ = ≃Ext (tree-inc-label-glob d₁ d₂ S b₁ b₂ p ⟦ P ⟧) refl≃
tree-inc-label-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ p ⟦ PShift P ⟧ = ≃Shift refl≃ (tree-inc-label-glob (suc d₁) (suc d₂) T b₁ b₂ p ⟦ P ⟧)

tree-inc-glob : (d₁ d₂ : ℕ) → (T : Tree n) → (b₁ b₂ : Bool) → d₁ < d₂ → tree-inc d₂ T b₂ ∘ tree-inc d₁ (tree-bd d₂ T) b₁ ≃s tree-inc d₁ T b₁
tree-inc-glob d₁ d₂ T b₁ b₂ p = begin
  < tree-inc d₂ T b₂ ∘ tree-inc d₁ (tree-bd d₂ T) b₁ >s
    ≈˘⟨ label-to-sub-comp (tree-inc-label d₁ (tree-bd d₂ T) b₁) (tree-inc-label d₂ T b₂) ⟩
  < label-to-sub (label-comp (tree-inc-label d₁ (tree-bd d₂ T) b₁) (tree-inc-label d₂ T b₂)) >s
    ≈⟨ label-to-sub-≃ (label-comp (tree-inc-label d₁ (tree-bd d₂ T) b₁) (tree-inc-label d₂ T b₂)) (prepend (tree-inc-label′ d₁ (tree-bd d₂ T) b₁) (tree-inc-label d₂ T b₂)) (λ P → extend-ppath (tree-inc-label′ d₁ (tree-bd d₂ T) b₁ P) (tree-inc-label d₂ T b₂)) refl≃ty ⟩
  < label-to-sub (prepend (tree-inc-label′ d₁ (tree-bd d₂ T) b₁) (tree-inc-label d₂ T b₂)) >s
    ≈⟨ label-to-sub-≃′ (prepend (tree-inc-label′ d₁ (tree-bd d₂ T) b₁) (tree-inc-label d₂ T b₂)) (tree-inc-label d₁ T b₁) ((tree-bd-glob d₁ d₂ T p) ,, (tree-inc-label-glob d₁ d₂ T b₁ b₂ p)) refl≃ty ⟩
  < tree-inc d₁ T b₁ >s ∎
  where
    open Reasoning sub-setoid

-- tree-inc-glob : (d₁ d₂ : ℕ) → (T : Tree n) → (b₁ b₂ : Bool) → d₁ < d₂ → tree-inc d₂ T b₂ ∘ tree-inc d₁ (tree-bd d₂ T) b₁ ≃s tree-inc d₁ T b₁
-- tree-inc-glob zero (suc d₂) T false b₂ p = Ext≃ refl≃s (tree-inc-preserve-fst-var d₂ T b₂)
-- tree-inc-glob zero (suc d₂) T true b₂ p = Ext≃ refl≃s (tree-inc-preserve-last-var d₂ T b₂)
-- tree-inc-glob (suc d₁) (suc d₂) Sing b₁ b₂ p = refl≃s
-- tree-inc-glob (suc d₁) (suc d₂) (Join S T) b₁ b₂ p = begin
--   < sub-between-connect-susps (tree-inc d₂ S b₂) (tree-inc (suc d₂) T b₂)
--     ∘ sub-between-connect-susps (tree-inc d₁ (tree-bd d₂ S) b₁) (tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁) >s
--     ≈⟨ sub-between-connect-susps-comp (tree-inc d₁ (tree-bd d₂ S) b₁) (tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁) (tree-inc d₂ S b₂) (tree-inc (suc d₂) T b₂) (tree-inc-preserve-fst-var d₂ T b₂) ⟩
--   < sub-between-connect-susps
--     (tree-inc d₂ S b₂ ∘ tree-inc d₁ (tree-bd d₂ S) b₁)
--     (tree-inc (suc d₂) T b₂ ∘ tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁)
--     >s
--     ≈⟨ sub-between-connect-susps-≃ (tree-inc d₂ S b₂ ∘ tree-inc d₁ (tree-bd d₂ S) b₁)
--                                    (tree-inc d₁ S b₁)
--                                    (tree-inc (suc d₂) T b₂ ∘ tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁)
--                                    (tree-inc (suc d₁) T b₁)
--                                    (≃-to-same-n (tree-bd-glob d₁ d₂ S (≤-pred p)))
--                                    (≃-to-same-n (tree-bd-glob (suc d₁) (suc d₂) T p))
--                                    (tree-inc-glob d₁ d₂ S b₁ b₂ (≤-pred p))
--                                    (tree-inc-glob (suc d₁) (suc d₂) T b₁ b₂ p) ⟩
--   < sub-between-connect-susps (tree-inc d₁ S b₁)
--       (tree-inc (suc d₁) T b₁) >s ∎
--   where
--     open Reasoning sub-setoid

-- tree-inc-full : (d : ℕ) → (T : Tree n) → (b : Bool) → (p : tree-dim T ≤ d) → tree-inc d T b ≃s idSub {suc (tree-size T)}
-- tree-inc-full zero Sing false p = refl≃s
-- tree-inc-full zero Sing true p = refl≃s
-- tree-inc-full zero (Join S T) b ()
-- tree-inc-full (suc d) Sing b p = refl≃s
-- tree-inc-full (suc d) (Join S T) b p = begin
--   < sub-between-connect-susps (tree-inc d S b) (tree-inc (suc d) T b) >s
--     ≈⟨ sub-between-connect-susps-≃ (tree-inc d S b) idSub (tree-inc (suc d) T b) idSub (≃-to-same-n (tree-bd-full d S (m⊔n≤o⇒n≤o (pred (tree-dim T)) (tree-dim S) (≤-pred p)))) (≃-to-same-n (tree-bd-full (suc d) T (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p))) (tree-inc-full d S b (m⊔n≤o⇒n≤o (pred (tree-dim T)) (tree-dim S) (≤-pred p))) (tree-inc-full (suc d) T b (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p)) ⟩
--   < sub-between-connect-susps idSub idSub >s
--     ≈⟨ sub-between-connect-susps-id _ _ ⟩
--   < idSub >s ∎
--   where
--     open Reasoning sub-setoid

-- tree-inc-glob-step : (d : ℕ) → (T : Tree n) (b₁ b₂ : Bool) → tree-inc (suc d) T b₁ ∘ tree-inc d (tree-bd (suc d) T) b₂ ≃s tree-inc (suc d) T (not b₁) ∘ tree-inc d (tree-bd (suc d) T) b₂
-- tree-inc-glob-step d T b₁ b₂ = begin
--   < tree-inc (suc d) T b₁ ∘ tree-inc d (tree-bd (suc d) T) b₂ >s
--     ≈⟨ tree-inc-glob d (suc d) T b₂ b₁ (s≤s ≤-refl) ⟩
--   < tree-inc d T b₂ >s
--     ≈˘⟨ tree-inc-glob d (suc d) T b₂ (not b₁) (s≤s ≤-refl)  ⟩
--   < tree-inc (suc d) T (not b₁) ∘ tree-inc d (tree-bd (suc d) T) b₂
--     >s ∎
--   where
--     open Reasoning sub-setoid


-- tree-dim-bd : (d : ℕ) → (T : Tree n) → tree-dim (tree-bd d T) ≡ d ⊓ tree-dim T
-- tree-dim-bd zero T = refl
-- tree-dim-bd (suc d) Sing = refl
-- tree-dim-bd (suc d) (Join S T) = cong suc (begin
--   pred (tree-dim (tree-bd (suc d) T)) ⊔ tree-dim (tree-bd d S)
--     ≡⟨ cong₂ (λ a → (pred a) ⊔_) (tree-dim-bd (suc d) T) (tree-dim-bd d S) ⟩
--   pred (suc d ⊓ tree-dim T) ⊔ (d ⊓ tree-dim S)
--     ≡⟨ cong (_⊔ (d ⊓ tree-dim S)) (∸-distribʳ-⊓ 1 (suc d) (tree-dim T)) ⟩
--   (d ⊓ pred (tree-dim T)) ⊔ (d ⊓ tree-dim S)
--     ≡˘⟨ ⊓-distribˡ-⊔ d (pred (tree-dim T)) (tree-dim S) ⟩
--   d ⊓ (pred (tree-dim T) ⊔ tree-dim S) ∎)
--   where
--     open ≡-Reasoning

-- tree-dim-bd′ : (d : ℕ) → (T : Tree n) → d ≤ tree-dim T → tree-dim (tree-bd d T) ≡ d
-- tree-dim-bd′ d T p = trans (tree-dim-bd d T) (m≤n⇒m⊓n≡m p)

-- tree-inc-susp-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → suspSub (tree-inc d T b) ≃s tree-inc (suc d) (suspTree T) b
-- tree-inc-susp-lem zero T false = sym≃s (id-left-unit ⟨ ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩ , suspTm (Var (fromℕ _)) ⟩)
-- tree-inc-susp-lem zero T true = sym≃s (id-left-unit ⟨ ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩ , suspTm (tree-last-var T) ⟩)
-- tree-inc-susp-lem (suc d) Sing b = refl≃s
-- tree-inc-susp-lem (suc d) (Join S T) b = sym≃s (id-left-unit _)
