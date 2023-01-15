module Catt.Tree.Unbiased.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Unbiased
open import Catt.Tree
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Globular
open import Catt.Globular.Properties

unbiased-type-dim : (d : ℕ) → (T : Tree n) → sty-dim (unbiased-type d T) ≡ d
unbiased-type-dim zero T = refl
unbiased-type-dim (suc d) T = cong suc (unbiased-type-dim d T)

-- unbiased-comp-dim : (d : ℕ) → (T : Tree n) → tm-height (tree-to-ctx T) (stm-to-term (unbiased-comp d T)) ≡ d
-- unbiased-comp-dim d T = trans (sym (sub-dim (label-to-sub (id-label-wt T) ● idSub) (unbiased-type d T))) (unbiased-type-dim d T)

unbiased-type-≃ : d ≡ d′ → (S ≃ T) → unbiased-type d S ≃sty unbiased-type d′ T
unbiased-type-≃ refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃sty

unbiased-comp-≃ : d ≡ d′ → (S ≃ T) → unbiased-comp d S ≃stm unbiased-comp d′ T
unbiased-comp-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

unbiased-comp′-≃ : d ≡ d′ → (S ≃ T) → unbiased-comp′ d S ≃stm unbiased-comp′ d′ T
unbiased-comp′-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

unbiased-stm-≃ : d ≡ d′ → (S ≃ T) → unbiased-stm d S ≃stm unbiased-stm d′ T
unbiased-stm-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

unbiased-stm-≃-prop : (d : ℕ) → (p : S ≃′ T) → (unbiased-stm d S >>= SPath ∘ ppath-≃ p ,, S⋆) ≃stm unbiased-stm d T
unbiased-stm-≃-prop {S = S} {T = T} d p = begin
  < unbiased-stm d S >>= SPath ∘ ppath-≃ p ,, S⋆ >stm
    ≈⟨ extend-≃ (refl≃stm {a = unbiased-stm d S}) (ppath-≃l p) (≃S⋆ (sym≃ (≃′-to-≃ p))) ⟩
  < unbiased-stm d S >>= id-label-wt S >stm
    ≈⟨ extend-id (unbiased-stm d S) ⟩
  < unbiased-stm d S >stm
    ≈⟨ unbiased-stm-≃ refl (≃′-to-≃ p) ⟩
  < unbiased-stm d T >stm ∎
  where open Reasoning stm-setoid

unbiased-stm-linear : (d : ℕ) → (T : Tree n) → .⦃ _ : is-linear T ⦄ → .(d ≡ tree-dim T) → unbiased-stm d T ≃stm SPath (is-linear-max-path T)
unbiased-stm-linear zero Sing p = [ refl≃tm ]
unbiased-stm-linear (suc d) (Join T Sing) p = compute-≃ (≃SExt (unbiased-stm-linear d T (cong pred p)) refl≃)

unbiased-stm-bd-non-linear : (d : ℕ) → (T : Tree n) → .(d > linear-height T) → unbiased-stm d (tree-bd d T) ≃stm unbiased-comp′ d (tree-bd d T)
unbiased-stm-bd-non-linear (suc d) Sing p = refl≃stm
unbiased-stm-bd-non-linear (suc d) (Join T Sing) p = ≃SExt (unbiased-stm-bd-non-linear d T (≤-pred p)) Sing≃
unbiased-stm-bd-non-linear (suc d) (Join T (Join T₁ T₂)) p = refl≃stm

unbiased-stm-full-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → (tree-dim T ≤ d) → (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm unbiased-stm d T
unbiased-stm-full-lem d T b p = begin
  < unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b >stm
    ≈⟨ extend-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → ≃SPath (tree-inc-label-full d T b p .get P)) ] refl≃sty ⟩
  < unbiased-stm d (tree-bd d T) >>= (λ z → SPath (ppath-≃ (tree-bd-full d T p) z)) ,, S⋆ >stm
    ≈˘⟨ extend-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → ≃SPath (ppath-≃-≃p (tree-bd-full d T p) P)) ] [ (Star≃ (cong suc (≃-to-same-n (≃′-to-≃ (tree-bd-full d T p))))) ] ⟩
  < unbiased-stm d (tree-bd d T) >>= id-label-wt (tree-bd d T) >stm
    ≈⟨ extend-id (unbiased-stm d (tree-bd d T)) ⟩
  < unbiased-stm d (tree-bd d T) >stm
    ≈⟨ unbiased-stm-≃ refl (≃′-to-≃ (tree-bd-full d T p)) ⟩
  < unbiased-stm d T >stm ∎
  where
    open Reasoning stm-setoid

-- unbiased-type-truncate-1 : (d : ℕ) → (T : Tree n) → truncate 1 (unbiased-type (suc d) T) ≃ty Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T
-- unbiased-type-truncate-1 zero T = Arr≃ refl≃tm refl≃ty (last-path-to-term T)
-- unbiased-type-truncate-1 (suc d) T = begin
--   < truncate 1 (stm-to-term (unbiased-stm (suc d) (tree-bd (suc d) T) >>= tree-inc-label (suc d) T false)
--                ─⟨ unbiased-type (suc d) T ⟩⟶
--                stm-to-term (unbiased-stm (suc d) (tree-bd (suc d) T) >>= tree-inc-label (suc d) T true)) >ty
--     ≈⟨ truncate-≤ {s = stm-to-term (unbiased-stm (suc d) (tree-bd (suc d) T) >>= tree-inc-label (suc d) T false)}
--                   {t = stm-to-term (unbiased-stm (suc d) (tree-bd (suc d) T) >>= tree-inc-label (suc d) T true)}
--                   1 (unbiased-type (suc d) T) (s≤s z≤n) ⟩
--   < truncate 1 (unbiased-type (suc d) T) >ty
--     ≈⟨ unbiased-type-truncate-1 d T ⟩
--   < Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T >ty ∎
--   where
--     open Reasoning ty-setoid

-- unbiased-type-truncate-1′ : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → truncate 1 (unbiased-type d T) ≃ty Var (fromℕ _) ─⟨ ⋆ ⟩⟶ tree-last-var T
-- unbiased-type-truncate-1′ (suc d) = unbiased-type-truncate-1 d

unbiased-term-≃ : (d ≡ d′) → S ≃ T → unbiased-term d S ≃tm unbiased-term d′ T
unbiased-term-≃ refl p with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = refl≃tm

unbiased-type-prop : (d : ℕ) → (T : Tree n) → (d′ : ℕ) → (d ≤ d′) → (b : Bool) → unbiased-type d T ≃sty label-on-sty (unbiased-type d (tree-bd d′ T)) (tree-inc-label d′ T b)
unbiased-type-prop zero T d′ p b = refl≃sty
unbiased-type-prop (suc d) T d′ p b = ≃SArr (lem false) (unbiased-type-prop d T d′ (≤-trans (n≤1+n d) p) b) (lem true)
  where
    lem : (b′ : Bool) → (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b′)
      ≃stm (unbiased-stm d (tree-bd d (tree-bd d′ T)) >>=
        tree-inc-label d (tree-bd d′ T) b′ >>= tree-inc-label d′ T b)
    lem b′ = begin
      < unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b′ >stm
        ≈˘⟨ extend-≃′ (unbiased-stm-≃ {d = d} refl (≃′-to-≃ (tree-bd-glob d d′ T p))) ((tree-bd-glob d d′ T p) ,, [ (λ P → ≃SPath (tree-inc-label-glob d d′ T b′ b p .get P)) ]) refl≃sty ⟩
      < unbiased-stm d (tree-bd d (tree-bd d′ T))
        >>= label-wt-comp (tree-inc-label d (tree-bd d′ T) b′) (tree-inc-label d′ T b) >stm
        ≈˘⟨ extend-assoc (unbiased-stm d (tree-bd d (tree-bd d′ T))) _ _ ⟩
      < unbiased-stm d (tree-bd d (tree-bd d′ T))
        >>= tree-inc-label d (tree-bd d′ T) b′
        >>= tree-inc-label d′ T b >stm ∎
-- begin
      -- < stm-to-term (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b′) >tm
      --   ≈˘⟨ label-to-sub-stm (tree-inc-label d T b′) (unbiased-stm d (tree-bd d T)) ⟩
      -- < unbiased-term d (tree-bd d T) [ tree-inc d T b′ ]tm >tm
      --   ≈˘⟨ sub-action-≃-tm (unbiased-term-≃ (refl {x = d}) (≃′-to-≃ (tree-bd-glob d d′ T p))) (tree-inc-glob d d′ T b′ b p) ⟩
      -- < unbiased-term d (tree-bd d (tree-bd d′ T))
      --   [ tree-inc d′ T b ● tree-inc d (tree-bd d′ T) b′ ]tm >tm
      --   ≈⟨ assoc-tm _ _ (unbiased-term d (tree-bd d (tree-bd d′ T))) ⟩
      -- < unbiased-term d (tree-bd d (tree-bd d′ T))
      --   [ tree-inc d (tree-bd d′ T) b′ ]tm
      --   [ tree-inc d′ T b ]tm >tm
      --   ≈⟨ sub-action-≃-tm (label-to-sub-stm (tree-inc-label d (tree-bd d′ T) b′) (unbiased-stm d (tree-bd d (tree-bd d′ T)))) refl≃s ⟩
      -- < stm-to-term (unbiased-stm d (tree-bd d (tree-bd d′ T)) >>= tree-inc-label d (tree-bd d′ T) b′) [ tree-inc d′ T b ]tm >tm ∎
      where
        open Reasoning stm-setoid

lfltu-maximal-path : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → (Z : Path S) → .⦃ is-Maximal Z ⦄
                                             → label-from-linear-tree-unbiased S T d Z ≃stm unbiased-comp′ (d + tree-dim S) T
lfltu-maximal-path Sing T d Z = unbiased-comp′-≃ (sym (+-identityʳ d)) refl≃
lfltu-maximal-path (Join S Sing) T d (PExt Z) = trans≃stm (lfltu-maximal-path S T (suc d) Z) (unbiased-comp′-≃ (sym (+-suc d (tree-dim S))) refl≃)
lfltu-maximal-path (Join S Sing) T d (PShift PHere) = ⊥-elim it

lfltu-≤-linear-height-lem : {x y : ℕ}
                          → (p : x ≡ y)
                          → (T : Tree n)
                          → (b : Bool)
                          → .(xp : x ≤ linear-height T)
        → SPath (tree-inc-label′ x T b (is-linear-max-path (tree-bd x T) ⦃ bd-linear-height x T xp ⦄))
          ≃stm SPath (tree-inc-label′ y T b (is-linear-max-path (tree-bd y T) ⦃ bd-linear-height y T (≤-trans (≤-reflexive (sym p)) xp) ⦄))
lfltu-≤-linear-height-lem refl T b xp = refl≃stm

module _ where
  open Reasoning stm-setoid

  lfltu-≤-linear-height : (S : Tree n) → .⦃ _ : is-linear S ⦄
                        → (T : Tree m)
                        → (d₁ : ℕ) → (d₂ : ℕ) → .(p : d₁ + d₂ ≤ linear-height T)
                        → .(d₂ < tree-dim S)
                        → .(d₁ + tree-dim S ≥ tree-dim T)
                        → (b : Bool)
                        → (Z : Path (tree-bd d₂ S)) → .⦃ is-Maximal Z ⦄
                        → label-from-linear-tree-unbiased S T d₁ (tree-inc-label′ d₂ S b Z)
                        ≃stm SPath (tree-inc-label′ (d₁ + d₂) T b (is-linear-max-path (tree-bd (d₁ + d₂) T) ⦃ bd-linear-height (d₁ + d₂) T p ⦄))
  lfltu-≤-linear-height Sing T d₁ d₂ p () r
  lfltu-≤-linear-height (Join S Sing) T d₁ zero p q r false PHere = let
    .p′ : d₁ ≤ linear-height T
    p′ = ≤-trans (≤-reflexive (sym (+-identityʳ d₁))) p
    instance _ = bd-linear-height d₁ T p′
    instance _ = bd-linear-height (d₁ + zero) T p
    in begin
    < unbiased-stm d₁ (tree-bd d₁ T) >>= tree-inc-label d₁ T false >stm
      ≈⟨ extend-≃ (unbiased-stm-linear d₁ (tree-bd d₁ T) (sym (tree-dim-bd′ d₁ T (≤-trans p′ (linear-height-dim T))))) (refl≃l {L = ap (tree-inc-label d₁ T false)}) refl≃sty ⟩
    < SPath (tree-inc-label′ d₁ T false (is-linear-max-path (tree-bd d₁ T))) >stm
      ≈˘⟨ lfltu-≤-linear-height-lem (+-identityʳ d₁) T false p ⟩
    < SPath (tree-inc-label′ (d₁ + zero) T false (is-linear-max-path (tree-bd (d₁ + zero) T))) >stm ∎
  lfltu-≤-linear-height (Join S Sing) T d₁ zero p q r true PHere = let
    .p′ : d₁ ≤ linear-height T
    p′ = ≤-trans (≤-reflexive (sym (+-identityʳ d₁))) p
    instance _ = bd-linear-height d₁ T p′
    instance _ = bd-linear-height (d₁ + zero) T p
    in begin
    < unbiased-stm d₁ (tree-bd d₁ T) >>= tree-inc-label d₁ T true >stm
      ≈⟨ extend-≃ (unbiased-stm-linear d₁ (tree-bd d₁ T) (sym (tree-dim-bd′ d₁ T (≤-trans p′ (linear-height-dim T))))) (refl≃l {L = ap (tree-inc-label d₁ T true)}) refl≃sty ⟩
    < SPath (tree-inc-label′ d₁ T true (is-linear-max-path (tree-bd d₁ T))) >stm
      ≈˘⟨ lfltu-≤-linear-height-lem (+-identityʳ d₁) T true p ⟩
    < SPath (tree-inc-label′ (d₁ + zero) T true (is-linear-max-path (tree-bd (d₁ + zero) T))) >stm ∎
  lfltu-≤-linear-height (Join S Sing) T d₁ (suc d₂) p q r b (PExt Z) = let
    .p′ : suc (d₁ + d₂) ≤ linear-height T
    p′ = ≤-trans (≤-reflexive (sym (+-suc d₁ d₂))) p
    instance _ = bd-linear-height (suc d₁ + d₂) T p′
    instance _ = bd-linear-height (d₁ + suc d₂) T p
    in begin
    < label-from-linear-tree-unbiased S T (suc d₁)
        (tree-inc-label′ d₂ S b Z) >stm
      ≈⟨ lfltu-≤-linear-height S T (suc d₁) d₂ p′ (≤-pred q) (≤-trans r (≤-reflexive (+-suc d₁ (tree-dim S)))) b Z ⟩
    < SPath (tree-inc-label′ (suc d₁ + d₂) T b (is-linear-max-path (tree-bd (suc d₁ + d₂) T))) >stm
      ≈˘⟨ lfltu-≤-linear-height-lem (+-suc d₁ d₂) T b p ⟩
    < SPath (tree-inc-label′ (d₁ + suc d₂) T b (is-linear-max-path (tree-bd (d₁ + suc d₂) T))) >stm ∎
  lfltu-≤-linear-height (Join S Sing) T d₁ (suc d₂) p q r b (PShift PHere) = ⊥-elim it

  lfltu->-linear-height : (S : Tree n) → .⦃ _ : is-linear S ⦄
                        → (T : Tree m)
                        → (d₁ : ℕ) → (d₂ : ℕ)
                        → .(d₁ + tree-dim S ≥ tree-dim T)
                        → .(d₁ + d₂ > linear-height T)
                        → .(d₂ ≤ tree-dim S)
                        → (b : Bool)
                        → (Z : Path (tree-bd d₂ S)) → .⦃ _ : is-Maximal Z ⦄
                        → label-from-linear-tree-unbiased S T d₁ (tree-inc-label′ d₂ S b Z) ≃stm (unbiased-comp′ (d₂ + d₁) (tree-bd (d₂ + d₁) T) >>= tree-inc-label (d₂ + d₁) T b)
  lfltu->-linear-height Sing T d₁ zero p q r b Z = let
    .p′ : tree-dim T ≤ d₁
    p′ = ≤-trans p (≤-reflexive (+-identityʳ d₁))
    in begin
    < unbiased-comp′ d₁ T >stm
      ≈˘⟨ unbiased-comp′-≃ refl (≃′-to-≃ (tree-bd-full d₁ T p′)) ⟩
    < unbiased-comp′ d₁ (tree-bd d₁ T) >stm
      ≈˘⟨ extend-id (unbiased-comp′ d₁ (tree-bd d₁ T)) ⟩
    < unbiased-comp′ d₁ (tree-bd d₁ T) >>= id-label-wt (tree-bd d₁ T) >stm
      ≈⟨ extend-≃ (refl≃stm {a = unbiased-comp′ d₁ (tree-bd d₁ T)}) [ (λ P → ≃SPath (ppath-≃-≃p (tree-bd-full d₁ T p′) P )) ] [ (Star≃ (cong suc (≃-to-same-n (≃′-to-≃ (tree-bd-full d₁ T p′))))) ]
      ⟩
    < unbiased-comp′ d₁ (tree-bd d₁ T)
      >>= (λ z → SPath (ppath-≃ (tree-bd-full d₁ T p′) z)) ,, S⋆ >stm
      ≈˘⟨ extend-≃ (refl≃stm {a = unbiased-comp′ d₁ (tree-bd d₁ T)}) [ (λ P → ≃SPath (tree-inc-label-full d₁ T b p′ .get P)) ] refl≃sty ⟩
    < unbiased-comp′ d₁ (tree-bd d₁ T) >>= tree-inc-label d₁ T b >stm ∎
  lfltu->-linear-height (Join S Sing) T d₁ (suc d₂) p q r b (PExt Z) = begin
    < label-from-linear-tree-unbiased S T (suc d₁)
         (tree-inc-label′ d₂ S b Z) >stm
      ≈⟨ lfltu->-linear-height S T (suc d₁) d₂ (≤-trans p (≤-reflexive (+-suc d₁ (tree-dim S)))) (<-transˡ q (≤-reflexive (+-suc d₁ d₂))) (≤-pred r) b Z ⟩
    < unbiased-comp′ (d₂ + suc d₁) (tree-bd (d₂ + suc d₁) T)
      >>= tree-inc-label (d₂ + suc d₁) T b >stm
      ≈⟨ reflexive≃stm (cong (λ - → unbiased-comp′ - (tree-bd - T) >>= tree-inc-label - T b) (+-suc d₂ d₁)) ⟩
    < unbiased-comp′ (suc d₂ + d₁) (tree-bd (suc d₂ + d₁) T)
      >>= tree-inc-label (suc d₂ + d₁) T b >stm ∎
  lfltu->-linear-height (Join S Sing) T d₁ (suc d₂) p q r b (PShift PHere) = ⊥-elim it
  lfltu->-linear-height (Join S Sing) T (suc d₁) zero p q r false PHere
    = extend-≃ (unbiased-stm-bd-non-linear (suc d₁) T (<-transˡ q (s≤s (≤-reflexive (+-identityʳ d₁))))) refl≃l refl≃sty
  lfltu->-linear-height (Join S Sing) T (suc d₁) zero p q r true PHere
    = extend-≃ (unbiased-stm-bd-non-linear (suc d₁) T (<-transˡ q (s≤s (≤-reflexive (+-identityʳ d₁))))) refl≃l refl≃sty

unbiased-type-susp-lem : (d : ℕ) → (T : Tree n) → susp-sty (unbiased-type d T) ≃sty unbiased-type (suc d) (suspTree T)
unbiased-comp-susp-lem : (d : ℕ) → (T : Tree n) → SExt {T = Sing} (unbiased-comp d T) ≃stm unbiased-comp (suc d) (suspTree T)

unbiased-type-susp-lem zero T = ≃SArr [ refl≃tm ] refl≃sty [ refl≃tm ]
unbiased-type-susp-lem (suc d) T = ≃SArr (lem false) (unbiased-type-susp-lem d T) (lem true)
  where
    open Reasoning stm-setoid
    lem : (b : Bool) → susp-stm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm (unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (suspTree T) b))
    lem b = begin
      < SExt (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm
        ≈˘⟨ extend-map-pext (unbiased-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < unbiased-stm d (tree-bd d T) >>= map-pext (tree-inc-label d T b) >stm
        ≈⟨ extend-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
      < unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (suspTree T) b) >stm ∎

unbiased-comp-susp-lem d T = begin
  < SExt (unbiased-comp d T) >stm
    ≈˘⟨ SCoh-ext T (unbiased-type d T) (id-label-wt T) ⟩
  < SCoh T (unbiased-type d T) (map-pext (id-label-wt T)) >stm
    ≈⟨ SCoh-unrestrict T (unbiased-type d T) (map-pext (id-label-wt T)) ⟩
  < SCoh (suspTree T) (susp-sty (unbiased-type d T)) (susp-label-full (id-label T) ,, S⋆) >stm
    ≈⟨ ≃SCoh (suspTree T) (unbiased-type-susp-lem d T) (id-label-susp-full T) refl≃sty ⟩
  < unbiased-comp (suc d) (suspTree T) >stm ∎
  where
    open Reasoning stm-setoid

unbiased-comp′-compat : (d : ℕ) → (T : Tree n) → unbiased-comp′ d T ≃stm unbiased-comp d T
unbiased-comp′-compat zero T = refl≃stm
unbiased-comp′-compat (suc d) Sing = refl≃stm
unbiased-comp′-compat (suc d) (Join T Sing) = begin
  < SExt (unbiased-comp′ d T) >stm
    ≈⟨ ≃SExt (unbiased-comp′-compat d T) Sing≃ ⟩
  < SExt (unbiased-comp d T) >stm
    ≈⟨ unbiased-comp-susp-lem d T ⟩
  < unbiased-comp (suc d) (Join T Sing) >stm ∎
  where
    open Reasoning stm-setoid
unbiased-comp′-compat (suc d) T@(Join _ (Join _ _)) = refl≃stm

lfltu-susp : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → (label-from-linear-tree-unbiased S (suspTree T) (suc d)) ≃l (SExt {T = Sing} ∘ label-from-linear-tree-unbiased S T d)
lfltu-susp Sing T d .get PHere = refl≃stm
lfltu-susp (Join S Sing) T d .get PHere = begin
  < unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (suspTree T) false) >stm
    ≈⟨ extend-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
  < unbiased-stm d (tree-bd d T) >>= map-pext (tree-inc-label d T false) >stm
    ≈⟨ extend-map-pext (unbiased-stm d (tree-bd d T)) (tree-inc-label d T false) ⟩
  < SExt (unbiased-stm d (tree-bd d T) >>= (tree-inc-label d T false)) >stm ∎
  where
    open Reasoning stm-setoid
lfltu-susp (Join S Sing) T d .get (PExt Z) = lfltu-susp S T (suc d) .get Z
lfltu-susp (Join S Sing) T d .get (PShift PHere) = begin
  < unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (suspTree T) true) >stm
    ≈⟨ extend-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
  < unbiased-stm d (tree-bd d T) >>= map-pext (tree-inc-label d T true) >stm
    ≈⟨ extend-map-pext (unbiased-stm d (tree-bd d T)) (tree-inc-label d T true) ⟩
  < SExt (unbiased-stm d (tree-bd d T) >>= (tree-inc-label d T true)) >stm ∎
  where
    open Reasoning stm-setoid


{-
unbiased-term-susp-lem : (d : ℕ) → (T : Tree n) → suspTm (unbiased-term d T) ≃tm unbiased-term (suc d) (suspTree T)
unbiased-type-susp-lem : (d : ℕ) → (T : Tree n) → suspTy (unbiased-type d T) ≃ty unbiased-type (suc d) (suspTree T)
unbiased-comp-susp-lem : (d : ℕ) → (T : Tree n) → suspTm (unbiased-comp d T) ≃tm unbiased-comp (suc d) (suspTree T)

unbiased-term-susp-lem d T with is-linear-dec T
... | yes p = refl≃tm
... | no p = unbiased-comp-susp-lem d T

unbiased-type-susp-lem zero T = refl≃ty
unbiased-type-susp-lem (suc d) T = Arr≃ (l1 false) (unbiased-type-susp-lem d T) (l1 true)
  where
    l1 : (b : Bool)
       → suspTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm)
           ≃tm
         unbiased-term (suc d) (tree-bd (suc d) (suspTree T))
           [ tree-inc (suc d) (suspTree T) b ]tm
    l1 b = begin
      < suspTm (unbiased-term d (tree-bd d T) [ tree-inc d T b ]tm) >tm
        ≈⟨ susp-functorial-tm (tree-inc d T b) (unbiased-term d (tree-bd d T)) ⟩
      < suspTm (unbiased-term d (tree-bd d T))
          [ suspSub (tree-inc d T b) ]tm >tm
        ≈⟨ sub-action-≃-tm (unbiased-term-susp-lem d (tree-bd d T)) (tree-inc-susp-lem d T b) ⟩
      < unbiased-term (suc d) (tree-bd (suc d) (suspTree T))
          [ tree-inc (suc d) (suspTree T) b ]tm >tm ∎
      where
        open Reasoning tm-setoid

unbiased-comp-susp-lem d T = Coh≃ refl≃c (unbiased-type-susp-lem d T) susp-functorial-id

linear-tree-unbiased-lem : (d : ℕ) → (T : Tree n) → .⦃ is-linear T ⦄ → .(tree-dim T ≡ d) → tree-to-ctx T ‼ zero ≃ty unbiased-type d T
linear-tree-unbiased-lem zero Sing p = Star≃ refl
linear-tree-unbiased-lem zero (Join S T) ()
linear-tree-unbiased-lem (suc d) (Join S Sing) p = begin
  < suspCtx (tree-to-ctx S) ‼ zero >ty
    ≈⟨ susp-‼ (tree-to-ctx S) zero ⟩
  < suspTy (tree-to-ctx S ‼ zero) >ty
    ≈⟨ susp-ty-≃ (linear-tree-unbiased-lem d S (cong pred p)) ⟩
  < suspTy (unbiased-type d S) >ty
    ≈⟨ unbiased-type-susp-lem d S ⟩
  < unbiased-type (suc d) (Join S Sing) >ty ∎
  where
    open Reasoning ty-setoid

sub-from-linear-tree-unbiased-0V : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → 0V [ sub-from-linear-tree-unbiased S T d ]tm ≃tm unbiased-comp (d + tree-dim S) T
sub-from-linear-tree-unbiased-0V Sing T d = unbiased-comp-≃ (sym (+-identityʳ d)) refl≃
sub-from-linear-tree-unbiased-0V (Join S Sing) T d = trans≃tm (unrestrict-comp-tm 0V (sub-from-linear-tree-unbiased S T (suc d))) (trans≃tm (sub-from-linear-tree-unbiased-0V S T (suc d)) (unbiased-comp-≃ (sym (+-suc d (tree-dim S))) refl≃))

sub-from-linear-tree-0V : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (t : Tm m) → (A : Ty m) → (p : ty-dim A ≡ tree-dim S) → 0V [ sub-from-linear-tree S t A p ]tm ≃tm t
sub-from-linear-tree-0V Sing t A p = refl≃tm
sub-from-linear-tree-0V (Join S Sing) t (s ─⟨ A ⟩⟶ s′) p = refl≃tm

sub-from-linear-tree-‼-0 : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (t : Tm m) → (A : Ty m) → (p : ty-dim A ≡ tree-dim S) → tree-to-ctx S ‼ zero [ sub-from-linear-tree S t A p ]ty ≃ty A
sub-from-linear-tree-‼-0 Sing t ⋆ p = refl≃ty
sub-from-linear-tree-‼-0 (Join S Sing) t (s ─⟨ A ⟩⟶ s′) p = begin
  < suspCtx (tree-to-ctx S) ‼ zero [ ⟨ ⟨ sub-from-linear-tree S s A (cong pred p) , s′ ⟩ , t ⟩ ]ty >ty
    ≈⟨ sub-action-≃-ty (‼-≃ zero zero refl (susp-lin-tree S)) refl≃s ⟩
  < ((0V [ sub-from-linear-tree S s A (cong pred p) ]tm)
    ─⟨ liftType (liftType (tree-to-ctx S ‼ zero))
       [ ⟨ ⟨ sub-from-linear-tree S s A (cong pred p) , s′ ⟩ , t ⟩ ]ty
       ⟩⟶ s′) >ty
    ≈⟨ Arr≃ (sub-from-linear-tree-0V S s A (cong pred p)) lem refl≃tm ⟩
  < s ─⟨ A ⟩⟶ s′ >ty ∎
  where
    open Reasoning ty-setoid

    lem : liftType (liftType (tree-to-ctx S ‼ zero))
            [ ⟨ ⟨ sub-from-linear-tree S s A (cong pred p) , s′ ⟩ , t ⟩ ]ty
            ≃ty A
    lem = begin
      < liftType (liftType (tree-to-ctx S ‼ zero))
        [ ⟨ ⟨ sub-from-linear-tree S s A _ , s′ ⟩ , t ⟩ ]ty >ty
        ≈⟨ lift-sub-comp-lem-ty ⟨ sub-from-linear-tree S s A _ , s′ ⟩ (liftType (tree-to-ctx S ‼ zero)) ⟩
      < liftType (tree-to-ctx S ‼ zero) [ ⟨ sub-from-linear-tree S s A _ , s′ ⟩ ]ty >ty
        ≈⟨ lift-sub-comp-lem-ty (sub-from-linear-tree S s A _) (tree-to-ctx S ‼ zero) ⟩
      < tree-to-ctx S ‼ zero [ sub-from-linear-tree S s A _ ]ty >ty
        ≈⟨ sub-from-linear-tree-‼-0 S s A (cong pred p) ⟩
      < A >ty ∎

unbiased-term-disc : (n : ℕ) → unbiased-term n (n-disc n) ≃tm 0V {suc (n * 2)}
unbiased-term-disc zero = refl≃tm
unbiased-term-disc (suc n) = trans≃tm (sym≃tm (unbiased-term-susp-lem n (n-disc n))) (susp-tm-≃ (unbiased-term-disc n))

unbiased-type-disc : (n : ℕ) → unbiased-type n (n-disc n) ≃ty (tree-to-ctx (n-disc n)) ‼ zero
unbiased-type-disc zero = refl≃ty
unbiased-type-disc (suc n) = begin
  < unbiased-type (suc n) (n-disc (suc n)) >ty
    ≈˘⟨ unbiased-type-susp-lem n (n-disc n) ⟩
  < suspTy (unbiased-type n (n-disc n)) >ty
    ≈⟨ susp-ty-≃ (unbiased-type-disc n) ⟩
  < suspTy (tree-to-ctx (n-disc n) ‼ zero) >ty
    ≈˘⟨ susp-‼ (tree-to-ctx (n-disc n)) zero ⟩
  < suspCtx (tree-to-ctx (n-disc n)) ‼ zero >ty ∎
  where
    open Reasoning ty-setoid

sub-from-linear-tree-≃ : S ≃ T → .⦃ _ : is-linear S ⦄ → .⦃ _ : is-linear T ⦄ → s ≃tm t → A ≃ty B → (p : ty-dim A ≡ tree-dim S) → (q : ty-dim B ≡ tree-dim T) → sub-from-linear-tree S s A p ≃s sub-from-linear-tree T t B q
sub-from-linear-tree-≃ Sing≃ b (Star≃ x) p q = Ext≃ (Null≃ (Star≃ x)) b
sub-from-linear-tree-≃ (Join≃ a Sing≃) b (Arr≃ c d e) p q = Ext≃ (Ext≃ (sub-from-linear-tree-≃ a c d (cong pred p) (cong pred q)) e) b

sub-from-linear-tree-sub : (a : S ≃ T) → .⦃ _ : is-linear S ⦄ → .⦃ _ : is-linear T ⦄ → (t : Tm m) → (A : Ty m) → (p : ty-dim A ≡ tree-dim S) → (σ : Sub m l ⋆) → σ ∘ sub-from-linear-tree S t A p ≃s sub-from-linear-tree T (t [ σ ]tm) (A [ σ ]ty) (trans (sym (sub-dim σ A)) (trans p (tree-dim-≃ a)))
sub-from-linear-tree-sub Sing≃ t A p σ = refl≃s
sub-from-linear-tree-sub (Join≃ a Sing≃) t (s ─⟨ A ⟩⟶ s′) p σ = Ext≃ (Ext≃ (sub-from-linear-tree-sub a s A (cong pred p) σ) refl≃tm) refl≃tm

identity-tree-sub : (t : Tm n) → (A : Ty n) → (σ : Sub n m ⋆) → identity-tree t A [ σ ]tm ≃tm identity-tree (t [ σ ]tm) (A [ σ ]ty)
identity-tree-sub t A σ = Coh≃ (tree-to-ctx-≃ (n-disc-≃ (sub-dim σ A))) (unbiased-type-≃ (cong suc (sub-dim σ A)) (n-disc-≃ (sub-dim σ A))) (sub-from-linear-tree-sub (n-disc-≃ (sub-dim σ A)) ⦃ n-disc-is-linear (ty-dim A) ⦄ ⦃ n-disc-is-linear (ty-dim (A [ σ ]ty)) ⦄ t A (sym (tree-dim-n-disc (ty-dim A))) σ)

identity-tree-≃ : s ≃tm t → A ≃ty B → identity-tree s A ≃tm identity-tree t B
identity-tree-≃ {A = A} {B = B} p q = Coh≃ (tree-to-ctx-≃ (n-disc-≃ (ty-dim-≃ q))) (unbiased-type-≃ (cong suc (ty-dim-≃ q)) (n-disc-≃ (ty-dim-≃ q))) (sub-from-linear-tree-≃ (n-disc-≃ (ty-dim-≃ q)) ⦃ n-disc-is-linear (ty-dim A) ⦄ ⦃ n-disc-is-linear (ty-dim B) ⦄ p q (sym (tree-dim-n-disc (ty-dim A))) (sym (tree-dim-n-disc (ty-dim B))))
-}

label-from-linear-tree-type-≃ : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (As ≃sty Bs) → label-from-linear-tree-type S As ≃sty label-from-linear-tree-type S Bs
label-from-linear-tree-type-≃ Sing p = p
label-from-linear-tree-type-≃ (Join S Sing) p = label-from-linear-tree-type-≃ S (sty-base-≃ p)

label-from-linear-tree-≃ : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (a ≃stm b) → (q : As ≃sty Bs) → .(r : tree-dim S ≤ sty-dim As) → label-from-linear-tree S a As r ≃l label-from-linear-tree S b Bs (≤-trans r (≤-reflexive (sty-dim-≃ q)))
label-from-linear-tree-≃ Sing p q r .get P = p
label-from-linear-tree-≃ (Join S Sing) p q r .get PHere = sty-src-≃ (label-from-linear-tree-type-≃ S q) ⦃ _ ⦄
label-from-linear-tree-≃ (Join S Sing) p q r .get (PExt P) = label-from-linear-tree-≃ S p q _ .get P
label-from-linear-tree-≃ (Join S Sing) p q r .get (PShift PHere) = sty-tgt-≃ (label-from-linear-tree-type-≃ S q) ⦃ _ ⦄

label-from-linear-tree-unbiased-type-lem : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → label-from-linear-tree-type S (unbiased-type (tree-dim S + d) T) ≃sty unbiased-type d T
label-from-linear-tree-unbiased-type-lem Sing T d = refl≃sty
label-from-linear-tree-unbiased-type-lem (Join S Sing) T d = label-from-linear-tree-unbiased-type-lem S T d

label-from-linear-tree-unbiased-lem
  : (S : Tree n)
  → .⦃ _ : is-linear S ⦄
  → (T : Tree m)
  → (d : ℕ)
  → label-from-linear-tree S (unbiased-comp′ (tree-dim S + d) T)
                             (unbiased-type (tree-dim S + d) T)
                             (≤-trans (m≤m+n (tree-dim S) d) (≤-reflexive (sym (unbiased-type-dim (tree-dim S + d) T))))
  ≃l label-from-linear-tree-unbiased S T d
label-from-linear-tree-unbiased-lem Sing T d .get P = refl≃stm
label-from-linear-tree-unbiased-lem (Join S Sing) T d .get PHere = begin
  < sty-src (label-from-linear-tree-type S (unbiased-type (suc (tree-dim S) + d) T)) ⦃ _ ⦄ >stm
    ≈⟨ sty-src-≃ (label-from-linear-tree-type-≃ S (unbiased-type-≃ (sym (+-suc (tree-dim S) d)) refl≃)) ⦃ _ ⦄ ⟩
  < sty-src (label-from-linear-tree-type S (unbiased-type (tree-dim S + suc d) T)) ⦃ _ ⦄ >stm
    ≈⟨ sty-src-≃ (label-from-linear-tree-unbiased-type-lem S T (suc d)) ⦃ _ ⦄ ⟩
  < sty-src (unbiased-type (suc d) T) >stm
    ≡⟨⟩
  < unbiased-stm d (tree-bd d T) >>= tree-inc-label d T false >stm ∎
  where
    open Reasoning stm-setoid
label-from-linear-tree-unbiased-lem (Join S Sing) T d .get (PExt P) = begin
  < label-from-linear-tree S
                           (unbiased-comp′ (suc (tree-dim S + d)) T)
                           (unbiased-type (suc (tree-dim S + d)) T)
                           _ P >stm
    ≈⟨ label-from-linear-tree-≃ S (unbiased-comp′-≃ (sym (+-suc (tree-dim S) d)) refl≃) (unbiased-type-≃ (sym (+-suc (tree-dim S) d)) refl≃) _ .get P ⟩
  < label-from-linear-tree S
                           (unbiased-comp′ (tree-dim S + suc d) T)
                           (unbiased-type (tree-dim S + suc d) T)
                           _ P >stm
    ≈⟨ label-from-linear-tree-unbiased-lem S T (suc d) .get P ⟩
  < label-from-linear-tree-unbiased S T (suc d) P >stm ∎
  where
    open Reasoning stm-setoid
label-from-linear-tree-unbiased-lem (Join S Sing) T d .get (PShift PHere) = begin
  < sty-tgt (label-from-linear-tree-type S (unbiased-type (suc (tree-dim S) + d) T)) ⦃ _ ⦄ >stm
    ≈⟨ sty-tgt-≃ (label-from-linear-tree-type-≃ S (unbiased-type-≃ (sym (+-suc (tree-dim S) d)) refl≃)) ⦃ _ ⦄ ⟩
  < sty-tgt (label-from-linear-tree-type S (unbiased-type (tree-dim S + suc d) T)) ⦃ _ ⦄ >stm
    ≈⟨ sty-tgt-≃ (label-from-linear-tree-unbiased-type-lem S T (suc d)) ⦃ _ ⦄ ⟩
  < sty-tgt (unbiased-type (suc d) T) >stm
    ≡⟨⟩
  < unbiased-stm d (tree-bd d T) >>= tree-inc-label d T true >stm ∎
  where
    open Reasoning stm-setoid

label-from-linear-tree-unbiased-lem-0 :
    (S : Tree n)
  → .⦃ _ : is-linear S ⦄
  → (T : Tree m)
  → (d : ℕ)
  → (p : tree-dim S ≡ d)
  → label-from-linear-tree S (unbiased-comp′ d T)
                             (unbiased-type d T)
                             (≤-reflexive (trans p (sym (unbiased-type-dim d T))))
  ≃l label-from-linear-tree-unbiased S T 0
label-from-linear-tree-unbiased-lem-0 S T d p = begin
  < label-from-linear-tree S (unbiased-comp′ d T)
                             (unbiased-type d T) _ >l
    ≈˘⟨ label-from-linear-tree-≃ S (unbiased-comp′-≃ (trans (+-identityʳ (tree-dim S)) p) refl≃) (unbiased-type-≃ (trans (+-identityʳ (tree-dim S)) p) refl≃) _ ⟩
  < label-from-linear-tree S (unbiased-comp′ (tree-dim S + 0) T)
                             (unbiased-type (tree-dim S + 0) T) _ >l
    ≈⟨ label-from-linear-tree-unbiased-lem S T 0 ⟩
  < label-from-linear-tree-unbiased S T 0 >l ∎
  where
    open Reasoning (label-setoid S)

label-from-linear-tree-type-prop : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (As : STy X) → label-from-linear-tree-type S (sty-base As) ≃sty sty-base (label-from-linear-tree-type S As)
label-from-linear-tree-type-prop Sing As = refl≃sty
label-from-linear-tree-type-prop (Join S Sing) As = label-from-linear-tree-type-prop S (sty-base As)

truncate-unbiased-sty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → truncate-sty 1 (unbiased-type d T) ≃sty SArr SHere S⋆ (SPath (last-path T))
truncate-unbiased-sty (suc zero) T = refl≃sty
truncate-unbiased-sty (suc (suc d)) T = begin
  < truncate-sty 1 (unbiased-type (suc (suc d)) T) >sty
    ≈⟨ truncate-sty-≤ 1 (unbiased-type (2 + d) T) (s≤s (s≤s z≤n)) ⟩
  < truncate-sty 1 (unbiased-type (1 + d) T) >sty
    ≈⟨ truncate-unbiased-sty (suc d) T ⟩
  < SArr SHere S⋆ (SPath (last-path T)) >sty ∎
  where
    open Reasoning sty-setoid
