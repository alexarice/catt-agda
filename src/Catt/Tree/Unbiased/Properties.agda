module Catt.Tree.Unbiased.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Globular.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Unbiased

unbiased-type-dim : (d : ℕ) → (T : Tree n) → sty-dim (unbiased-type d T) ≡ d
unbiased-type-dim zero T = refl
unbiased-type-dim (suc d) T = cong suc (unbiased-type-dim d T)

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

unbiased-stm-≃-prop : (d : ℕ) → (p : S ≃′ T) → (unbiased-stm d S >>= (SPath ∘ ppath-≃ p ,, S⋆)) ≃stm unbiased-stm d T
unbiased-stm-≃-prop {S = S} {T = T} d p = begin
  < unbiased-stm d S >>= (SPath ∘ ppath-≃ p ,, S⋆) >stm
    ≈⟨ >>=-≃ (refl≃stm {a = unbiased-stm d S}) (ppath-≃l p) (S⋆-≃ (sym≃ (≃′-to-≃ p))) ⟩
  < unbiased-stm d S >>= id-label-wt S >stm
    ≈⟨ >>=-id (unbiased-stm d S) ⟩
  < unbiased-stm d S >stm
    ≈⟨ unbiased-stm-≃ refl (≃′-to-≃ p) ⟩
  < unbiased-stm d T >stm ∎
  where open Reasoning stm-setoid

unbiased-stm-linear : (d : ℕ) → (T : Tree n) → .⦃ _ : is-linear T ⦄ → .(d ≡ tree-dim T) → unbiased-stm d T ≃stm SPath (is-linear-max-path T)
unbiased-stm-linear zero Sing p = [ refl≃tm ]
unbiased-stm-linear (suc d) (Join T Sing) p = compute-≃ (SExt≃ (unbiased-stm-linear d T (cong pred p)) refl≃)

unbiased-stm-bd-non-linear : (d : ℕ) → (T : Tree n) → .(d > linear-height T) → unbiased-stm d (tree-bd d T) ≃stm unbiased-comp′ d (tree-bd d T)
unbiased-stm-bd-non-linear (suc d) Sing p = refl≃stm
unbiased-stm-bd-non-linear (suc d) (Join T Sing) p = SExt≃ (unbiased-stm-bd-non-linear d T (≤-pred p)) Sing≃
unbiased-stm-bd-non-linear (suc d) (Join T (Join T₁ T₂)) p = refl≃stm

unbiased-stm-full-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → (tree-dim T ≤ d) → (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm unbiased-stm d T
unbiased-stm-full-lem d T b p = begin
  < unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b >stm
    ≈⟨ >>=-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → SPath≃ (tree-inc-label-full d T b p .get P)) ] refl≃sty ⟩
  < unbiased-stm d (tree-bd d T) >>= ((λ z → SPath (ppath-≃ (tree-bd-full d T p) z)) ,, S⋆) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → SPath≃ (ppath-≃-≃p (tree-bd-full d T p) P)) ] [ (Star≃ (cong suc (≃-to-same-n (≃′-to-≃ (tree-bd-full d T p))))) ] ⟩
  < unbiased-stm d (tree-bd d T) >>= id-label-wt (tree-bd d T) >stm
    ≈⟨ >>=-id (unbiased-stm d (tree-bd d T)) ⟩
  < unbiased-stm d (tree-bd d T) >stm
    ≈⟨ unbiased-stm-≃ refl (≃′-to-≃ (tree-bd-full d T p)) ⟩
  < unbiased-stm d T >stm ∎
  where
    open Reasoning stm-setoid

unbiased-term-≃ : (d ≡ d′) → S ≃ T → unbiased-term d S ≃tm unbiased-term d′ T
unbiased-term-≃ refl p with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = refl≃tm

unbiased-type-prop : (d : ℕ) → (T : Tree n) → (d′ : ℕ) → (d ≤ d′) → (b : Bool) → unbiased-type d T ≃sty unbiased-type d (tree-bd d′ T) >>=′ tree-inc-label d′ T b
unbiased-type-prop zero T d′ p b = refl≃sty
unbiased-type-prop (suc d) T d′ p b = SArr≃ (lem false) (unbiased-type-prop d T d′ (≤-trans (n≤1+n d) p) b) (lem true)
  where
    lem : (b′ : Bool) → (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b′)
      ≃stm (unbiased-stm d (tree-bd d (tree-bd d′ T)) >>=
        tree-inc-label d (tree-bd d′ T) b′ >>= tree-inc-label d′ T b)
    lem b′ = begin
      < unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b′ >stm
        ≈˘⟨ >>=-≃′ (unbiased-stm-≃ {d = d} refl (≃′-to-≃ (tree-bd-glob d d′ T p))) ((tree-bd-glob d d′ T p) ,, [ (λ P → SPath≃ (tree-inc-label-glob d d′ T b′ b p .get P)) ]) refl≃sty ⟩
      < unbiased-stm d (tree-bd d (tree-bd d′ T))
        >>= tree-inc-label d (tree-bd d′ T) b′ ●lt tree-inc-label d′ T b >stm
        ≈˘⟨ >>=-assoc (unbiased-stm d (tree-bd d (tree-bd d′ T))) _ _ ⟩
      < unbiased-stm d (tree-bd d (tree-bd d′ T))
        >>= tree-inc-label d (tree-bd d′ T) b′
        >>= tree-inc-label d′ T b >stm ∎
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
      ≈⟨ >>=-≃ (unbiased-stm-linear d₁ (tree-bd d₁ T) (sym (tree-dim-bd′ d₁ T (≤-trans p′ (linear-height-dim T))))) (refl≃l {L = ap (tree-inc-label d₁ T false)}) refl≃sty ⟩
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
      ≈⟨ >>=-≃ (unbiased-stm-linear d₁ (tree-bd d₁ T) (sym (tree-dim-bd′ d₁ T (≤-trans p′ (linear-height-dim T))))) (refl≃l {L = ap (tree-inc-label d₁ T true)}) refl≃sty ⟩
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
      ≈˘⟨ >>=-id (unbiased-comp′ d₁ (tree-bd d₁ T)) ⟩
    < unbiased-comp′ d₁ (tree-bd d₁ T) >>= id-label-wt (tree-bd d₁ T) >stm
      ≈⟨ >>=-≃ (refl≃stm {a = unbiased-comp′ d₁ (tree-bd d₁ T)}) [ (λ P → SPath≃ (ppath-≃-≃p (tree-bd-full d₁ T p′) P )) ] [ (Star≃ (cong suc (≃-to-same-n (≃′-to-≃ (tree-bd-full d₁ T p′))))) ]
      ⟩
    < unbiased-comp′ d₁ (tree-bd d₁ T)
      >>= ((λ z → SPath (ppath-≃ (tree-bd-full d₁ T p′) z)) ,, S⋆) >stm
      ≈˘⟨ >>=-≃ (refl≃stm {a = unbiased-comp′ d₁ (tree-bd d₁ T)}) [ (λ P → SPath≃ (tree-inc-label-full d₁ T b p′ .get P)) ] refl≃sty ⟩
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
    = >>=-≃ (unbiased-stm-bd-non-linear (suc d₁) T (<-transˡ q (s≤s (≤-reflexive (+-identityʳ d₁))))) refl≃l refl≃sty
  lfltu->-linear-height (Join S Sing) T (suc d₁) zero p q r true PHere
    = >>=-≃ (unbiased-stm-bd-non-linear (suc d₁) T (<-transˡ q (s≤s (≤-reflexive (+-identityʳ d₁))))) refl≃l refl≃sty

unbiased-type-susp-lem : (d : ℕ) → (T : Tree n) → susp-sty (unbiased-type d T) ≃sty unbiased-type (suc d) (susp-tree T)
unbiased-comp-susp-lem : (d : ℕ) → (T : Tree n) → SExt {T = Sing} (unbiased-comp d T) ≃stm unbiased-comp (suc d) (susp-tree T)

unbiased-type-susp-lem zero T = SArr≃ [ refl≃tm ] refl≃sty [ refl≃tm ]
unbiased-type-susp-lem (suc d) T = SArr≃ (lem false) (unbiased-type-susp-lem d T) (lem true)
  where
    open Reasoning stm-setoid
    lem : (b : Bool) → susp-stm (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm (unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) b))
    lem b = begin
      < SExt (unbiased-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm
        ≈˘⟨ >>=-ext (unbiased-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < unbiased-stm d (tree-bd d T) >>= map-ext (tree-inc-label d T b) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
      < unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) b) >stm ∎

unbiased-comp-susp-lem d T = begin
  < SExt (unbiased-comp d T) >stm
    ≈˘⟨ SCoh-ext T (unbiased-type d T) (id-label-wt T) ⟩
  < SCoh T (unbiased-type d T) (map-ext (id-label-wt T)) >stm
    ≈⟨ SCoh-unrestrict T (unbiased-type d T) (map-ext (id-label-wt T)) ⟩
  < SCoh (susp-tree T) (susp-sty (unbiased-type d T)) (susp-label-full (id-label T) ,, S⋆) >stm
    ≈⟨ SCoh≃ (susp-tree T) (unbiased-type-susp-lem d T) (id-label-susp-full T) refl≃sty ⟩
  < unbiased-comp (suc d) (susp-tree T) >stm ∎
  where
    open Reasoning stm-setoid

unbiased-comp′-compat : (d : ℕ) → (T : Tree n) → unbiased-comp′ d T ≃stm unbiased-comp d T
unbiased-comp′-compat zero T = refl≃stm
unbiased-comp′-compat (suc d) Sing = refl≃stm
unbiased-comp′-compat (suc d) (Join T Sing) = begin
  < SExt (unbiased-comp′ d T) >stm
    ≈⟨ SExt≃ (unbiased-comp′-compat d T) Sing≃ ⟩
  < SExt (unbiased-comp d T) >stm
    ≈⟨ unbiased-comp-susp-lem d T ⟩
  < unbiased-comp (suc d) (Join T Sing) >stm ∎
  where
    open Reasoning stm-setoid
unbiased-comp′-compat (suc d) T@(Join _ (Join _ _)) = refl≃stm

lfltu-susp : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → (label-from-linear-tree-unbiased S (susp-tree T) (suc d)) ≃l (SExt {T = Sing} ∘ label-from-linear-tree-unbiased S T d)
lfltu-susp Sing T d .get PHere = refl≃stm
lfltu-susp (Join S Sing) T d .get PHere = begin
  < unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) false) >stm
    ≈⟨ >>=-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
  < unbiased-stm d (tree-bd d T) >>= map-ext (tree-inc-label d T false) >stm
    ≈⟨ >>=-ext (unbiased-stm d (tree-bd d T)) (tree-inc-label d T false) ⟩
  < SExt (unbiased-stm d (tree-bd d T) >>= (tree-inc-label d T false)) >stm ∎
  where
    open Reasoning stm-setoid
lfltu-susp (Join S Sing) T d .get (PExt Z) = lfltu-susp S T (suc d) .get Z
lfltu-susp (Join S Sing) T d .get (PShift PHere) = begin
  < unbiased-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) true) >stm
    ≈⟨ >>=-≃ (refl≃stm {a = unbiased-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
  < unbiased-stm d (tree-bd d T) >>= map-ext (tree-inc-label d T true) >stm
    ≈⟨ >>=-ext (unbiased-stm d (tree-bd d T)) (tree-inc-label d T true) ⟩
  < SExt (unbiased-stm d (tree-bd d T) >>= (tree-inc-label d T true)) >stm ∎
  where
    open Reasoning stm-setoid

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

label-from-linear-tree-type-susp : (S : Tree n)
                                 → .⦃ _ : is-linear S ⦄
                                 → (As : STy X)
                                 → .(sty-dim As ≥ tree-dim S)
                                 → label-from-linear-tree-type S (susp-sty As) ≃sty susp-sty (label-from-linear-tree-type S As)
label-from-linear-tree-type-susp Sing As p = refl≃sty
label-from-linear-tree-type-susp (Join S Sing) As@(SArr _ _ _) p = label-from-linear-tree-type-susp S (sty-base As) (≤-pred p)

label-from-linear-tree-susp : (S : Tree n)
                            → .⦃ _ : is-linear S ⦄
                            → (a : STm X)
                            → (As : STy X)
                            → .(p : tree-dim S ≤ sty-dim As)
                            → label-from-linear-tree S (susp-stm a) (susp-sty As) (≤-trans p (≤-trans (n≤1+n (sty-dim As)) (≤-reflexive (sym (susp-sty-dim As))))) ≃l (susp-stm ∘ label-from-linear-tree S a As p)
label-from-linear-tree-susp Sing a As p .get PHere = refl≃stm
label-from-linear-tree-susp (Join S Sing) a As p = begin
  < unrestrict-label
      (label-from-linear-tree S (susp-stm a) (susp-sty As) _ ,,
       label-from-linear-tree-type S (susp-sty As)) ⦃ _ ⦄ >l
    ≈⟨ unrestrict-label-≃ _ _ ⦃ _ ⦄ (label-from-linear-tree-susp S a As _) (label-from-linear-tree-type-susp S As (≤-trans (n≤1+n (tree-dim S)) p)) ⟩
  < unrestrict-label (susp-label (label-from-linear-tree S a As _ ,, label-from-linear-tree-type S As)) ⦃ _ ⦄ >l
    ≈˘⟨ susp-unrestrict-label (label-from-linear-tree S a As _ ,, label-from-linear-tree-type S As) ⦃ label-from-linear-tree-nz S As p ⦄ ⟩
  < (susp-stm ∘
       unrestrict-label
       (label-from-linear-tree S a As _ ,,
        label-from-linear-tree-type S As) ⦃ _ ⦄) >l ∎
  where
    open Reasoning (label-setoid _)

label-from-linear-tree-type-0 : (S : Tree n)
                            → .⦃ _ : is-linear S ⦄
                            → (As : STy X)
                            → .(p : tree-dim S ≡ sty-dim As)
                            → label-from-linear-tree-type S As ≃sty (S⋆ {X = X})
label-from-linear-tree-type-0 Sing S⋆ p = refl≃sty
label-from-linear-tree-type-0 (Join S Sing) (SArr s As t) p = label-from-linear-tree-type-0 S As (cong pred p)

label-from-linear-tree-susp-full : (S : Tree n)
                            → .⦃ _ : is-linear S ⦄
                            → (a : STm X)
                            → (As : STy X)
                            → .(p : tree-dim S ≡ sty-dim As)
                            → label-from-linear-tree (susp-tree S) (susp-stm a) (susp-sty As) (≤-reflexive (trans (cong suc p) (sym (susp-sty-dim As)))) ≃l susp-label-full (label-from-linear-tree S a As (≤-reflexive p))
label-from-linear-tree-susp-full S a As p = unrestrict-label-≃ _ _ ⦃ _ ⦄ (label-from-linear-tree-susp S a As (≤-reflexive p)) (begin
  < label-from-linear-tree-type S (susp-sty As) >sty
    ≈⟨ label-from-linear-tree-type-susp S As (≤-reflexive p) ⟩
  < susp-sty (label-from-linear-tree-type S As) >sty
    ≈⟨ susp-sty-≃ (label-from-linear-tree-type-0 S As p) ⟩
  < SArr stm-fst S⋆ stm-snd >sty ∎)
  where
    open Reasoning sty-setoid

label-from-disc-type-dim-lem : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → tree-dim S + (sty-dim (lty L)) ≡ sty-dim (label-from-disc-type L)
label-from-disc-type-dim-lem {S = Sing} L = refl
label-from-disc-type-dim-lem {S = Join S Sing} L = begin
  suc (tree-dim S) + sty-dim (lty L)
    ≡˘⟨ +-suc (tree-dim S) (sty-dim (proj₂ L)) ⟩
  tree-dim S + suc (sty-dim (lty L))
    ≡⟨ label-from-disc-type-dim-lem (label₁ L) ⟩
  sty-dim (label-from-disc-type (label₁ L)) ∎
  where
    open ≡-Reasoning

label-from-disc-type-lem : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → label-from-linear-tree-type S (label-from-disc-type L) ≃sty lty L
label-from-disc-type-lem {S = Sing} L = refl≃sty
label-from-disc-type-lem {S = Join S Sing} L = begin
  < label-from-linear-tree-type S (sty-base (label-from-disc-type (label₁ L))) >sty
    ≈⟨ label-from-linear-tree-type-prop S (label-from-disc-type (label₁ L)) ⟩
  < sty-base (label-from-linear-tree-type S (label-from-disc-type (label₁ L))) >sty
    ≈⟨ sty-base-≃ (label-from-disc-type-lem (label₁ L)) ⟩
  < lty L >sty ∎
  where
    open Reasoning sty-setoid

label-from-linear-tree-prop : .⦃ _ : is-linear S ⦄ → (L : Label-WT X S) → ap L ≃l label-from-linear-tree S (label-from-disc-term L) (label-from-disc-type L) (≤-trans (m≤m+n (tree-dim S) (sty-dim (lty L))) (≤-reflexive (label-from-disc-type-dim-lem L)))
label-from-linear-tree-prop {S = Sing} L .get PHere = refl≃stm
label-from-linear-tree-prop {S = Join S Sing} L .get PHere = sym≃stm (sty-src-≃ (label-from-disc-type-lem (label₁ L)) ⦃ _ ⦄)
label-from-linear-tree-prop {S = Join S Sing} L .get (PExt P) = label-from-linear-tree-prop (label₁ L) .get P
label-from-linear-tree-prop {S = Join S Sing} L .get (PShift PHere) = sym≃stm (sty-tgt-≃ (label-from-disc-type-lem (label₁ L)) ⦃ _ ⦄)

label-from-disc-type-prop : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → label-from-disc-type L ≃sty unbiased-type (tree-dim S) S >>=′ L
label-from-disc-type-prop {S = Sing} L = refl≃sty
label-from-disc-type-prop {S = Join S Sing} L = begin
  < label-from-disc-type (label₁ L) >sty
    ≈⟨ label-from-disc-type-prop (label₁ L) ⟩
  < unbiased-type (tree-dim S) S >>=′ label₁ L >sty
    ≈˘⟨ map-sty-ext-label (unbiased-type (tree-dim S) S) L ⟩
  < map-sty-ext (unbiased-type (tree-dim S) S) >>=′ L >sty
    ≈⟨ >>=′-≃ (map-sty-ext-susp-compat (unbiased-type (tree-dim S) S)) refl≃l refl≃sty ⟩
  < susp-sty (unbiased-type (tree-dim S) S) >>=′ L >sty
    ≈⟨ >>=′-≃ (unbiased-type-susp-lem (tree-dim S) S) refl≃l refl≃sty ⟩
  < unbiased-type (suc (tree-dim S)) (susp-tree S) >>=′ L >sty ∎
  where
    open Reasoning sty-setoid

label-from-disc-term-prop : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → label-from-disc-term L ≃stm ap L (is-linear-max-path S)
label-from-disc-term-prop {S = Sing} L = refl≃stm
label-from-disc-term-prop {S = Join S Sing} L = label-from-disc-term-prop (label₁ L)

unbiased-type-linear : (d : ℕ) → (S : Tree n) → .⦃ _ : is-linear S ⦄ → .(d ≡ tree-dim S) → sty-to-type (unbiased-type d S) ≃ty lift-ty (sphere-type d)
unbiased-type-linear zero Sing p = refl≃ty
unbiased-type-linear (suc d) (Join S Sing) p = begin
  < sty-to-type (unbiased-type (suc d) (susp-tree S)) >ty
    ≈˘⟨ unbiased-type-susp-lem d S .get ⟩
  < sty-to-type (susp-sty (unbiased-type d S)) >ty
    ≈⟨ susp-sty-to-type (unbiased-type d S) ⟩
  < susp-ty (sty-to-type (unbiased-type d S)) >ty
    ≈⟨ susp-ty-≃ (unbiased-type-linear d S (cong pred p)) ⟩
  < susp-ty (lift-ty (sphere-type d)) >ty
    ≈⟨ susp-ty-lift (sphere-type d) ⟩
  < lift-ty (susp-ty (sphere-type d)) >ty
    ≈⟨ lift-ty-≃ (sphere-type-susp d) ⟩
  < lift-ty (sphere-type (suc d)) >ty ∎
  where
    open Reasoning ty-setoid

unbiased-term-linear : (d : ℕ) → (S : Tree n) → .⦃ _ : is-linear S ⦄ → .(d ≡ tree-dim S) → stm-to-term (unbiased-stm d S) ≃tm (0V {n = suc n})
unbiased-term-linear zero Sing p = refl≃tm
unbiased-term-linear (suc d) (Join S Sing) p = begin
  < susp-tm (stm-to-term (unbiased-stm d S)) [ idSub ]tm >tm
    ≈⟨ id-on-tm (susp-tm (stm-to-term (unbiased-stm d S))) ⟩
  < susp-tm (stm-to-term (unbiased-stm d S)) >tm
    ≈⟨ susp-tm-≃ (unbiased-term-linear d S (cong pred p)) ⟩
  < 0V >tm ∎
  where
    open Reasoning tm-setoid

identity-stm-to-term : (n : ℕ) → stm-to-term (identity-stm n) ≃tm identity n idSub
identity-stm-to-term n = begin
  < stm-to-term (identity-stm n) >tm
    ≈⟨ unbiased-comp′-compat (suc n) (n-disc n) .get ⟩
  < stm-to-term (unbiased-comp (suc n) (n-disc n)) >tm
    ≈⟨ Coh≃ lem1 lem3 lem4 ⟩
  < identity n idSub >tm ∎
  where
    lem1 : tree-to-ctx (n-disc n) ≃c Disc n
    lem1 = begin
      < tree-to-ctx (n-disc n) >c
        ≈⟨ linear-tree-compat (n-disc n) ⦃ n-disc-is-linear n ⦄ ⟩
      < Disc (tree-dim (n-disc n)) >c
        ≈⟨ disc-≡ (tree-dim-n-disc n) ⟩
      < Disc n >c ∎
      where
        open Reasoning ctx-setoid

    lem2 : (b : Bool) → stm-to-term
             (unbiased-stm n (tree-bd n (n-disc n)) >>=
              tree-inc-label n (n-disc n) b)
             ≃tm (0V {n = suc (double n)})
    lem2 b = begin
      < stm-to-term (unbiased-stm n (tree-bd n (n-disc n)) >>= tree-inc-label n (n-disc n) b) >tm
        ≈˘⟨ label-to-sub-stm (tree-inc-label n (n-disc n) b) (unbiased-stm n (tree-bd n (n-disc n))) ⟩
      < stm-to-term (unbiased-stm n (tree-bd n (n-disc n))) [ label-to-sub (tree-inc-label n (n-disc n) b) ]tm >tm
        ≈⟨ sub-action-≃-tm {s = stm-to-term (unbiased-stm n (tree-bd n (n-disc n)))} {t = stm-to-term (unbiased-stm n (n-disc n))} (unbiased-stm-≃ (refl {x = n}) (≃′-to-≃ (tree-bd-full n (n-disc n) (≤-reflexive (tree-dim-n-disc n)))) .get) (tree-inc-full n (n-disc n) b (≤-reflexive (tree-dim-n-disc n))) ⟩
      < stm-to-term (unbiased-stm n (n-disc n)) [ idSub ]tm >tm
        ≈⟨ id-on-tm (stm-to-term (unbiased-stm n (n-disc n))) ⟩
      < stm-to-term (unbiased-stm n (n-disc n)) >tm
        ≈⟨ unbiased-term-linear n (n-disc n) ⦃ n-disc-is-linear n ⦄ (sym (tree-dim-n-disc n)) ⟩
      < 0V >tm ∎
      where
        open Reasoning tm-setoid

    lem3 : sty-to-type (unbiased-type (suc n) (n-disc n)) ≃ty
             (Var 0F ─⟨ lift-ty (sphere-type n) ⟩⟶ Var 0F)
    lem3 = Arr≃ (lem2 false) (unbiased-type-linear n (n-disc n) ⦃ n-disc-is-linear n ⦄ (sym (tree-dim-n-disc n))) (lem2 true)

    lem4 : label-to-sub (id-label (n-disc n) ,, S⋆) ● idSub ≃s idSub
    lem4 = begin
      < label-to-sub (id-label (n-disc n) ,, S⋆) ● idSub >s
        ≈⟨ id-right-unit (label-to-sub (id-label (n-disc n) ,, S⋆)) ⟩
      < label-to-sub (id-label (n-disc n) ,, S⋆) >s
        ≈⟨ id-label-to-sub (n-disc n) ⟩
      < idSub >s ∎
      where
        open Reasoning sub-setoid
    open Reasoning tm-setoid

label-to-sub-from-disc-term : (L : Label-WT X (n-disc d)) → sub-from-disc-term (label-to-sub L) ≃tm stm-to-term (label-from-disc-term L ⦃ n-disc-is-linear d ⦄)
label-to-sub-from-disc-term {d = zero} L = refl≃tm
label-to-sub-from-disc-term {d = suc d} L = begin
  < sub-from-disc-term (label-to-sub L) >tm
    ≈⟨ sub-from-disc-term-unrestrict (label-to-sub (label₁ L)) ⟩
  < sub-from-disc-term (label-to-sub (label₁ L)) >tm
    ≈⟨ label-to-sub-from-disc-term (label₁ L) ⟩
  < stm-to-term (label-from-disc-term (label₁ L) ⦃ _ ⦄) >tm ∎
  where
    open Reasoning tm-setoid

label-to-sub-from-disc-type : (L : Label-WT X (n-disc d)) → sub-from-disc-type (label-to-sub L) ≃ty sty-to-type (label-from-disc-type L ⦃ n-disc-is-linear d ⦄)
label-to-sub-from-disc-type {d = zero} L = refl≃ty
label-to-sub-from-disc-type {d = suc d} L = begin
  < sub-from-disc-type (label-to-sub L) >ty
    ≈⟨ sub-from-disc-type-unrestrict (label-to-sub (label₁ L)) ⟩
  < sub-from-disc-type (label-to-sub (label₁ L)) >ty
    ≈⟨ label-to-sub-from-disc-type (label₁ L) ⟩
  < sty-to-type (label-from-disc-type (label₁ L) ⦃ _ ⦄) >ty ∎
  where
    open Reasoning ty-setoid

label-from-linear-tree-disc-type : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (a : STm X) → (As : STy X) → .(p : tree-dim S ≤ sty-dim As) → (Bs : STy X) → (Bs ≃sty label-from-linear-tree-type S As) → label-from-disc-type (label-from-linear-tree S a As p ,, Bs) ≃sty As
label-from-linear-tree-disc-type Sing a As p Bs q = q
label-from-linear-tree-disc-type (Join S Sing) a As p Bs q = label-from-linear-tree-disc-type S a As _ _ (trans≃sty (SArr≃ refl≃stm (trans≃sty q (label-from-linear-tree-type-prop S As)) refl≃stm) (sty-prop (label-from-linear-tree-type S As) ⦃ label-from-linear-tree-nz S As p ⦄))

label-from-linear-tree-disc-term : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (a : STm X) → (As : STy X) → .(p : tree-dim S ≤ sty-dim As) → (Bs : STy X) → label-from-disc-term (label-from-linear-tree S a As p ,, Bs) ≃stm a
label-from-linear-tree-disc-term Sing a As p Bs = refl≃stm
label-from-linear-tree-disc-term (Join S Sing) a As p Bs = label-from-linear-tree-disc-term S a As _ _

label-from-linear-tree-to-sub : (d : ℕ) → (a : STm X) → (As : STy X) → .(p : d ≡ sty-dim As) → label-to-sub (label-from-linear-tree (n-disc d) ⦃ n-disc-is-linear d ⦄ a As (≤-reflexive (trans (tree-dim-n-disc d) p)) ,, S⋆) ≃s sub-from-disc d (sty-to-type As) (trans (sty-to-type-dim As) (sym p)) (stm-to-term a)
label-from-linear-tree-to-sub d a As p = begin
  < label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) >s
    ≈⟨ prop-sub-from-disc (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)) ⟩
  < sub-from-disc d
    (sub-from-disc-type
     (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)))
    _
    (sub-from-disc-term
      (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)))
    >s
    ≈⟨ sub-from-disc-≃ d d lem1 (sub-from-disc-type-dim
                                  (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆))) (trans (sty-to-type-dim As) (sym p)) lem2 ⟩
  < sub-from-disc d (sty-to-type As) _ (stm-to-term a) >s ∎
  where
    lem1 : sub-from-disc-type (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆))
         ≃ty sty-to-type As
    lem1 = begin
      < sub-from-disc-type (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)) >ty
        ≈⟨ label-to-sub-from-disc-type (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) ⟩
      < sty-to-type (label-from-disc-type (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) ⦃ _ ⦄) >ty
        ≈⟨ label-from-linear-tree-disc-type (n-disc d) ⦃ _ ⦄ a As _ S⋆ (sym≃sty (label-from-linear-tree-type-0 (n-disc d) ⦃ _ ⦄ As (trans (tree-dim-n-disc d) p))) .get ⟩
      < sty-to-type As >ty ∎
      where
        open Reasoning ty-setoid

    lem2 : sub-from-disc-term (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As (≤-reflexive (trans (tree-dim-n-disc d) p)) ,, S⋆))
         ≃tm stm-to-term a
    lem2 = begin
      < sub-from-disc-term (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)) >tm
        ≈⟨ label-to-sub-from-disc-term (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) ⟩
      < stm-to-term (label-from-disc-term (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) ⦃ _ ⦄) >tm
        ≈⟨ label-from-linear-tree-disc-term (n-disc d) ⦃ _ ⦄ a As _ S⋆ .get ⟩
      < stm-to-term a >tm ∎
      where
        open Reasoning tm-setoid

    open Reasoning sub-setoid
