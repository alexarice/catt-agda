module Catt.Tree.Canonical.Properties where

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
open import Catt.Tree.Canonical
open import Data.Sum

canonical-type-dim : (d : ℕ) → (T : Tree n) → sty-dim (canonical-type d T) ≡ d
canonical-type-dim zero T = refl
canonical-type-dim (suc d) T = cong suc (canonical-type-dim d T)

canonical-type-≃ : d ≡ d′ → (S ≃ T) → canonical-type d S ≃sty canonical-type d′ T
canonical-type-≃ refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃sty

canonical-comp-≃ : d ≡ d′ → (S ≃ T) → canonical-comp d S ≃stm canonical-comp d′ T
canonical-comp-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

canonical-comp′-≃ : d ≡ d′ → (S ≃ T) → canonical-comp′ d S ≃stm canonical-comp′ d′ T
canonical-comp′-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

canonical-stm-≃ : d ≡ d′ → (S ≃ T) → canonical-stm d S ≃stm canonical-stm d′ T
canonical-stm-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

canonical-stm-≃-prop : (d : ℕ) → (p : S ≃′ T) → (canonical-stm d S >>= (SPath ∘ ppath-≃ p ,, S⋆)) ≃stm canonical-stm d T
canonical-stm-≃-prop {S = S} {T = T} d p = begin
  < canonical-stm d S >>= (SPath ∘ ppath-≃ p ,, S⋆) >stm
    ≈⟨ >>=-≃ (refl≃stm {a = canonical-stm d S}) (ppath-≃l p) (S⋆-≃ (sym≃ (≃′-to-≃ p))) ⟩
  < canonical-stm d S >>= id-label-wt S >stm
    ≈⟨ >>=-id (canonical-stm d S) ⟩
  < canonical-stm d S >stm
    ≈⟨ canonical-stm-≃ refl (≃′-to-≃ p) ⟩
  < canonical-stm d T >stm ∎
  where open Reasoning stm-setoid

canonical-stm-linear : (d : ℕ) → (T : Tree n) → .⦃ _ : is-linear T ⦄ → .(d ≡ tree-dim T) → canonical-stm d T ≃stm SPath (is-linear-max-path T)
canonical-stm-linear zero Sing p = [ refl≃tm ]
canonical-stm-linear (suc d) (Join T Sing) p = compute-≃ (SExt≃ (canonical-stm-linear d T (cong pred p)) refl≃)

canonical-stm-bd-non-linear : (d : ℕ) → (T : Tree n) → .(d > trunk-height T) → canonical-stm d (tree-bd d T) ≃stm canonical-comp′ d (tree-bd d T)
canonical-stm-bd-non-linear (suc d) Sing p = refl≃stm
canonical-stm-bd-non-linear (suc d) (Join T Sing) p = SExt≃ (canonical-stm-bd-non-linear d T (≤-pred p)) Sing≃
canonical-stm-bd-non-linear (suc d) (Join T (Join T₁ T₂)) p = refl≃stm

canonical-stm-full-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → (tree-dim T ≤ d) → (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm canonical-stm d T
canonical-stm-full-lem d T b p = begin
  < canonical-stm d (tree-bd d T) >>= tree-inc-label d T b >stm
    ≈⟨ >>=-≃ (refl≃stm {a = canonical-stm d (tree-bd d T)}) [ (λ P → SPath≃ (tree-inc-label-full d T b p .get P)) ] refl≃sty ⟩
  < canonical-stm d (tree-bd d T) >>= ((λ z → SPath (ppath-≃ (tree-bd-full d T p) z)) ,, S⋆) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = canonical-stm d (tree-bd d T)}) [ (λ P → SPath≃ (ppath-≃-≃p (tree-bd-full d T p) P)) ] [ (Star≃ (cong suc (≃-to-same-n (≃′-to-≃ (tree-bd-full d T p))))) ] ⟩
  < canonical-stm d (tree-bd d T) >>= id-label-wt (tree-bd d T) >stm
    ≈⟨ >>=-id (canonical-stm d (tree-bd d T)) ⟩
  < canonical-stm d (tree-bd d T) >stm
    ≈⟨ canonical-stm-≃ refl (≃′-to-≃ (tree-bd-full d T p)) ⟩
  < canonical-stm d T >stm ∎
  where
    open Reasoning stm-setoid

canonical-term-≃ : (d ≡ d′) → S ≃ T → canonical-term d S ≃tm canonical-term d′ T
canonical-term-≃ refl p with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = refl≃tm

canonical-type-prop : (d : ℕ) → (T : Tree n) → (d′ : ℕ) → (d ≤ d′) → (b : Bool) → canonical-type d T ≃sty canonical-type d (tree-bd d′ T) >>=′ tree-inc-label d′ T b
canonical-type-prop zero T d′ p b = refl≃sty
canonical-type-prop (suc d) T d′ p b = SArr≃ (lem false) (canonical-type-prop d T d′ (≤-trans (n≤1+n d) p) b) (lem true)
  where
    lem : (b′ : Bool) → (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b′)
      ≃stm (canonical-stm d (tree-bd d (tree-bd d′ T)) >>=
        tree-inc-label d (tree-bd d′ T) b′ >>= tree-inc-label d′ T b)
    lem b′ = begin
      < canonical-stm d (tree-bd d T) >>= tree-inc-label d T b′ >stm
        ≈˘⟨ >>=-≃′ (canonical-stm-≃ {d = d} refl (≃′-to-≃ (tree-bd-glob d d′ T p))) ((tree-bd-glob d d′ T p) ,, [ (λ P → SPath≃ (tree-inc-label-glob d d′ T b′ b p .get P)) ]) refl≃sty ⟩
      < canonical-stm d (tree-bd d (tree-bd d′ T))
        >>= tree-inc-label d (tree-bd d′ T) b′ ●lt tree-inc-label d′ T b >stm
        ≈˘⟨ >>=-assoc (canonical-stm d (tree-bd d (tree-bd d′ T))) _ _ ⟩
      < canonical-stm d (tree-bd d (tree-bd d′ T))
        >>= tree-inc-label d (tree-bd d′ T) b′
        >>= tree-inc-label d′ T b >stm ∎
      where
        open Reasoning stm-setoid

instance
  canonical-type-1-Full : {d : ℕ} → .⦃ NonZero d ⦄ → {T : Tree n} → 1-Full (canonical-type d T)
  canonical-type-1-Full {d = 1} .p₁ = refl≃stm
  canonical-type-1-Full {d = 1} .p₂ = refl≃stm
  canonical-type-1-Full {d = 2+ d} = inst

canonical-label-max : (S : Tree n)
                    → .⦃ _ : is-linear S ⦄
                    → (T : Tree m)
                    → (Z : Path S)
                    → .⦃ is-maximal Z ⦄
                    → canonical-label S T Z ≃stm canonical-comp′ (tree-dim S) T
canonical-label-max S T
  = stm-to-label-max S (canonical-comp′ (tree-dim S) T) (canonical-type (tree-dim S) T)

canonical-label-fst : (S : Tree n)
                    → .⦃ _ : is-linear S ⦄
                    → .⦃ NonZero (tree-dim S) ⦄
                    → (T : Tree m)
                    → canonical-label S T PHere ≃stm SHere {S = T}
canonical-label-fst S T = stm-to-label-1-Full-src S (canonical-comp′ (tree-dim S) T) (canonical-type (tree-dim S) T)

canonical-label-last : (S : Tree n)
                     → .⦃ _ : is-linear S ⦄
                     → .⦃ NonZero (tree-dim S) ⦄
                     → (T : Tree m)
                     → canonical-label S T (last-path S) ≃stm SPath (last-path T)
canonical-label-last S T = stm-to-label-1-Full-tgt S (canonical-comp′ (tree-dim S) T) (canonical-type (tree-dim S) T)

extend-disc-label-bd-< : (L : Label X S)
                       → .⦃ _ : is-linear S ⦄
                       → (t : STm X)
                       → (a : STm X)
                       → (d : ℕ)
                       → (d < tree-dim S)
                       → (b : Bool)
                       → extend-disc-label L t a (disc-inc d (susp S) b) ≃stm L (disc-inc d S b)
extend-disc-label-bd-< {S = susp S} L t a zero q false = refl≃stm
extend-disc-label-bd-< {S = susp S} L t a zero q true = refl≃stm
extend-disc-label-bd-< {S = susp S} L t a (suc d) q b = extend-disc-label-bd-< (L ∘ PExt) t a d (≤-pred q) b

extend-disc-label-bd-≡ : (L : Label X S)
                       → .⦃ _ : is-linear S ⦄
                       → (t : STm X)
                       → (a : STm X)
                       → (d : ℕ)
                       → (d ≡ tree-dim S)
                       → (b : Bool)
                       → extend-disc-label L t a (disc-inc d (susp S) b)
                         ≃stm
                         (if b then t else L (is-linear-max-path S))
extend-disc-label-bd-≡ {S = Sing} L t a zero p false = refl≃stm
extend-disc-label-bd-≡ {S = Sing} L t a zero p true = refl≃stm
extend-disc-label-bd-≡ {S = susp S} L t a (suc d) p b = extend-disc-label-bd-≡ (L ∘ PExt) t a d (cong pred p) b

module _ where
  open Reasoning stm-setoid
  canonical-label-bd-<-lem : (S : Tree n)
                           → .⦃ _ : is-linear S ⦄
                           → (T : Tree m)
                           → (d : ℕ)
                           → (b : Bool)
                           → (d < tree-dim S)
                           → (a : STm (someTree T))
                           → stm-to-label S a (canonical-type (tree-dim S) T) (disc-inc d S b)
                             ≃stm
                             canonical-stm d (tree-bd d T) >>= tree-inc-label d T b
  canonical-label-bd-<-lem (susp S) T d b q a with <-cmp d (tree-dim S)
  ... | tri< x _ _ = begin
    < extend-disc-label
      (stm-to-label S
       (canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
        (tree-inc-label (tree-dim S) T false))
       (canonical-type (tree-dim S) T))
      (canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
       (tree-inc-label (tree-dim S) T true))
      a
      (disc-inc d (susp S) b) >stm
      ≈⟨ extend-disc-label-bd-< _ _ a d x b ⟩
    < stm-to-label S
      (canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
        tree-inc-label (tree-dim S) T false)
      (canonical-type (tree-dim S) T) (disc-inc d S b) >stm
      ≈⟨ canonical-label-bd-<-lem S T d b x _ ⟩
    < canonical-stm d (tree-bd d T) >>= tree-inc-label d T b >stm ∎
  ... | tri> ¬a ¬b c = ⊥-elim (1+n≰n (≤-trans q c))
  ... | tri≈ _ refl _ with b
  ... | false = begin
    < extend-disc-label
      (stm-to-label S
       (canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
        (tree-inc-label (tree-dim S) T false))
       (canonical-type (tree-dim S) T))
      (canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
       (tree-inc-label (tree-dim S) T true))
      a
      (disc-inc d (susp S) false) >stm
      ≈⟨ extend-disc-label-bd-≡ _ _ a d refl false ⟩
    < stm-to-label S (canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>= tree-inc-label (tree-dim S) T false)  (canonical-type (tree-dim S) T) (is-linear-max-path S)
     >stm
      ≈⟨ stm-to-label-max S _ _ (is-linear-max-path S) ⟩
    < canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>= tree-inc-label (tree-dim S) T false >stm ∎
  ... | true = extend-disc-label-bd-≡ _ _ a d refl true


canonical-label-bd-< : (S : Tree n)
                     → .⦃ _ : is-linear S ⦄
                     → (T : Tree m)
                     → (d : ℕ)
                     → (b : Bool)
                     → (d < tree-dim S)
                     → (Z : Path (tree-bd d S))
                     → .⦃ is-maximal Z ⦄
                     → canonical-label S T (tree-inc-label′ d S b Z)
                       ≃stm
                       canonical-stm d (tree-bd d T) >>= tree-inc-label d T b
canonical-label-bd-< S T d b q Z = begin
  < canonical-label S T (tree-inc-label′ d S b Z) >stm
    ≈˘⟨ ap-≃ (refl≃l {L = canonical-label S T}) (ap′-≃ (tree-inc-label′ d S b) (max-path-lin-tree (tree-bd d S) ⦃ _ ⦄ Z refl≃)) ⟩
  < canonical-label S T (disc-inc d S b) >stm
    ≈⟨ canonical-label-bd-<-lem S T d b q (canonical-comp′ (tree-dim S) T) ⟩
  < canonical-stm d (tree-bd d T) >>= tree-inc-label d T b >stm ∎
  where
    open Reasoning stm-setoid

module _ where
  open Reasoning stm-setoid
  canonical-label-bd->-trunk-height : (S : Tree n)
    → .⦃ _ : is-linear S ⦄
    → (T : Tree m)
    → (d : ℕ)
    → (b : Bool)
    → (d ≤ tree-dim S)
    → (d > trunk-height T)
    → (tree-dim S ≥ tree-dim T)
    → (Z : Path (tree-bd d S))
    → .⦃ is-maximal Z ⦄
    → canonical-label S T (tree-inc-label′ d S b Z)
      ≃stm
      canonical-comp′ d (tree-bd d T) >>= tree-inc-label d T b
  canonical-label-bd->-trunk-height S T d b p q r Z with <-cmp d (tree-dim S)
  ... | tri< x _ _ = begin
    < canonical-label S T (tree-inc-label′ d S b Z) >stm
      ≈⟨ canonical-label-bd-< S T d b x Z ⟩
    < canonical-stm d (tree-bd d T) >>= tree-inc-label d T b >stm
      ≈⟨ >>=-≃ (canonical-stm-bd-non-linear d T q) refl≃l refl≃sty ⟩
    < canonical-comp′ d (tree-bd d T) >>= tree-inc-label d T b >stm ∎
  ... | tri≈ _ x _ = begin
    < canonical-label S T (tree-inc-label′ d S b Z) >stm
      ≈⟨ canonical-label-max S T _ ⦃ tree-inc-full-preserve-max d S b (≤-reflexive (sym x)) Z ⦄ ⟩
    < canonical-comp′ (tree-dim S) T >stm
      ≈˘⟨ canonical-comp′-≃ x (≃′-to-≃ (tree-bd-full d T (≤-trans r (≤-reflexive (sym x))))) ⟩
    < canonical-comp′ d (tree-bd d T) >stm
      ≈˘⟨ >>=-id (canonical-comp′ d (tree-bd d T)) ⟩
    < canonical-comp′ d (tree-bd d T) >>= id-label-wt (tree-bd d T) >stm
      ≈˘⟨ >>=-≃ (refl≃stm {a = canonical-comp′ d (tree-bd d T)}) (tree-inc-label-full-is-id d T b (≤-trans r (≤-reflexive (sym x)))) (S⋆-≃ (sym≃ (≃′-to-≃ (tree-bd-full d T (≤-trans r (≤-reflexive (sym x))))))) ⟩
    < canonical-comp′ d (tree-bd d T) >>= tree-inc-label d T b >stm ∎
  ... | tri> ¬a ¬b c = ⊥-elim (1+n≰n (≤-trans c p))

-- lfltu-≤-trunk-height-lem : {x y : ℕ}
--                           → (p : x ≡ y)
--                           → (T : Tree n)
--                           → (b : Bool)
--                           → .(xp : x ≤ trunk-height T)
--         → SPath (tree-inc-label′ x T b (is-linear-max-path (tree-bd x T) ⦃ bd-trunk-height x T xp ⦄))
--           ≃stm SPath (tree-inc-label′ y T b (is-linear-max-path (tree-bd y T) ⦃ bd-trunk-height y T (≤-trans (≤-reflexive (sym p)) xp) ⦄))
-- lfltu-≤-trunk-height-lem refl T b xp = refl≃stm

-- module _ where
--   open Reasoning stm-setoid

--   lfltu-≤-trunk-height : (S : Tree n) → .⦃ _ : is-linear S ⦄
--                         → (T : Tree m)
--                         → (d₁ : ℕ) → (d₂ : ℕ) → .(p : d₁ + d₂ ≤ trunk-height T)
--                         → .(d₂ < tree-dim S)
--                         → .(d₁ + tree-dim S ≥ tree-dim T)
--                         → (b : Bool)
--                         → (Z : Path (tree-bd d₂ S)) → .⦃ is-maximal Z ⦄
--                         → label-from-linear-tree-canonical S T d₁ (tree-inc-label′ d₂ S b Z)
--                         ≃stm SPath (tree-inc-label′ (d₁ + d₂) T b (is-linear-max-path (tree-bd (d₁ + d₂) T) ⦃ bd-trunk-height (d₁ + d₂) T p ⦄))
--   lfltu-≤-trunk-height Sing T d₁ d₂ p () r
--   lfltu-≤-trunk-height (Join S Sing) T d₁ zero p q r false PHere = let
--     .p′ : d₁ ≤ trunk-height T
--     p′ = ≤-trans (≤-reflexive (sym (+-identityʳ d₁))) p
--     instance _ = bd-trunk-height d₁ T p′
--     instance _ = bd-trunk-height (d₁ + zero) T p
--     in begin
--     < canonical-stm d₁ (tree-bd d₁ T) >>= tree-inc-label d₁ T false >stm
--       ≈⟨ >>=-≃ (canonical-stm-linear d₁ (tree-bd d₁ T) (sym (tree-dim-bd′ d₁ T (≤-trans p′ (trunk-height-dim T))))) (refl≃l {L = ap (tree-inc-label d₁ T false)}) refl≃sty ⟩
--     < SPath (tree-inc-label′ d₁ T false (is-linear-max-path (tree-bd d₁ T))) >stm
--       ≈˘⟨ lfltu-≤-trunk-height-lem (+-identityʳ d₁) T false p ⟩
--     < SPath (tree-inc-label′ (d₁ + zero) T false (is-linear-max-path (tree-bd (d₁ + zero) T))) >stm ∎
--   lfltu-≤-trunk-height (Join S Sing) T d₁ zero p q r true PHere = let
--     .p′ : d₁ ≤ trunk-height T
--     p′ = ≤-trans (≤-reflexive (sym (+-identityʳ d₁))) p
--     instance _ = bd-trunk-height d₁ T p′
--     instance _ = bd-trunk-height (d₁ + zero) T p
--     in begin
--     < canonical-stm d₁ (tree-bd d₁ T) >>= tree-inc-label d₁ T true >stm
--       ≈⟨ >>=-≃ (canonical-stm-linear d₁ (tree-bd d₁ T) (sym (tree-dim-bd′ d₁ T (≤-trans p′ (trunk-height-dim T))))) (refl≃l {L = ap (tree-inc-label d₁ T true)}) refl≃sty ⟩
--     < SPath (tree-inc-label′ d₁ T true (is-linear-max-path (tree-bd d₁ T))) >stm
--       ≈˘⟨ lfltu-≤-trunk-height-lem (+-identityʳ d₁) T true p ⟩
--     < SPath (tree-inc-label′ (d₁ + zero) T true (is-linear-max-path (tree-bd (d₁ + zero) T))) >stm ∎
--   lfltu-≤-trunk-height (Join S Sing) T d₁ (suc d₂) p q r b (PExt Z) = let
--     .p′ : suc (d₁ + d₂) ≤ trunk-height T
--     p′ = ≤-trans (≤-reflexive (sym (+-suc d₁ d₂))) p
--     instance _ = bd-trunk-height (suc d₁ + d₂) T p′
--     instance _ = bd-trunk-height (d₁ + suc d₂) T p
--     in begin
--     < label-from-linear-tree-canonical S T (suc d₁)
--         (tree-inc-label′ d₂ S b Z) >stm
--       ≈⟨ lfltu-≤-trunk-height S T (suc d₁) d₂ p′ (≤-pred q) (≤-trans r (≤-reflexive (+-suc d₁ (tree-dim S)))) b Z ⟩
--     < SPath (tree-inc-label′ (suc d₁ + d₂) T b (is-linear-max-path (tree-bd (suc d₁ + d₂) T))) >stm
--       ≈˘⟨ lfltu-≤-trunk-height-lem (+-suc d₁ d₂) T b p ⟩
--     < SPath (tree-inc-label′ (d₁ + suc d₂) T b (is-linear-max-path (tree-bd (d₁ + suc d₂) T))) >stm ∎
--   lfltu-≤-trunk-height (Join S Sing) T d₁ (suc d₂) p q r b (PShift PHere) = ⊥-elim it

--   lfltu->-trunk-height : (S : Tree n) → .⦃ _ : is-linear S ⦄
--                         → (T : Tree m)
--                         → (d₁ : ℕ) → (d₂ : ℕ)
--                         → .(d₁ + tree-dim S ≥ tree-dim T)
--                         → .(d₁ + d₂ > trunk-height T)
--                         → .(d₂ ≤ tree-dim S)
--                         → (b : Bool)
--                         → (Z : Path (tree-bd d₂ S)) → .⦃ _ : is-maximal Z ⦄
--                         → label-from-linear-tree-canonical S T d₁ (tree-inc-label′ d₂ S b Z) ≃stm (canonical-comp′ (d₂ + d₁) (tree-bd (d₂ + d₁) T) >>= tree-inc-label (d₂ + d₁) T b)
--   lfltu->-trunk-height Sing T d₁ zero p q r b Z = let
--     .p′ : tree-dim T ≤ d₁
--     p′ = ≤-trans p (≤-reflexive (+-identityʳ d₁))
--     in begin
--     < canonical-comp′ d₁ T >stm
--       ≈˘⟨ canonical-comp′-≃ refl (≃′-to-≃ (tree-bd-full d₁ T p′)) ⟩
--     < canonical-comp′ d₁ (tree-bd d₁ T) >stm
--       ≈˘⟨ >>=-id (canonical-comp′ d₁ (tree-bd d₁ T)) ⟩
--     < canonical-comp′ d₁ (tree-bd d₁ T) >>= id-label-wt (tree-bd d₁ T) >stm
--       ≈⟨ >>=-≃ (refl≃stm {a = canonical-comp′ d₁ (tree-bd d₁ T)}) [ (λ P → SPath≃ (ppath-≃-≃p (tree-bd-full d₁ T p′) P )) ] [ (Star≃ (cong suc (≃-to-same-n (≃′-to-≃ (tree-bd-full d₁ T p′))))) ]
--       ⟩
--     < canonical-comp′ d₁ (tree-bd d₁ T)
--       >>= ((λ z → SPath (ppath-≃ (tree-bd-full d₁ T p′) z)) ,, S⋆) >stm
--       ≈˘⟨ >>=-≃ (refl≃stm {a = canonical-comp′ d₁ (tree-bd d₁ T)}) [ (λ P → SPath≃ (tree-inc-label-full d₁ T b p′ .get P)) ] refl≃sty ⟩
--     < canonical-comp′ d₁ (tree-bd d₁ T) >>= tree-inc-label d₁ T b >stm ∎
--   lfltu->-trunk-height (Join S Sing) T d₁ (suc d₂) p q r b (PExt Z) = begin
--     < label-from-linear-tree-canonical S T (suc d₁)
--          (tree-inc-label′ d₂ S b Z) >stm
--       ≈⟨ lfltu->-trunk-height S T (suc d₁) d₂ (≤-trans p (≤-reflexive (+-suc d₁ (tree-dim S)))) (<-≤-trans q (≤-reflexive (+-suc d₁ d₂))) (≤-pred r) b Z ⟩
--     < canonical-comp′ (d₂ + suc d₁) (tree-bd (d₂ + suc d₁) T)
--       >>= tree-inc-label (d₂ + suc d₁) T b >stm
--       ≈⟨ reflexive≃stm (cong (λ - → canonical-comp′ - (tree-bd - T) >>= tree-inc-label - T b) (+-suc d₂ d₁)) ⟩
--     < canonical-comp′ (suc d₂ + d₁) (tree-bd (suc d₂ + d₁) T)
--       >>= tree-inc-label (suc d₂ + d₁) T b >stm ∎
--   lfltu->-trunk-height (Join S Sing) T d₁ (suc d₂) p q r b (PShift PHere) = ⊥-elim it
--   lfltu->-trunk-height (Join S Sing) T (suc d₁) zero p q r false PHere
--     = >>=-≃ (canonical-stm-bd-non-linear (suc d₁) T (<-≤-trans q (s≤s (≤-reflexive (+-identityʳ d₁))))) refl≃l refl≃sty
--   lfltu->-trunk-height (Join S Sing) T (suc d₁) zero p q r true PHere
--     = >>=-≃ (canonical-stm-bd-non-linear (suc d₁) T (<-≤-trans q (s≤s (≤-reflexive (+-identityʳ d₁))))) refl≃l refl≃sty

canonical-type-susp-lem : (d : ℕ) → (T : Tree n) → susp-sty (canonical-type d T) ≃sty canonical-type (suc d) (susp-tree T)
canonical-comp-susp-lem : (d : ℕ) → (T : Tree n) → SExt {T = Sing} (canonical-comp d T) ≃stm canonical-comp (suc d) (susp-tree T)

canonical-type-susp-lem zero T = SArr≃ [ refl≃tm ] refl≃sty [ refl≃tm ]
canonical-type-susp-lem (suc d) T = SArr≃ (lem false) (canonical-type-susp-lem d T) (lem true)
  where
    open Reasoning stm-setoid
    lem : (b : Bool) → susp-stm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm (canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) b))
    lem b = begin
      < SExt (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm
        ≈˘⟨ >>=-ext (canonical-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < canonical-stm d (tree-bd d T) >>= map-ext (tree-inc-label d T b) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = canonical-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
      < canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) b) >stm ∎

canonical-comp-susp-lem d T = begin
  < SExt (canonical-comp d T) >stm
    ≈˘⟨ SCoh-ext T (canonical-type d T) (id-label-wt T) ⟩
  < SCoh T (canonical-type d T) (map-ext (id-label-wt T)) >stm
    ≈⟨ SCoh-unrestrict T (canonical-type d T) (map-ext (id-label-wt T)) ⟩
  < SCoh (susp-tree T) (susp-sty (canonical-type d T)) (susp-label-full (id-label T) ,, S⋆) >stm
    ≈⟨ SCoh≃ (susp-tree T) (canonical-type-susp-lem d T) (id-label-susp-full T) refl≃sty ⟩
  < canonical-comp (suc d) (susp-tree T) >stm ∎
  where
    open Reasoning stm-setoid

canonical-label-susp-lem : (S : Tree m)
                         → .⦃ _ : is-linear S ⦄
                         → (T : Tree n)
                         → canonical-label (susp S) (susp T) ≃l susp-label-full (canonical-label S T)
canonical-label-susp-lem S ⦃ lin ⦄ T = begin
  < canonical-label (susp S) (susp T) >l
    ≈⟨ stm-to-label-≃ (susp S) refl≃stm
                      (sym≃sty (canonical-type-susp-lem (tree-dim S) T)) ⦃ inst ⦄ ⟩
  < stm-to-label (susp S)
                 (susp-stm (canonical-comp′ (tree-dim S) T))
                 (susp-sty (canonical-type (tree-dim S) T))
                 ⦃ trans≃n inst (≡-to-≃n (sym (susp-sty-dim (canonical-type (tree-dim S) T)))) ⦄
   >l
    ≈⟨ stm-to-label-susp S (canonical-comp′ (tree-dim S) T) (canonical-type (tree-dim S) T) ⟩
  < susp-label-full (canonical-label S T) >l ∎
  where
    open Reasoning (label-setoid (susp S))

canonical-comp′-compat : (d : ℕ) → (T : Tree n) → canonical-comp′ d T ≃stm canonical-comp d T
canonical-comp′-compat zero T = refl≃stm
canonical-comp′-compat (suc d) Sing = refl≃stm
canonical-comp′-compat (suc d) (Join T Sing) = begin
  < SExt (canonical-comp′ d T) >stm
    ≈⟨ SExt≃ (canonical-comp′-compat d T) Sing≃ ⟩
  < SExt (canonical-comp d T) >stm
    ≈⟨ canonical-comp-susp-lem d T ⟩
  < canonical-comp (suc d) (Join T Sing) >stm ∎
  where
    open Reasoning stm-setoid
canonical-comp′-compat (suc d) T@(Join _ (Join _ _)) = refl≃stm

disc-sty-is-canonical : (S : Tree n) → .⦃ _ : is-linear S ⦄ → disc-sty S ≃sty canonical-type (tree-dim S) S
disc-sty-is-canonical Sing = refl≃sty
disc-sty-is-canonical (susp S) = begin
  < disc-sty (susp S) >sty
    ≈⟨ map-sty-ext-susp-compat (disc-sty S) ⟩
  < susp-sty (disc-sty S) >sty
    ≈⟨ susp-sty-≃ (disc-sty-is-canonical S) ⟩
  < susp-sty (canonical-type (tree-dim S) S) >sty
    ≈⟨ canonical-type-susp-lem (tree-dim S) S ⟩
  < canonical-type (tree-dim (susp S)) (susp S) >sty ∎
  where
    open Reasoning sty-setoid

disc-stm-is-canonical : (S : Tree n) → .⦃ _ : is-linear S ⦄ → disc-stm S ≃stm canonical-comp (tree-dim S) S
disc-stm-is-canonical S = SCoh≃ S (disc-sty-is-canonical S) refl≃l refl≃sty

identity-stm-is-canonical : (S : Tree n) → .⦃ _ : is-linear S ⦄ → identity-stm S ≃stm canonical-comp (suc (tree-dim S)) S
identity-stm-is-canonical S = SCoh≃ S (SArr≃ (lem false) (disc-sty-is-canonical S) (lem true)) refl≃l refl≃sty
  where
    open Reasoning stm-setoid
    lem : (b : Bool) → SPath (is-linear-max-path S)
                       ≃stm
                       canonical-stm (tree-dim S) (tree-bd (tree-dim S) S) >>= tree-inc-label (tree-dim S) S b
    lem b = begin
      < SPath (is-linear-max-path S) >stm
        ≈˘⟨ canonical-stm-linear (tree-dim S) S refl ⟩
      < canonical-stm (tree-dim S) S >stm
        ≈˘⟨ canonical-stm-full-lem (tree-dim S) S b ≤-refl ⟩
      < canonical-stm (tree-dim S) (tree-bd (tree-dim S) S) >>= tree-inc-label (tree-dim S) S b >stm ∎


-- lfltu-susp : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → (label-from-linear-tree-canonical S (susp-tree T) (suc d)) ≃l (SExt {T = Sing} ∘ label-from-linear-tree-canonical S T d)
-- lfltu-susp Sing T d .get PHere = refl≃stm
-- lfltu-susp (Join S Sing) T d .get PHere = begin
--   < canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) false) >stm
--     ≈⟨ >>=-≃ (refl≃stm {a = canonical-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
--   < canonical-stm d (tree-bd d T) >>= map-ext (tree-inc-label d T false) >stm
--     ≈⟨ >>=-ext (canonical-stm d (tree-bd d T)) (tree-inc-label d T false) ⟩
--   < SExt (canonical-stm d (tree-bd d T) >>= (tree-inc-label d T false)) >stm ∎
--   where
--     open Reasoning stm-setoid
-- lfltu-susp (Join S Sing) T d .get (PExt Z) = lfltu-susp S T (suc d) .get Z
-- lfltu-susp (Join S Sing) T d .get (PShift PHere) = begin
--   < canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (susp-tree T) true) >stm
--     ≈⟨ >>=-≃ (refl≃stm {a = canonical-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
--   < canonical-stm d (tree-bd d T) >>= map-ext (tree-inc-label d T true) >stm
--     ≈⟨ >>=-ext (canonical-stm d (tree-bd d T)) (tree-inc-label d T true) ⟩
--   < SExt (canonical-stm d (tree-bd d T) >>= (tree-inc-label d T true)) >stm ∎
--   where
--     open Reasoning stm-setoid

-- label-from-linear-tree-canonical-type-lem : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (T : Tree m) → (d : ℕ) → label-from-linear-tree-type S (canonical-type (tree-dim S + d) T) ≃sty canonical-type d T
-- label-from-linear-tree-canonical-type-lem Sing T d = refl≃sty
-- label-from-linear-tree-canonical-type-lem (Join S Sing) T d = label-from-linear-tree-canonical-type-lem S T d

-- label-from-linear-tree-canonical-lem
--   : (S : Tree n)
--   → .⦃ _ : is-linear S ⦄
--   → (T : Tree m)
--   → (d : ℕ)
--   → label-from-linear-tree S (canonical-comp′ (tree-dim S + d) T)
--                              (canonical-type (tree-dim S + d) T)
--                              (≤-trans (m≤m+n (tree-dim S) d) (≤-reflexive (sym (canonical-type-dim (tree-dim S + d) T))))
--   ≃l label-from-linear-tree-canonical S T d
-- label-from-linear-tree-canonical-lem Sing T d .get P = refl≃stm
-- label-from-linear-tree-canonical-lem (Join S Sing) T d .get PHere = begin
--   < sty-src (label-from-linear-tree-type S (canonical-type (suc (tree-dim S) + d) T)) ⦃ _ ⦄ >stm
--     ≈⟨ sty-src-≃ (label-from-linear-tree-type-≃ S (canonical-type-≃ (sym (+-suc (tree-dim S) d)) refl≃)) ⦃ _ ⦄ ⟩
--   < sty-src (label-from-linear-tree-type S (canonical-type (tree-dim S + suc d) T)) ⦃ _ ⦄ >stm
--     ≈⟨ sty-src-≃ (label-from-linear-tree-canonical-type-lem S T (suc d)) ⦃ _ ⦄ ⟩
--   < sty-src (canonical-type (suc d) T) >stm
--     ≡⟨⟩
--   < canonical-stm d (tree-bd d T) >>= tree-inc-label d T false >stm ∎
--   where
--     open Reasoning stm-setoid
-- label-from-linear-tree-canonical-lem (Join S Sing) T d .get (PExt P) = begin
--   < label-from-linear-tree S
--                            (canonical-comp′ (suc (tree-dim S + d)) T)
--                            (canonical-type (suc (tree-dim S + d)) T)
--                            _ P >stm
--     ≈⟨ label-from-linear-tree-≃ S (canonical-comp′-≃ (sym (+-suc (tree-dim S) d)) refl≃) (canonical-type-≃ (sym (+-suc (tree-dim S) d)) refl≃) _ .get P ⟩
--   < label-from-linear-tree S
--                            (canonical-comp′ (tree-dim S + suc d) T)
--                            (canonical-type (tree-dim S + suc d) T)
--                            _ P >stm
--     ≈⟨ label-from-linear-tree-canonical-lem S T (suc d) .get P ⟩
--   < label-from-linear-tree-canonical S T (suc d) P >stm ∎
--   where
--     open Reasoning stm-setoid
-- label-from-linear-tree-canonical-lem (Join S Sing) T d .get (PShift PHere) = begin
--   < sty-tgt (label-from-linear-tree-type S (canonical-type (suc (tree-dim S) + d) T)) ⦃ _ ⦄ >stm
--     ≈⟨ sty-tgt-≃ (label-from-linear-tree-type-≃ S (canonical-type-≃ (sym (+-suc (tree-dim S) d)) refl≃)) ⦃ _ ⦄ ⟩
--   < sty-tgt (label-from-linear-tree-type S (canonical-type (tree-dim S + suc d) T)) ⦃ _ ⦄ >stm
--     ≈⟨ sty-tgt-≃ (label-from-linear-tree-canonical-type-lem S T (suc d)) ⦃ _ ⦄ ⟩
--   < sty-tgt (canonical-type (suc d) T) >stm
--     ≡⟨⟩
--   < canonical-stm d (tree-bd d T) >>= tree-inc-label d T true >stm ∎
--   where
--     open Reasoning stm-setoid

-- label-from-linear-tree-canonical-lem-0 :
--     (S : Tree n)
--   → .⦃ _ : is-linear S ⦄
--   → (T : Tree m)
--   → (d : ℕ)
--   → (p : tree-dim S ≡ d)
--   → label-from-linear-tree S (canonical-comp′ d T)
--                              (canonical-type d T)
--                              (≤-reflexive (trans p (sym (canonical-type-dim d T))))
--   ≃l label-from-linear-tree-canonical S T 0
-- label-from-linear-tree-canonical-lem-0 S T d p = begin
--   < label-from-linear-tree S (canonical-comp′ d T)
--                              (canonical-type d T) _ >l
--     ≈˘⟨ label-from-linear-tree-≃ S (canonical-comp′-≃ (trans (+-identityʳ (tree-dim S)) p) refl≃) (canonical-type-≃ (trans (+-identityʳ (tree-dim S)) p) refl≃) _ ⟩
--   < label-from-linear-tree S (canonical-comp′ (tree-dim S + 0) T)
--                              (canonical-type (tree-dim S + 0) T) _ >l
--     ≈⟨ label-from-linear-tree-canonical-lem S T 0 ⟩
--   < label-from-linear-tree-canonical S T 0 >l ∎
--   where
--     open Reasoning (label-setoid S)

-- label-from-linear-tree-type-prop : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (As : STy X) → label-from-linear-tree-type S (sty-base As) ≃sty sty-base (label-from-linear-tree-type S As)
-- label-from-linear-tree-type-prop Sing As = refl≃sty
-- label-from-linear-tree-type-prop (Join S Sing) As = label-from-linear-tree-type-prop S (sty-base As)

truncate-canonical-sty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → truncate-sty 1 (canonical-type d T) ≃sty SArr SHere S⋆ (SPath (last-path T))
truncate-canonical-sty (suc zero) T = refl≃sty
truncate-canonical-sty (suc (suc d)) T = begin
  < truncate-sty 1 (canonical-type (suc (suc d)) T) >sty
    ≈⟨ truncate-sty-≤ 1 (canonical-type (2 + d) T) (s≤s (s≤s z≤n)) ⟩
  < truncate-sty 1 (canonical-type (1 + d) T) >sty
    ≈⟨ truncate-canonical-sty (suc d) T ⟩
  < SArr SHere S⋆ (SPath (last-path T)) >sty ∎
  where
    open Reasoning sty-setoid

-- label-from-linear-tree-type-susp : (S : Tree n)
--                                  → .⦃ _ : is-linear S ⦄
--                                  → (As : STy X)
--                                  → .(sty-dim As ≥ tree-dim S)
--                                  → label-from-linear-tree-type S (susp-sty As) ≃sty susp-sty (label-from-linear-tree-type S As)
-- label-from-linear-tree-type-susp Sing As p = refl≃sty
-- label-from-linear-tree-type-susp (Join S Sing) As@(SArr _ _ _) p = label-from-linear-tree-type-susp S (sty-base As) (≤-pred p)

-- label-from-linear-tree-susp : (S : Tree n)
--                             → .⦃ _ : is-linear S ⦄
--                             → (a : STm X)
--                             → (As : STy X)
--                             → .(p : tree-dim S ≤ sty-dim As)
--                             → label-from-linear-tree S (susp-stm a) (susp-sty As) (≤-trans p (≤-trans (n≤1+n (sty-dim As)) (≤-reflexive (sym (susp-sty-dim As))))) ≃l (susp-stm ∘ label-from-linear-tree S a As p)
-- label-from-linear-tree-susp Sing a As p .get PHere = refl≃stm
-- label-from-linear-tree-susp (Join S Sing) a As p = begin
--   < unrestrict-label
--       (label-from-linear-tree S (susp-stm a) (susp-sty As) _ ,,
--        label-from-linear-tree-type S (susp-sty As)) ⦃ _ ⦄ >l
--     ≈⟨ unrestrict-label-≃ _ _ ⦃ _ ⦄ (label-from-linear-tree-susp S a As _) (label-from-linear-tree-type-susp S As (≤-trans (n≤1+n (tree-dim S)) p)) ⟩
--   < unrestrict-label (susp-label (label-from-linear-tree S a As _ ,, label-from-linear-tree-type S As)) ⦃ _ ⦄ >l
--     ≈˘⟨ susp-unrestrict-label (label-from-linear-tree S a As _ ,, label-from-linear-tree-type S As) ⦃ label-from-linear-tree-nz S As p ⦄ ⟩
--   < (susp-stm ∘
--        unrestrict-label
--        (label-from-linear-tree S a As _ ,,
--         label-from-linear-tree-type S As) ⦃ _ ⦄) >l ∎
--   where
--     open Reasoning (label-setoid _)

-- label-from-linear-tree-type-0 : (S : Tree n)
--                             → .⦃ _ : is-linear S ⦄
--                             → (As : STy X)
--                             → .(p : tree-dim S ≡ sty-dim As)
--                             → label-from-linear-tree-type S As ≃sty (S⋆ {X = X})
-- label-from-linear-tree-type-0 Sing S⋆ p = refl≃sty
-- label-from-linear-tree-type-0 (Join S Sing) (SArr s As t) p = label-from-linear-tree-type-0 S As (cong pred p)

-- label-from-linear-tree-susp-full : (S : Tree n)
--                             → .⦃ _ : is-linear S ⦄
--                             → (a : STm X)
--                             → (As : STy X)
--                             → .(p : tree-dim S ≡ sty-dim As)
--                             → label-from-linear-tree (susp-tree S) (susp-stm a) (susp-sty As) (≤-reflexive (trans (cong suc p) (sym (susp-sty-dim As)))) ≃l susp-label-full (label-from-linear-tree S a As (≤-reflexive p))
-- label-from-linear-tree-susp-full S a As p = unrestrict-label-≃ _ _ ⦃ _ ⦄ (label-from-linear-tree-susp S a As (≤-reflexive p)) (begin
--   < label-from-linear-tree-type S (susp-sty As) >sty
--     ≈⟨ label-from-linear-tree-type-susp S As (≤-reflexive p) ⟩
--   < susp-sty (label-from-linear-tree-type S As) >sty
--     ≈⟨ susp-sty-≃ (label-from-linear-tree-type-0 S As p) ⟩
--   < SArr stm-fst S⋆ stm-snd >sty ∎)
--   where
--     open Reasoning sty-setoid

-- label-from-disc-type-dim-lem : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → tree-dim S + (sty-dim (lty L)) ≡ sty-dim (label-from-disc-type L)
-- label-from-disc-type-dim-lem {S = Sing} L = refl
-- label-from-disc-type-dim-lem {S = Join S Sing} L = begin
--   suc (tree-dim S) + sty-dim (lty L)
--     ≡˘⟨ +-suc (tree-dim S) (sty-dim (proj₂ L)) ⟩
--   tree-dim S + suc (sty-dim (lty L))
--     ≡⟨ label-from-disc-type-dim-lem (label₁ L) ⟩
--   sty-dim (label-from-disc-type (label₁ L)) ∎
--   where
--     open ≡-Reasoning

-- label-from-disc-type-lem : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → label-from-linear-tree-type S (label-from-disc-type L) ≃sty lty L
-- label-from-disc-type-lem {S = Sing} L = refl≃sty
-- label-from-disc-type-lem {S = Join S Sing} L = begin
--   < label-from-linear-tree-type S (sty-base (label-from-disc-type (label₁ L))) >sty
--     ≈⟨ label-from-linear-tree-type-prop S (label-from-disc-type (label₁ L)) ⟩
--   < sty-base (label-from-linear-tree-type S (label-from-disc-type (label₁ L))) >sty
--     ≈⟨ sty-base-≃ (label-from-disc-type-lem (label₁ L)) ⟩
--   < lty L >sty ∎
--   where
--     open Reasoning sty-setoid

-- label-from-linear-tree-prop : .⦃ _ : is-linear S ⦄ → (L : Label-WT X S) → ap L ≃l label-from-linear-tree S (label-from-disc-term L) (label-from-disc-type L) (≤-trans (m≤m+n (tree-dim S) (sty-dim (lty L))) (≤-reflexive (label-from-disc-type-dim-lem L)))
-- label-from-linear-tree-prop {S = Sing} L .get PHere = refl≃stm
-- label-from-linear-tree-prop {S = Join S Sing} L .get PHere = sym≃stm (sty-src-≃ (label-from-disc-type-lem (label₁ L)) ⦃ _ ⦄)
-- label-from-linear-tree-prop {S = Join S Sing} L .get (PExt P) = label-from-linear-tree-prop (label₁ L) .get P
-- label-from-linear-tree-prop {S = Join S Sing} L .get (PShift PHere) = sym≃stm (sty-tgt-≃ (label-from-disc-type-lem (label₁ L)) ⦃ _ ⦄)

-- label-from-disc-type-prop : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → label-from-disc-type L ≃sty canonical-type (tree-dim S) S >>=′ L
-- label-from-disc-type-prop {S = Sing} L = refl≃sty
-- label-from-disc-type-prop {S = Join S Sing} L = begin
--   < label-from-disc-type (label₁ L) >sty
--     ≈⟨ label-from-disc-type-prop (label₁ L) ⟩
--   < canonical-type (tree-dim S) S >>=′ label₁ L >sty
--     ≈˘⟨ map-sty-ext-label (canonical-type (tree-dim S) S) L ⟩
--   < map-sty-ext (canonical-type (tree-dim S) S) >>=′ L >sty
--     ≈⟨ >>=′-≃ (map-sty-ext-susp-compat (canonical-type (tree-dim S) S)) refl≃l refl≃sty ⟩
--   < susp-sty (canonical-type (tree-dim S) S) >>=′ L >sty
--     ≈⟨ >>=′-≃ (canonical-type-susp-lem (tree-dim S) S) refl≃l refl≃sty ⟩
--   < canonical-type (suc (tree-dim S)) (susp-tree S) >>=′ L >sty ∎
--   where
--     open Reasoning sty-setoid

-- label-from-disc-term-prop : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → label-from-disc-term L ≃stm ap L (is-linear-max-path S)
-- label-from-disc-term-prop {S = Sing} L = refl≃stm
-- label-from-disc-term-prop {S = Join S Sing} L = label-from-disc-term-prop (label₁ L)

-- canonical-type-linear : (d : ℕ) → (S : Tree n) → .⦃ _ : is-linear S ⦄ → .(d ≡ tree-dim S) → sty-to-type (canonical-type d S) ≃ty lift-ty (sphere-type d)
-- canonical-type-linear zero Sing p = refl≃ty
-- canonical-type-linear (suc d) (Join S Sing) p = begin
--   < sty-to-type (canonical-type (suc d) (susp-tree S)) >ty
--     ≈˘⟨ canonical-type-susp-lem d S .get ⟩
--   < sty-to-type (susp-sty (canonical-type d S)) >ty
--     ≈⟨ susp-sty-to-type (canonical-type d S) ⟩
--   < susp-ty (sty-to-type (canonical-type d S)) >ty
--     ≈⟨ susp-ty-≃ (canonical-type-linear d S (cong pred p)) ⟩
--   < susp-ty (lift-ty (sphere-type d)) >ty
--     ≈⟨ susp-ty-lift (sphere-type d) ⟩
--   < lift-ty (susp-ty (sphere-type d)) >ty
--     ≈⟨ lift-ty-≃ (sphere-type-susp d) ⟩
--   < lift-ty (sphere-type (suc d)) >ty ∎
--   where
--     open Reasoning ty-setoid

-- canonical-term-linear : (d : ℕ) → (S : Tree n) → .⦃ _ : is-linear S ⦄ → .(d ≡ tree-dim S) → stm-to-term (canonical-stm d S) ≃tm (0V {n = suc n})
-- canonical-term-linear zero Sing p = refl≃tm
-- canonical-term-linear (suc d) (Join S Sing) p = begin
--   < susp-tm (stm-to-term (canonical-stm d S)) [ idSub ]tm >tm
--     ≈⟨ id-on-tm (susp-tm (stm-to-term (canonical-stm d S))) ⟩
--   < susp-tm (stm-to-term (canonical-stm d S)) >tm
--     ≈⟨ susp-tm-≃ (canonical-term-linear d S (cong pred p)) ⟩
--   < 0V >tm ∎
--   where
--     open Reasoning tm-setoid

-- identity-stm-to-term : (n : ℕ) → stm-to-term (identity-stm n) ≃tm identity n idSub
-- identity-stm-to-term n = begin
--   < stm-to-term (identity-stm n) >tm
--     ≈⟨ canonical-comp′-compat (suc n) (n-disc n) .get ⟩
--   < stm-to-term (canonical-comp (suc n) (n-disc n)) >tm
--     ≈⟨ Coh≃ lem1 lem3 lem4 ⟩
--   < identity n idSub >tm ∎
--   where
--     lem1 : tree-to-ctx (n-disc n) ≃c Disc n
--     lem1 = begin
--       < tree-to-ctx (n-disc n) >c
--         ≈⟨ linear-tree-compat (n-disc n) ⟩
--       < Disc (tree-dim (n-disc n)) >c
--         ≈⟨ disc-≡ (≃n-to-≡ it) ⟩
--       < Disc n >c ∎
--       where
--         open Reasoning ctx-setoid

--     lem2 : (b : Bool) → stm-to-term
--              (canonical-stm n (tree-bd n (n-disc n)) >>=
--               tree-inc-label n (n-disc n) b)
--              ≃tm (0V {n = suc (double n)})
--     lem2 b = begin
--       < stm-to-term (canonical-stm n (tree-bd n (n-disc n)) >>= tree-inc-label n (n-disc n) b) >tm
--         ≈˘⟨ label-to-sub-stm (tree-inc-label n (n-disc n) b) (canonical-stm n (tree-bd n (n-disc n))) ⟩
--       < stm-to-term (canonical-stm n (tree-bd n (n-disc n))) [ label-to-sub (tree-inc-label n (n-disc n) b) ]tm >tm
--         ≈⟨ sub-action-≃-tm {s = stm-to-term (canonical-stm n (tree-bd n (n-disc n)))}
--                            {t = stm-to-term (canonical-stm n (n-disc n))}
--                            (canonical-stm-≃ (refl {x = n}) (≃′-to-≃ (tree-bd-full n (n-disc n) (≤-reflexive (≃n-to-≡ it)))) .get)
--                            (tree-inc-full n (n-disc n) b (≤-reflexive (≃n-to-≡ it))) ⟩
--       < stm-to-term (canonical-stm n (n-disc n)) [ idSub ]tm >tm
--         ≈⟨ id-on-tm (stm-to-term (canonical-stm n (n-disc n))) ⟩
--       < stm-to-term (canonical-stm n (n-disc n)) >tm
--         ≈⟨ canonical-term-linear n (n-disc n) (sym (≃n-to-≡ it)) ⟩
--       < 0V >tm ∎
--       where
--         open Reasoning tm-setoid

--     lem3 : sty-to-type (canonical-type (suc n) (n-disc n)) ≃ty
--              (Var 0F ─⟨ lift-ty (sphere-type n) ⟩⟶ Var 0F)
--     lem3 = Arr≃ (lem2 false) (canonical-type-linear n (n-disc n) (sym (≃n-to-≡ it))) (lem2 true)

--     lem4 : label-to-sub (id-label (n-disc n) ,, S⋆) ● idSub ≃s idSub
--     lem4 = begin
--       < label-to-sub (id-label (n-disc n) ,, S⋆) ● idSub >s
--         ≈⟨ id-right-unit (label-to-sub (id-label (n-disc n) ,, S⋆)) ⟩
--       < label-to-sub (id-label (n-disc n) ,, S⋆) >s
--         ≈⟨ id-label-to-sub (n-disc n) ⟩
--       < idSub >s ∎
--       where
--         open Reasoning sub-setoid
--     open Reasoning tm-setoid

-- label-to-sub-from-disc-term : (L : Label-WT X (n-disc d)) → sub-from-disc-term (label-to-sub L) ≃tm stm-to-term (label-from-disc-term L ⦃ n-disc-is-linear d ⦄)
-- label-to-sub-from-disc-term {d = zero} L = refl≃tm
-- label-to-sub-from-disc-term {d = suc d} L = begin
--   < sub-from-disc-term (label-to-sub L) >tm
--     ≈⟨ sub-from-disc-term-unrestrict (label-to-sub (label₁ L)) ⟩
--   < sub-from-disc-term (label-to-sub (label₁ L)) >tm
--     ≈⟨ label-to-sub-from-disc-term (label₁ L) ⟩
--   < stm-to-term (label-from-disc-term (label₁ L) ⦃ _ ⦄) >tm ∎
--   where
--     open Reasoning tm-setoid

-- label-to-sub-from-disc-type : (L : Label-WT X (n-disc d)) → sub-from-disc-type (label-to-sub L) ≃ty sty-to-type (label-from-disc-type L ⦃ n-disc-is-linear d ⦄)
-- label-to-sub-from-disc-type {d = zero} L = refl≃ty
-- label-to-sub-from-disc-type {d = suc d} L = begin
--   < sub-from-disc-type (label-to-sub L) >ty
--     ≈⟨ sub-from-disc-type-unrestrict (label-to-sub (label₁ L)) ⟩
--   < sub-from-disc-type (label-to-sub (label₁ L)) >ty
--     ≈⟨ label-to-sub-from-disc-type (label₁ L) ⟩
--   < sty-to-type (label-from-disc-type (label₁ L) ⦃ _ ⦄) >ty ∎
--   where
--     open Reasoning ty-setoid

-- label-from-linear-tree-disc-type : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (a : STm X) → (As : STy X) → .(p : tree-dim S ≤ sty-dim As) → (Bs : STy X) → (Bs ≃sty label-from-linear-tree-type S As) → label-from-disc-type (label-from-linear-tree S a As p ,, Bs) ≃sty As
-- label-from-linear-tree-disc-type Sing a As p Bs q = q
-- label-from-linear-tree-disc-type (Join S Sing) a As p Bs q = label-from-linear-tree-disc-type S a As _ _ (trans≃sty (SArr≃ refl≃stm (trans≃sty q (label-from-linear-tree-type-prop S As)) refl≃stm) (sty-prop (label-from-linear-tree-type S As) ⦃ label-from-linear-tree-nz S As p ⦄))

-- label-from-linear-tree-disc-term : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (a : STm X) → (As : STy X) → .(p : tree-dim S ≤ sty-dim As) → (Bs : STy X) → label-from-disc-term (label-from-linear-tree S a As p ,, Bs) ≃stm a
-- label-from-linear-tree-disc-term Sing a As p Bs = refl≃stm
-- label-from-linear-tree-disc-term (Join S Sing) a As p Bs = label-from-linear-tree-disc-term S a As _ _

-- label-from-linear-tree-to-sub : (d : ℕ) → (a : STm X) → (As : STy X) → .(p : d ≡ sty-dim As) → label-to-sub (label-from-linear-tree (n-disc d) ⦃ n-disc-is-linear d ⦄ a As (≤-reflexive (trans (tree-dim-n-disc d) p)) ,, S⋆) ≃s sub-from-disc d (sty-to-type As) (trans (sty-to-type-dim As) (sym p)) (stm-to-term a)
-- label-from-linear-tree-to-sub d a As p = begin
--   < label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) >s
--     ≈⟨ prop-sub-from-disc (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)) ⟩
--   < sub-from-disc d
--     (sub-from-disc-type
--      (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)))
--     _
--     (sub-from-disc-term
--       (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)))
--     >s
--     ≈⟨ sub-from-disc-≃ d d lem1 (sub-from-disc-type-dim
--                                   (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆))) (trans (sty-to-type-dim As) (sym p)) lem2 ⟩
--   < sub-from-disc d (sty-to-type As) _ (stm-to-term a) >s ∎
--   where
--     lem1 : sub-from-disc-type (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆))
--          ≃ty sty-to-type As
--     lem1 = begin
--       < sub-from-disc-type (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)) >ty
--         ≈⟨ label-to-sub-from-disc-type (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) ⟩
--       < sty-to-type (label-from-disc-type (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) ⦃ _ ⦄) >ty
--         ≈⟨ label-from-linear-tree-disc-type (n-disc d) ⦃ _ ⦄ a As _ S⋆ (sym≃sty (label-from-linear-tree-type-0 (n-disc d) ⦃ _ ⦄ As (trans (tree-dim-n-disc d) p))) .get ⟩
--       < sty-to-type As >ty ∎
--       where
--         open Reasoning ty-setoid

--     lem2 : sub-from-disc-term (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As (≤-reflexive (trans (tree-dim-n-disc d) p)) ,, S⋆))
--          ≃tm stm-to-term a
--     lem2 = begin
--       < sub-from-disc-term (label-to-sub (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆)) >tm
--         ≈⟨ label-to-sub-from-disc-term (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) ⟩
--       < stm-to-term (label-from-disc-term (label-from-linear-tree (n-disc d) ⦃ _ ⦄ a As _ ,, S⋆) ⦃ _ ⦄) >tm
--         ≈⟨ label-from-linear-tree-disc-term (n-disc d) ⦃ _ ⦄ a As _ S⋆ .get ⟩
--       < stm-to-term a >tm ∎
--       where
--         open Reasoning tm-setoid

--     open Reasoning sub-setoid
