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
                       → extend-disc-label L t a (disc-inc d (Susp S) b) ≃stm L (disc-inc d S b)
extend-disc-label-bd-< {S = Susp S} L t a zero q false = refl≃stm
extend-disc-label-bd-< {S = Susp S} L t a zero q true = refl≃stm
extend-disc-label-bd-< {S = Susp S} L t a (suc d) q b = extend-disc-label-bd-< (L ∘ PExt) t a d (≤-pred q) b

extend-disc-label-bd-≡ : (L : Label X S)
                       → .⦃ _ : is-linear S ⦄
                       → (t : STm X)
                       → (a : STm X)
                       → (d : ℕ)
                       → (d ≡ tree-dim S)
                       → (b : Bool)
                       → extend-disc-label L t a (disc-inc d (Susp S) b)
                         ≃stm
                         (if b then t else L (is-linear-max-path S))
extend-disc-label-bd-≡ {S = Sing} L t a zero p false = refl≃stm
extend-disc-label-bd-≡ {S = Sing} L t a zero p true = refl≃stm
extend-disc-label-bd-≡ {S = Susp S} L t a (suc d) p b = extend-disc-label-bd-≡ (L ∘ PExt) t a d (cong pred p) b

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
  canonical-label-bd-<-lem (Susp S) T d b q a with <-cmp d (tree-dim S)
  ... | tri< x _ _ = begin
    < extend-disc-label
      (stm-to-label S
       (canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
        (tree-inc-label (tree-dim S) T false))
       (canonical-type (tree-dim S) T))
      (canonical-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
       (tree-inc-label (tree-dim S) T true))
      a
      (disc-inc d (Susp S) b) >stm
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
      (disc-inc d (Susp S) false) >stm
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

canonical-type-susp-lem : (d : ℕ) → (T : Tree n) → susp-sty (canonical-type d T) ≃sty canonical-type (suc d) (Susp T)
canonical-comp-susp-lem : (d : ℕ) → (T : Tree n) → SExt {T = Sing} (canonical-comp d T) ≃stm canonical-comp (suc d) (Susp T)

canonical-type-susp-lem zero T = SArr≃ [ refl≃tm ] refl≃sty [ refl≃tm ]
canonical-type-susp-lem (suc d) T = SArr≃ (lem false) (canonical-type-susp-lem d T) (lem true)
  where
    open Reasoning stm-setoid
    lem : (b : Bool) → susp-stm (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm (canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (Susp T) b))
    lem b = begin
      < SExt (canonical-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm
        ≈˘⟨ >>=-ext (canonical-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < canonical-stm d (tree-bd d T) >>= map-ext (tree-inc-label d T b) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = canonical-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
      < canonical-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (Susp T) b) >stm ∎

canonical-comp-susp-lem d T = begin
  < SExt (canonical-comp d T) >stm
    ≈˘⟨ SCoh-ext T (canonical-type d T) (id-label-wt T) ⟩
  < SCoh T (canonical-type d T) (map-ext (id-label-wt T)) >stm
    ≈⟨ SCoh-unrestrict T (canonical-type d T) (map-ext (id-label-wt T)) ⟩
  < SCoh (Susp T) (susp-sty (canonical-type d T)) (susp-label-full (id-label T) ,, S⋆) >stm
    ≈⟨ SCoh≃ (Susp T) (canonical-type-susp-lem d T) (id-label-susp-full T) refl≃sty ⟩
  < canonical-comp (suc d) (Susp T) >stm ∎
  where
    open Reasoning stm-setoid

canonical-label-susp-lem : (S : Tree m)
                         → .⦃ _ : is-linear S ⦄
                         → (T : Tree n)
                         → canonical-label (Susp S) (Susp T) ≃l susp-label-full (canonical-label S T)
canonical-label-susp-lem S ⦃ lin ⦄ T = begin
  < canonical-label (Susp S) (Susp T) >l
    ≈⟨ stm-to-label-≃ (Susp S) refl≃stm
                      (sym≃sty (canonical-type-susp-lem (tree-dim S) T)) ⦃ inst ⦄ ⟩
  < stm-to-label (Susp S)
                 (susp-stm (canonical-comp′ (tree-dim S) T))
                 (susp-sty (canonical-type (tree-dim S) T))
                 ⦃ trans≃n inst (≡-to-≃n (sym (susp-sty-dim (canonical-type (tree-dim S) T)))) ⦄
   >l
    ≈⟨ stm-to-label-susp S (canonical-comp′ (tree-dim S) T) (canonical-type (tree-dim S) T) ⟩
  < susp-label-full (canonical-label S T) >l ∎
  where
    open Reasoning (label-setoid (Susp S))

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
disc-sty-is-canonical (Susp S) = begin
  < disc-sty (Susp S) >sty
    ≈⟨ map-sty-ext-susp-compat (disc-sty S) ⟩
  < susp-sty (disc-sty S) >sty
    ≈⟨ susp-sty-≃ (disc-sty-is-canonical S) ⟩
  < susp-sty (canonical-type (tree-dim S) S) >sty
    ≈⟨ canonical-type-susp-lem (tree-dim S) S ⟩
  < canonical-type (tree-dim (Susp S)) (Susp S) >sty ∎
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
