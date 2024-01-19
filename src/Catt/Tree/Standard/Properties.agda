module Catt.Tree.Standard.Properties where

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
open import Catt.Tree.Standard

standard-type-dim : (d : ℕ) → (T : Tree n) → sty-dim (standard-type d T) ≡ d
standard-type-dim zero T = refl
standard-type-dim (suc d) T = cong suc (standard-type-dim d T)

standard-type-≃ : d ≡ d′ → (S ≃ T) → standard-type d S ≃sty standard-type d′ T
standard-type-≃ refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃sty

standard-comp-≃ : d ≡ d′ → (S ≃ T) → standard-comp d S ≃stm standard-comp d′ T
standard-comp-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

standard-comp′-≃ : d ≡ d′ → (S ≃ T) → standard-comp′ d S ≃stm standard-comp′ d′ T
standard-comp′-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

standard-stm-≃ : d ≡ d′ → (S ≃ T) → standard-stm d S ≃stm standard-stm d′ T
standard-stm-≃ {S = S} refl q with ≃-to-same-n q
... | refl with ≃-to-≡ q
... | refl = refl≃stm

standard-stm-≃-prop : (d : ℕ) → (p : S ≃′ T) → (standard-stm d S >>= (SPath ∘ ppath-≃ p ,, S⋆)) ≃stm standard-stm d T
standard-stm-≃-prop {S = S} {T = T} d p = begin
  < standard-stm d S >>= (SPath ∘ ppath-≃ p ,, S⋆) >stm
    ≈⟨ >>=-≃ (refl≃stm {a = standard-stm d S}) (ppath-≃l p) (S⋆-≃ (sym≃ (≃′-to-≃ p))) ⟩
  < standard-stm d S >>= id-label-wt S >stm
    ≈⟨ >>=-id (standard-stm d S) ⟩
  < standard-stm d S >stm
    ≈⟨ standard-stm-≃ refl (≃′-to-≃ p) ⟩
  < standard-stm d T >stm ∎
  where open Reasoning stm-setoid

standard-stm-linear : (d : ℕ) → (T : Tree n) → .⦃ _ : is-linear T ⦄ → .(d ≡ tree-dim T) → standard-stm d T ≃stm SPath (is-linear-max-path T)
standard-stm-linear zero Sing p = [ refl≃tm ]
standard-stm-linear (suc d) (Join T Sing) p = compute-≃ (SExt≃ (standard-stm-linear d T (cong pred p)) refl≃)

standard-stm-bd-non-linear : (d : ℕ) → (T : Tree n) → .(d > trunk-height T) → standard-stm d (tree-bd d T) ≃stm standard-comp′ d (tree-bd d T)
standard-stm-bd-non-linear (suc d) Sing p = refl≃stm
standard-stm-bd-non-linear (suc d) (Join T Sing) p = SExt≃ (standard-stm-bd-non-linear d T (≤-pred p)) Sing≃
standard-stm-bd-non-linear (suc d) (Join T (Join T₁ T₂)) p = refl≃stm

standard-stm-full-lem : (d : ℕ) → (T : Tree n) → (b : Bool) → (tree-dim T ≤ d) → (standard-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm standard-stm d T
standard-stm-full-lem d T b p = begin
  < standard-stm d (tree-bd d T) >>= tree-inc-label d T b >stm
    ≈⟨ >>=-≃ (refl≃stm {a = standard-stm d (tree-bd d T)}) [ (λ P → SPath≃ (tree-inc-label-full d T b p .get P)) ] refl≃sty ⟩
  < standard-stm d (tree-bd d T) >>= ((λ z → SPath (ppath-≃ (tree-bd-full d T p) z)) ,, S⋆) >stm
    ≈˘⟨ >>=-≃ (refl≃stm {a = standard-stm d (tree-bd d T)}) [ (λ P → SPath≃ (ppath-≃-≃p (tree-bd-full d T p) P)) ] [ (Star≃ (cong suc (≃-to-same-n (≃′-to-≃ (tree-bd-full d T p))))) ] ⟩
  < standard-stm d (tree-bd d T) >>= id-label-wt (tree-bd d T) >stm
    ≈⟨ >>=-id (standard-stm d (tree-bd d T)) ⟩
  < standard-stm d (tree-bd d T) >stm
    ≈⟨ standard-stm-≃ refl (≃′-to-≃ (tree-bd-full d T p)) ⟩
  < standard-stm d T >stm ∎
  where
    open Reasoning stm-setoid

standard-term-≃ : (d ≡ d′) → S ≃ T → standard-term d S ≃tm standard-term d′ T
standard-term-≃ refl p with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = refl≃tm

standard-type-prop : (d : ℕ) → (T : Tree n) → (d′ : ℕ) → (d ≤ d′) → (b : Bool) → standard-type d T ≃sty standard-type d (tree-bd d′ T) >>=′ tree-inc-label d′ T b
standard-type-prop zero T d′ p b = refl≃sty
standard-type-prop (suc d) T d′ p b = SArr≃ (lem false) (standard-type-prop d T d′ (≤-trans (n≤1+n d) p) b) (lem true)
  where
    lem : (b′ : Bool) → (standard-stm d (tree-bd d T) >>= tree-inc-label d T b′)
      ≃stm (standard-stm d (tree-bd d (tree-bd d′ T)) >>=
        tree-inc-label d (tree-bd d′ T) b′ >>= tree-inc-label d′ T b)
    lem b′ = begin
      < standard-stm d (tree-bd d T) >>= tree-inc-label d T b′ >stm
        ≈˘⟨ >>=-≃′ (standard-stm-≃ {d = d} refl (≃′-to-≃ (tree-bd-glob d d′ T p))) ((tree-bd-glob d d′ T p) ,, [ (λ P → SPath≃ (tree-inc-label-glob d d′ T b′ b p .get P)) ]) refl≃sty ⟩
      < standard-stm d (tree-bd d (tree-bd d′ T))
        >>= tree-inc-label d (tree-bd d′ T) b′ ●lt tree-inc-label d′ T b >stm
        ≈˘⟨ >>=-assoc (standard-stm d (tree-bd d (tree-bd d′ T))) _ _ ⟩
      < standard-stm d (tree-bd d (tree-bd d′ T))
        >>= tree-inc-label d (tree-bd d′ T) b′
        >>= tree-inc-label d′ T b >stm ∎
      where
        open Reasoning stm-setoid

instance
  standard-type-1-Full : {d : ℕ} → .⦃ NonZero d ⦄ → {T : Tree n} → 1-Full (standard-type d T)
  standard-type-1-Full {d = 1} .p₁ = refl≃stm
  standard-type-1-Full {d = 1} .p₂ = refl≃stm
  standard-type-1-Full {d = 2+ d} = inst

standard-label-max : (S : Tree n)
                    → .⦃ _ : is-linear S ⦄
                    → (T : Tree m)
                    → (Z : Path S)
                    → .⦃ is-maximal Z ⦄
                    → standard-label S T Z ≃stm standard-comp′ (tree-dim S) T
standard-label-max S T
  = stm-to-label-max S (standard-comp′ (tree-dim S) T) (standard-type (tree-dim S) T)

standard-label-fst : (S : Tree n)
                    → .⦃ _ : is-linear S ⦄
                    → .⦃ NonZero (tree-dim S) ⦄
                    → (T : Tree m)
                    → standard-label S T PHere ≃stm SHere {S = T}
standard-label-fst S T = stm-to-label-1-Full-src S (standard-comp′ (tree-dim S) T) (standard-type (tree-dim S) T)

standard-label-last : (S : Tree n)
                     → .⦃ _ : is-linear S ⦄
                     → .⦃ NonZero (tree-dim S) ⦄
                     → (T : Tree m)
                     → standard-label S T (last-path S) ≃stm SPath (last-path T)
standard-label-last S T = stm-to-label-1-Full-tgt S (standard-comp′ (tree-dim S) T) (standard-type (tree-dim S) T)

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
  standard-label-bd-<-lem : (S : Tree n)
                           → .⦃ _ : is-linear S ⦄
                           → (T : Tree m)
                           → (d : ℕ)
                           → (b : Bool)
                           → (d < tree-dim S)
                           → (a : STm (someTree T))
                           → stm-to-label S a (standard-type (tree-dim S) T) (disc-inc d S b)
                             ≃stm
                             standard-stm d (tree-bd d T) >>= tree-inc-label d T b
  standard-label-bd-<-lem (Susp S) T d b q a with <-cmp d (tree-dim S)
  ... | tri< x _ _ = begin
    < extend-disc-label
      (stm-to-label S
       (standard-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
        (tree-inc-label (tree-dim S) T false))
       (standard-type (tree-dim S) T))
      (standard-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
       (tree-inc-label (tree-dim S) T true))
      a
      (disc-inc d (Susp S) b) >stm
      ≈⟨ extend-disc-label-bd-< _ _ a d x b ⟩
    < stm-to-label S
      (standard-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
        tree-inc-label (tree-dim S) T false)
      (standard-type (tree-dim S) T) (disc-inc d S b) >stm
      ≈⟨ standard-label-bd-<-lem S T d b x _ ⟩
    < standard-stm d (tree-bd d T) >>= tree-inc-label d T b >stm ∎
  ... | tri> ¬a ¬b c = ⊥-elim (1+n≰n (≤-trans q c))
  ... | tri≈ _ refl _ with b
  ... | false = begin
    < extend-disc-label
      (stm-to-label S
       (standard-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
        (tree-inc-label (tree-dim S) T false))
       (standard-type (tree-dim S) T))
      (standard-stm (tree-dim S) (tree-bd (tree-dim S) T) >>=
       (tree-inc-label (tree-dim S) T true))
      a
      (disc-inc d (Susp S) false) >stm
      ≈⟨ extend-disc-label-bd-≡ _ _ a d refl false ⟩
    < stm-to-label S (standard-stm (tree-dim S) (tree-bd (tree-dim S) T) >>= tree-inc-label (tree-dim S) T false)  (standard-type (tree-dim S) T) (is-linear-max-path S)
     >stm
      ≈⟨ stm-to-label-max S _ _ (is-linear-max-path S) ⟩
    < standard-stm (tree-dim S) (tree-bd (tree-dim S) T) >>= tree-inc-label (tree-dim S) T false >stm ∎
  ... | true = extend-disc-label-bd-≡ _ _ a d refl true


standard-label-bd-< : (S : Tree n)
                     → .⦃ _ : is-linear S ⦄
                     → (T : Tree m)
                     → (d : ℕ)
                     → (b : Bool)
                     → (d < tree-dim S)
                     → (Z : Path (tree-bd d S))
                     → .⦃ is-maximal Z ⦄
                     → standard-label S T (tree-inc-label′ d S b Z)
                       ≃stm
                       standard-stm d (tree-bd d T) >>= tree-inc-label d T b
standard-label-bd-< S T d b q Z = begin
  < standard-label S T (tree-inc-label′ d S b Z) >stm
    ≈˘⟨ ap-≃ (refl≃l {L = standard-label S T}) (ap′-≃ (tree-inc-label′ d S b) (max-path-lin-tree (tree-bd d S) ⦃ _ ⦄ Z refl≃)) ⟩
  < standard-label S T (disc-inc d S b) >stm
    ≈⟨ standard-label-bd-<-lem S T d b q (standard-comp′ (tree-dim S) T) ⟩
  < standard-stm d (tree-bd d T) >>= tree-inc-label d T b >stm ∎
  where
    open Reasoning stm-setoid

module _ where
  open Reasoning stm-setoid
  standard-label-bd->-trunk-height : (S : Tree n)
    → .⦃ _ : is-linear S ⦄
    → (T : Tree m)
    → (d : ℕ)
    → (b : Bool)
    → (d ≤ tree-dim S)
    → (d > trunk-height T)
    → (tree-dim S ≥ tree-dim T)
    → (Z : Path (tree-bd d S))
    → .⦃ is-maximal Z ⦄
    → standard-label S T (tree-inc-label′ d S b Z)
      ≃stm
      standard-comp′ d (tree-bd d T) >>= tree-inc-label d T b
  standard-label-bd->-trunk-height S T d b p q r Z with <-cmp d (tree-dim S)
  ... | tri< x _ _ = begin
    < standard-label S T (tree-inc-label′ d S b Z) >stm
      ≈⟨ standard-label-bd-< S T d b x Z ⟩
    < standard-stm d (tree-bd d T) >>= tree-inc-label d T b >stm
      ≈⟨ >>=-≃ (standard-stm-bd-non-linear d T q) refl≃l refl≃sty ⟩
    < standard-comp′ d (tree-bd d T) >>= tree-inc-label d T b >stm ∎
  ... | tri≈ _ x _ = begin
    < standard-label S T (tree-inc-label′ d S b Z) >stm
      ≈⟨ standard-label-max S T _ ⦃ tree-inc-full-preserve-max d S b (≤-reflexive (sym x)) Z ⦄ ⟩
    < standard-comp′ (tree-dim S) T >stm
      ≈˘⟨ standard-comp′-≃ x (≃′-to-≃ (tree-bd-full d T (≤-trans r (≤-reflexive (sym x))))) ⟩
    < standard-comp′ d (tree-bd d T) >stm
      ≈˘⟨ >>=-id (standard-comp′ d (tree-bd d T)) ⟩
    < standard-comp′ d (tree-bd d T) >>= id-label-wt (tree-bd d T) >stm
      ≈˘⟨ >>=-≃ (refl≃stm {a = standard-comp′ d (tree-bd d T)}) (tree-inc-label-full-is-id d T b (≤-trans r (≤-reflexive (sym x)))) (S⋆-≃ (sym≃ (≃′-to-≃ (tree-bd-full d T (≤-trans r (≤-reflexive (sym x))))))) ⟩
    < standard-comp′ d (tree-bd d T) >>= tree-inc-label d T b >stm ∎
  ... | tri> ¬a ¬b c = ⊥-elim (1+n≰n (≤-trans c p))

standard-type-susp-lem : (d : ℕ) → (T : Tree n) → susp-sty (standard-type d T) ≃sty standard-type (suc d) (Susp T)
standard-comp-susp-lem : (d : ℕ) → (T : Tree n) → SExt {T = Sing} (standard-comp d T) ≃stm standard-comp (suc d) (Susp T)

standard-type-susp-lem zero T = SArr≃ [ refl≃tm ] refl≃sty [ refl≃tm ]
standard-type-susp-lem (suc d) T = SArr≃ (lem false) (standard-type-susp-lem d T) (lem true)
  where
    open Reasoning stm-setoid
    lem : (b : Bool) → susp-stm (standard-stm d (tree-bd d T) >>= tree-inc-label d T b) ≃stm (standard-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (Susp T) b))
    lem b = begin
      < SExt (standard-stm d (tree-bd d T) >>= tree-inc-label d T b) >stm
        ≈˘⟨ >>=-ext (standard-stm d (tree-bd d T)) (tree-inc-label d T b) ⟩
      < standard-stm d (tree-bd d T) >>= map-ext (tree-inc-label d T b) >stm
        ≈⟨ >>=-≃ (refl≃stm {a = standard-stm d (tree-bd d T)}) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm)) ⟩
      < standard-stm d (tree-bd d T) >>= label₁ (tree-inc-label (suc d) (Susp T) b) >stm ∎

standard-comp-susp-lem d T = begin
  < SExt (standard-comp d T) >stm
    ≈˘⟨ SCoh-ext T (standard-type d T) (id-label-wt T) ⟩
  < SCoh T (standard-type d T) (map-ext (id-label-wt T)) >stm
    ≈⟨ SCoh-unrestrict T (standard-type d T) (map-ext (id-label-wt T)) ⟩
  < SCoh (Susp T) (susp-sty (standard-type d T)) (susp-label-full (id-label T) ,, S⋆) >stm
    ≈⟨ SCoh≃ (Susp T) (standard-type-susp-lem d T) (id-label-susp-full T) refl≃sty ⟩
  < standard-comp (suc d) (Susp T) >stm ∎
  where
    open Reasoning stm-setoid

standard-label-susp-lem : (S : Tree m)
                         → .⦃ _ : is-linear S ⦄
                         → (T : Tree n)
                         → standard-label (Susp S) (Susp T) ≃l susp-label-full (standard-label S T)
standard-label-susp-lem S ⦃ lin ⦄ T = begin
  < standard-label (Susp S) (Susp T) >l
    ≈⟨ stm-to-label-≃ (Susp S) refl≃stm
                      (sym≃sty (standard-type-susp-lem (tree-dim S) T)) ⦃ inst ⦄ ⟩
  < stm-to-label (Susp S)
                 (susp-stm (standard-comp′ (tree-dim S) T))
                 (susp-sty (standard-type (tree-dim S) T))
                 ⦃ trans≃n inst (≡-to-≃n (sym (susp-sty-dim (standard-type (tree-dim S) T)))) ⦄
   >l
    ≈⟨ stm-to-label-susp S (standard-comp′ (tree-dim S) T) (standard-type (tree-dim S) T) ⟩
  < susp-label-full (standard-label S T) >l ∎
  where
    open Reasoning (label-setoid (Susp S))

standard-comp′-compat : (d : ℕ) → (T : Tree n) → standard-comp′ d T ≃stm standard-comp d T
standard-comp′-compat zero T = refl≃stm
standard-comp′-compat (suc d) Sing = refl≃stm
standard-comp′-compat (suc d) (Join T Sing) = begin
  < SExt (standard-comp′ d T) >stm
    ≈⟨ SExt≃ (standard-comp′-compat d T) Sing≃ ⟩
  < SExt (standard-comp d T) >stm
    ≈⟨ standard-comp-susp-lem d T ⟩
  < standard-comp (suc d) (Join T Sing) >stm ∎
  where
    open Reasoning stm-setoid
standard-comp′-compat (suc d) T@(Join _ (Join _ _)) = refl≃stm

disc-sty-is-standard : (S : Tree n) → .⦃ _ : is-linear S ⦄ → disc-sty S ≃sty standard-type (tree-dim S) S
disc-sty-is-standard Sing = refl≃sty
disc-sty-is-standard (Susp S) = begin
  < disc-sty (Susp S) >sty
    ≈⟨ map-sty-ext-susp-compat (disc-sty S) ⟩
  < susp-sty (disc-sty S) >sty
    ≈⟨ susp-sty-≃ (disc-sty-is-standard S) ⟩
  < susp-sty (standard-type (tree-dim S) S) >sty
    ≈⟨ standard-type-susp-lem (tree-dim S) S ⟩
  < standard-type (tree-dim (Susp S)) (Susp S) >sty ∎
  where
    open Reasoning sty-setoid

disc-stm-is-standard : (S : Tree n) → .⦃ _ : is-linear S ⦄ → disc-stm S ≃stm standard-comp (tree-dim S) S
disc-stm-is-standard S = SCoh≃ S (disc-sty-is-standard S) refl≃l refl≃sty

identity-stm-is-standard : (S : Tree n) → .⦃ _ : is-linear S ⦄ → identity-stm S ≃stm standard-comp (suc (tree-dim S)) S
identity-stm-is-standard S = SCoh≃ S (SArr≃ (lem false) (disc-sty-is-standard S) (lem true)) refl≃l refl≃sty
  where
    open Reasoning stm-setoid
    lem : (b : Bool) → SPath (is-linear-max-path S)
                       ≃stm
                       standard-stm (tree-dim S) (tree-bd (tree-dim S) S) >>= tree-inc-label (tree-dim S) S b
    lem b = begin
      < SPath (is-linear-max-path S) >stm
        ≈˘⟨ standard-stm-linear (tree-dim S) S refl ⟩
      < standard-stm (tree-dim S) S >stm
        ≈˘⟨ standard-stm-full-lem (tree-dim S) S b ≤-refl ⟩
      < standard-stm (tree-dim S) (tree-bd (tree-dim S) S) >>= tree-inc-label (tree-dim S) S b >stm ∎
truncate-standard-sty : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → truncate-sty 1 (standard-type d T) ≃sty SArr SHere S⋆ (SPath (last-path T))
truncate-standard-sty (suc zero) T = refl≃sty
truncate-standard-sty (suc (suc d)) T = begin
  < truncate-sty 1 (standard-type (suc (suc d)) T) >sty
    ≈⟨ truncate-sty-≤ 1 (standard-type (2 + d) T) (s≤s (s≤s z≤n)) ⟩
  < truncate-sty 1 (standard-type (1 + d) T) >sty
    ≈⟨ truncate-standard-sty (suc d) T ⟩
  < SArr SHere S⋆ (SPath (last-path T)) >sty ∎
  where
    open Reasoning sty-setoid
