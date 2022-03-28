module Catt.Tree.Properties where

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
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Relation.Binary hiding (Irrelevant)
open import Relation.Binary.Definitions hiding (Irrelevant)

tree-dim-n-disc : (n : ℕ) → tree-dim (n-disc n) ≡ n
tree-dim-n-disc zero = refl
tree-dim-n-disc (suc n) = cong suc (tree-dim-n-disc n)

record TREE (Xr : ISet) : Set₁ where
  constructor <_>t
  field
    {tree-level} : ℕ
    {tree-n} : ℕ
    tr : Tree Xr tree-level tree-n

open TREE public

data TreeEq (_∼_ : ISetRel Xr) : ∀ {l} {l′} → Tree Xr l n → Tree Xr l′ m → Set where
  Sing≃ : ∀ {x : Xr l} {y : Xr l′} → x ∼ y → TreeEq _∼_ (Sing x) (Sing y)
  Join≃ : ∀ {x : Xr l} {y : Xr l′} → x ∼ y → {S : Tree Xr l n} → {S′ : Tree Xr l′ n′} → {T : Tree Xr l m} → {T′ : Tree Xr l′ m′} → TreeEq _∼_ S S′ → TreeEq _∼_ T T′ → TreeEq _∼_ (Join x S T) (Join y S′ T′)

_≃⊤_ : Tree Xr l n → Tree Xr l′ m → Set
_≃⊤_ {Xr = Xr} = TreeEq (FullISetRel Xr)

reflTree : {_∼_ : ISetRel Xr} → ISRRefl {Xr} _∼_ → {T : Tree Xr l n} → TreeEq _∼_ T T
reflTree p {Sing l} = Sing≃ p
reflTree p {Join l S T} = Join≃ p (reflTree p) (reflTree p)

refl≃⊤ : T ≃⊤ T
refl≃⊤ {Xr} = reflTree tt

symTree : {_∼_ : ISetRel Xr} → ISRSym {Xr} _∼_ → {S : Tree Xr l n} → {T : Tree Xr l′ m} → TreeEq _∼_ S T → TreeEq _∼_ T S
symTree p (Sing≃ x) = Sing≃ (p x)
symTree p (Join≃ x q r) = Join≃ (p x) (symTree p q) (symTree p r)

sym≃⊤ : S ≃⊤ T → T ≃⊤ S
sym≃⊤ = symTree λ _ → tt

transTree : {_∼_ : ISetRel Xr} → ISRTrans {Xr} _∼_ → {S : Tree Xr l n} → {T : Tree Xr l′ m} → {U : Tree Xr l″ o} → TreeEq _∼_ S T → TreeEq _∼_ T U → TreeEq _∼_ S U
transTree p (Sing≃ x) (Sing≃ y) = Sing≃ (p x y)
transTree p (Join≃ x q q′) (Join≃ y r r′) = Join≃ (p x y) (transTree p q r) (transTree p q′ r′)

trans≃⊤ : S ≃⊤ T → T ≃⊤ U → S ≃⊤ U
trans≃⊤ = transTree λ _ _ → tt

tree-setoid-⊤ : Setoid _ _
tree-setoid-⊤ = record { Carrier = TREE ⊤ISet
                     ; _≈_ = λ x y → tr x ≃⊤ tr y
                     ; isEquivalence = record { refl = refl≃⊤
                                              ; sym = sym≃⊤
                                              ; trans = trans≃⊤
                                              }
                     }

module _ {Xr : ISet} {_∼_ : ISetRel Xr} where

  ≃-to-same-n : TreeEq {Xr = Xr} _∼_ S T → tree-size S ≡ tree-size T
  ≃-to-same-n (Sing≃ _) = refl
  ≃-to-same-n (Join≃ _ p q) = cong₂ (λ a b → (a + suc (suc b))) (≃-to-same-n q) (≃-to-same-n p)

  susp-tree-≃ : {_∼_ : Rel X 0ℓ} {x y x′ y′ : X} → x ∼ x′ → y ∼ y′ → TreeEq _∼_ S T → TreeEq _∼_ (suspTree x y S) (suspTree x′ y′ T)
  susp-tree-≃ p q r = Join≃ p r (Sing≃ q)

  replace-label-≃ : {x : Xr l} {y : Xr l′} → x ∼ y → TreeEq {Xr = Xr} _∼_ S T → TreeEq _∼_ (replace-label x S) (replace-label y T)
  replace-label-≃ p (Sing≃ x) = Sing≃ p
  replace-label-≃ p (Join≃ x q r) = Join≃ p q r

  connect-tree-≃ : TreeEq {Xr = Xr} _∼_ S S′ → TreeEq _∼_ T T′ → TreeEq _∼_ (connect-tree S T) (connect-tree S′ T′)
  connect-tree-≃ (Sing≃ x) q = replace-label-≃ x q
  connect-tree-≃ (Join≃ x p p′) q = Join≃ x p (connect-tree-≃ p′ q)

  tree-dim-≃ : TreeEq {Xr = Xr} _∼_ S T → tree-dim S ≡ tree-dim T
  tree-dim-≃ (Sing≃ x) = refl
  tree-dim-≃ (Join≃ x p q) = cong₂ (λ a b → suc ((pred a) ⊔ b)) (tree-dim-≃ q) (tree-dim-≃ p)

  first-label-≃ : TreeEq {Xr = Xr} _∼_ S T → first-label S ∼ first-label T
  first-label-≃ (Sing≃ x) = x
  first-label-≃ (Join≃ x p q) = x

  first-label-map : (f : Xr l → Xr l′) → (T : Tree Xr l n) → ISRRefl {Xr = Xr} _∼_ → first-label {Xr = Xr} (map-tree f T) ∼ f (first-label T)
  first-label-map f (Sing x) p = p
  first-label-map f (Join x S T) p = p

≃-to-≡ : {S T : Tree⊤ n} → S ≃⊤ T → S ≡ T
≃-to-≡ {S = S} {T = T} q = subst (λ - → subst Tree⊤ - S ≡ T) (≡-irrelevant (≃-to-same-n q) refl) (γ q)
  where
    subst-Tree : (p : n ≡ n′) → (q : m ≡ m′) → (S : Tree⊤ n) → (T : Tree⊤ m) → subst Tree⊤ (cong₂ (λ a b → (a + suc (suc b))) q p) (Join _ S T) ≡ Join _ (subst Tree⊤ p S) (subst Tree⊤ q T)
    subst-Tree refl refl S T = refl
    γ : {S : Tree⊤ n} → {T : Tree⊤ m} → (p : S ≃⊤ T) → subst Tree⊤ (≃-to-same-n p) S ≡ T
    γ (Sing≃ _) = refl
    γ (Join≃ _ q r) = trans (subst-Tree (≃-to-same-n q) (≃-to-same-n r) _ _) (cong₂ (Join _) (γ q) (γ r))

≃-dec : (S : Tree⊤ n) → (T : Tree⊤ m) → Dec (S ≃⊤ T)
≃-dec Sing⊤ Sing⊤ = yes refl≃⊤
≃-dec Sing⊤ (Join⊤ S T) = no λ ()
≃-dec (Join⊤ S T) Sing⊤ = no λ ()
≃-dec (Join⊤ S T) (Join⊤ S′ T′) with ≃-dec S S′ | ≃-dec T T′
... | yes p | yes q = yes (Join≃ tt p q)
... | yes p | no q = no λ where (Join≃ _ x y) → q y
... | no p | q = no λ where (Join≃ _ x y) → p x

≃-irrel : Irrelevant (S ≃⊤ T)
≃-irrel (Sing≃ _) (Sing≃ _) = refl
≃-irrel (Join≃ _ p q) (Join≃ _ p′ q′) = cong₂ (Join≃ _) (≃-irrel p p′) (≃-irrel q q′)

tree-to-ctx-replace : (x : Xr l) → (T : Tree Xr l n) → tree-to-ctx (replace-label x T) ≃c tree-to-ctx T
tree-to-ctx-replace x (Sing y) = refl≃c
tree-to-ctx-replace x (Join y S T) = refl≃c

connect-tree-to-ctx : (S : Tree Xr l n) → (T : Tree Xr l m)
                    → tree-to-ctx (connect-tree S T) ≃c connect (tree-to-ctx S) (tree-last-var S) (tree-to-ctx T)

connect-tree-to-ctx (Sing _) T = trans≃c (tree-to-ctx-replace _ T) (sym≃c (connect-left-unit (tree-to-ctx T)))
connect-tree-to-ctx (Join x S₁ S₂) T = begin
  < tree-to-ctx (connect-tree (Join x S₁ S₂) T) >c ≡⟨⟩
  < connect-susp (tree-to-ctx S₁) (tree-to-ctx (connect-tree S₂ T)) >c
    ≈⟨ connect-≃ refl≃c refl≃tm (connect-tree-to-ctx S₂ T) ⟩
  < connect-susp (tree-to-ctx S₁) (connect (tree-to-ctx S₂) (tree-last-var S₂) (tree-to-ctx T))
    >c
    ≈˘⟨ connect-susp-assoc (tree-to-ctx S₁) (tree-to-ctx S₂) (tree-last-var S₂) (tree-to-ctx T) ⟩
  < connect (connect-susp (tree-to-ctx S₁) (tree-to-ctx S₂))
            (tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
            (tree-to-ctx T) >c ∎
  where
    open Reasoning ctx-setoid

tree-to-ctx-≃ : {_∼_ : Rel X 0ℓ} → TreeEq _∼_ S T → tree-to-ctx S ≃c tree-to-ctx T
tree-to-ctx-≃ (Sing≃ _) = refl≃c
tree-to-ctx-≃ (Join≃ _ p q) = connect-susp-≃ (tree-to-ctx-≃ p) (tree-to-ctx-≃ q)

tree-last-var-is-var : (T : Tree Xr l n) → isVar (tree-last-var T)
tree-last-var-is-var (Sing _) = tt
tree-last-var-is-var (Join _ S T) = var-to-var-comp-tm (tree-last-var T) ⦃ tree-last-var-is-var T ⦄ (connect-susp-inc-right (tree-size S) (tree-size T)) ⦃ connect-susp-inc-right-var-to-var (tree-size S) (tree-size T) ⦄

tree-inc-preserve-fst-var : (d : ℕ) → (T : Tree⊤ n) → (b : Bool) → Var (fromℕ _) [ tree-inc (suc d) T b ]tm ≃tm Var {suc (tree-size T)} (fromℕ _)
tree-inc-preserve-fst-var d Sing⊤ b = refl≃tm
tree-inc-preserve-fst-var d (Join⊤ S T) b = sub-between-connect-susps-fst-var (tree-inc d S b) (tree-inc (suc d) T b)

tree-inc-preserve-last-var : (d : ℕ) → (T : Tree⊤ n) → (b : Bool) → tree-last-var (tree-bd (suc d) T) [ tree-inc (suc d) T b ]tm ≃tm tree-last-var T
tree-inc-preserve-last-var d Sing⊤ b = refl≃tm
tree-inc-preserve-last-var d (Join⊤ S T) b = begin
  < tree-last-var (tree-bd (suc d) T)
    [ connect-susp-inc-right (tree-bd-len d S) (tree-bd-len (suc d) T) ]tm
    [ sub-between-connect-susps (tree-inc d S b)
                                (tree-inc (suc d) T b) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (tree-last-var (tree-bd (suc d) T)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ sub-between-connect-susps (tree-inc d S b)
                                (tree-inc (suc d) T b)
      ∘ connect-susp-inc-right (tree-bd-len d S) (tree-bd-len (suc d) T) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var (tree-bd (suc d) T)})
       (sub-between-connect-susps-inc-right (tree-inc d S b)
                                            (tree-inc (suc d) T b)
                                            (tree-inc-preserve-fst-var d T b)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ connect-susp-inc-right (tree-size S) (tree-size T) ∘ tree-inc (suc d) T b ]tm >tm
    ≈⟨ assoc-tm _ _ (tree-last-var (tree-bd (suc d) T)) ⟩
  < tree-last-var (tree-bd (suc d) T)
    [ tree-inc (suc d) T b ]tm
    [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm
    ≈⟨ sub-action-≃-tm (tree-inc-preserve-last-var d T b) refl≃s ⟩
  < tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm >tm ∎
  where
    open Reasoning tm-setoid

tree-bd-glob : (d₁ d₂ : ℕ) → (T : Tree⊤ n) → d₁ < d₂ → tree-bd d₁ (tree-bd d₂ T) ≃⊤ tree-bd d₁ T
tree-bd-glob zero d₂ T p = Sing≃ tt
tree-bd-glob (suc d₁) (suc d₂) (Sing _) p = Sing≃ tt
tree-bd-glob (suc d₁) (suc d₂) (Join _ S T) p = Join≃ tt (tree-bd-glob d₁ d₂ S (≤-pred p)) (tree-bd-glob (suc d₁) (suc d₂) T p)

tree-bd-full : (d : ℕ) → (T : Tree⊤ n) → (tree-dim T ≤ d) → tree-bd d T ≃⊤ T
tree-bd-full zero Sing⊤ p = Sing≃ tt
tree-bd-full zero (Join⊤ S T) ()
tree-bd-full (suc d) Sing⊤ p = Sing≃ tt
tree-bd-full (suc d) (Join⊤ S T) p = Join≃ tt (tree-bd-full d S (≤-trans (m≤n⊔m (pred (tree-dim T)) (tree-dim S)) (≤-pred p))) (tree-bd-full (suc d) T (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p))

tree-inc-glob : (d₁ d₂ : ℕ) → (T : Tree⊤ n) → (b₁ b₂ : Bool) → d₁ < d₂ → tree-inc d₂ T b₂ ∘ tree-inc d₁ (tree-bd d₂ T) b₁ ≃s tree-inc d₁ T b₁
tree-inc-glob zero (suc d₂) T false b₂ p = Ext≃ refl≃s (tree-inc-preserve-fst-var d₂ T b₂)
tree-inc-glob zero (suc d₂) T true b₂ p = Ext≃ refl≃s (tree-inc-preserve-last-var d₂ T b₂)
tree-inc-glob (suc d₁) (suc d₂) Sing⊤ b₁ b₂ p = refl≃s
tree-inc-glob (suc d₁) (suc d₂) (Join⊤ S T) b₁ b₂ p = begin
  < sub-between-connect-susps (tree-inc d₂ S b₂) (tree-inc (suc d₂) T b₂)
    ∘ sub-between-connect-susps (tree-inc d₁ (tree-bd d₂ S) b₁) (tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁) >s
    ≈⟨ sub-between-connect-susps-comp (tree-inc d₁ (tree-bd d₂ S) b₁) (tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁) (tree-inc d₂ S b₂) (tree-inc (suc d₂) T b₂) (tree-inc-preserve-fst-var d₂ T b₂) ⟩
  < sub-between-connect-susps
    (tree-inc d₂ S b₂ ∘ tree-inc d₁ (tree-bd d₂ S) b₁)
    (tree-inc (suc d₂) T b₂ ∘ tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁)
    >s
    ≈⟨ sub-between-connect-susps-≃ (tree-inc d₂ S b₂ ∘ tree-inc d₁ (tree-bd d₂ S) b₁)
                                   (tree-inc d₁ S b₁)
                                   (tree-inc (suc d₂) T b₂ ∘ tree-inc (suc d₁) (tree-bd (suc d₂) T) b₁)
                                   (tree-inc (suc d₁) T b₁)
                                   (≃-to-same-n (tree-bd-glob d₁ d₂ S (≤-pred p)))
                                   (≃-to-same-n (tree-bd-glob (suc d₁) (suc d₂) T p))
                                   (tree-inc-glob d₁ d₂ S b₁ b₂ (≤-pred p))
                                   (tree-inc-glob (suc d₁) (suc d₂) T b₁ b₂ p) ⟩
  < sub-between-connect-susps (tree-inc d₁ S b₁)
      (tree-inc (suc d₁) T b₁) >s ∎
  where
    open Reasoning sub-setoid

tree-inc-full : (d : ℕ) → (T : Tree⊤ n) → (b : Bool) → (p : tree-dim T ≤ d) → tree-inc d T b ≃s idSub {suc (tree-size T)}
tree-inc-full zero Sing⊤ false p = refl≃s
tree-inc-full zero Sing⊤ true p = refl≃s
tree-inc-full zero (Join⊤ S T) b ()
tree-inc-full (suc d) Sing⊤ b p = refl≃s
tree-inc-full (suc d) (Join⊤ S T) b p = begin
  < sub-between-connect-susps (tree-inc d S b) (tree-inc (suc d) T b) >s
    ≈⟨ sub-between-connect-susps-≃ (tree-inc d S b) idSub (tree-inc (suc d) T b) idSub (≃-to-same-n (tree-bd-full d S (m⊔n≤o⇒n≤o (pred (tree-dim T)) (tree-dim S) (≤-pred p)))) (≃-to-same-n (tree-bd-full (suc d) T (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p))) (tree-inc-full d S b (m⊔n≤o⇒n≤o (pred (tree-dim T)) (tree-dim S) (≤-pred p))) (tree-inc-full (suc d) T b (≤-trans (≤-trans (suc-pred-≤ (tree-dim T)) (s≤s (m≤m⊔n (pred (tree-dim T)) (tree-dim S)))) p)) ⟩
  < sub-between-connect-susps idSub idSub >s
    ≈⟨ sub-between-connect-susps-id _ _ ⟩
  < idSub >s ∎
  where
    open Reasoning sub-setoid

tree-inc-glob-step : (d : ℕ) → (T : Tree⊤ n) (b₁ b₂ : Bool) → tree-inc (suc d) T b₁ ∘ tree-inc d (tree-bd (suc d) T) b₂ ≃s tree-inc (suc d) T (not b₁) ∘ tree-inc d (tree-bd (suc d) T) b₂
tree-inc-glob-step d T b₁ b₂ = begin
  < tree-inc (suc d) T b₁ ∘ tree-inc d (tree-bd (suc d) T) b₂ >s
    ≈⟨ tree-inc-glob d (suc d) T b₂ b₁ (s≤s ≤-refl) ⟩
  < tree-inc d T b₂ >s
    ≈˘⟨ tree-inc-glob d (suc d) T b₂ (not b₁) (s≤s ≤-refl)  ⟩
  < tree-inc (suc d) T (not b₁) ∘ tree-inc d (tree-bd (suc d) T) b₂
    >s ∎
  where
    open Reasoning sub-setoid

tree-dim-bd : (d : ℕ) → (T : Tree⊤ n) → tree-dim (tree-bd d T) ≡ d ⊓ tree-dim T
tree-dim-bd zero T = refl
tree-dim-bd (suc d) Sing⊤ = refl
tree-dim-bd (suc d) (Join⊤ S T) = cong suc (begin
  pred (tree-dim (tree-bd (suc d) T)) ⊔ tree-dim (tree-bd d S)
    ≡⟨ cong₂ (λ a → (pred a) ⊔_) (tree-dim-bd (suc d) T) (tree-dim-bd d S) ⟩
  pred (suc d ⊓ tree-dim T) ⊔ (d ⊓ tree-dim S)
    ≡⟨ cong (_⊔ (d ⊓ tree-dim S)) (∸-distribʳ-⊓ 1 (suc d) (tree-dim T)) ⟩
  (d ⊓ pred (tree-dim T)) ⊔ (d ⊓ tree-dim S)
    ≡˘⟨ ⊓-distribˡ-⊔ d (pred (tree-dim T)) (tree-dim S) ⟩
  d ⊓ (pred (tree-dim T) ⊔ tree-dim S) ∎)
  where
    open ≡-Reasoning

tree-dim-bd′ : (d : ℕ) → (T : Tree⊤ n) → d ≤ tree-dim T → tree-dim (tree-bd d T) ≡ d
tree-dim-bd′ d T p = trans (tree-dim-bd d T) (m≤n⇒m⊓n≡m p)

tree-inc-susp-lem : (d : ℕ) → (T : Tree⊤ n) → (b : Bool) → suspSub (tree-inc d T b) ≃s tree-inc (suc d) (suspTree⊤ T) b
tree-inc-susp-lem zero T false = sym≃s (id-left-unit ⟨ ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩ , suspTm (Var (fromℕ _)) ⟩)
tree-inc-susp-lem zero T true = sym≃s (id-left-unit ⟨ ⟨ ⟨ ⟨⟩ , getFst ⟩ , getSnd ⟩ , suspTm (tree-last-var T) ⟩)
tree-inc-susp-lem (suc d) Sing⊤ b = refl≃s
tree-inc-susp-lem (suc d) (Join⊤ S T) b = sym≃s (id-left-unit _)

linear-tree-dim : (S : Tree Xr l n) → .⦃ is-linear S ⦄ → tm-height (tree-to-ctx S) 0V ≡ tree-dim S
linear-tree-dim (Sing _) = refl
linear-tree-dim (Join _ S (Sing _)) = begin
  tm-height (suspCtx (tree-to-ctx S)) 0V
    ≡⟨ susp-tm-height 0V (tree-to-ctx S) ⟩
  suc (tm-height (tree-to-ctx S) 0V)
    ≡⟨ cong suc (linear-tree-dim S) ⟩
  suc (tree-dim S) ∎
  where
    open ≡-Reasoning

tree-dim-replace : (x : Xr l) → (T : Tree Xr l n) → tree-dim (replace-label x T) ≡ tree-dim T
tree-dim-replace x (Sing y) = refl
tree-dim-replace x (Join y S T) = refl

connect-tree-dim : (S : Tree Xr l n) → (T : Tree Xr l m) → tree-dim (connect-tree S T) ≡ tree-dim S ⊔ tree-dim T
connect-tree-dim (Sing _) T = tree-dim-replace _ T
connect-tree-dim (Join _ S₁ S₂) T = begin
  suc (pred (tree-dim (connect-tree S₂ T)) ⊔ tree-dim S₁)
    ≡˘⟨ ⊔-lem (tree-dim S₁) (tree-dim (connect-tree S₂ T)) ⟩
  suc (tree-dim S₁) ⊔ tree-dim (connect-tree S₂ T)
    ≡⟨ cong (suc (tree-dim S₁) ⊔_) (connect-tree-dim S₂ T) ⟩
  suc (tree-dim S₁) ⊔ (tree-dim S₂ ⊔ tree-dim T)
    ≡˘⟨ ⊔-assoc (suc (tree-dim S₁)) (tree-dim S₂) (tree-dim T) ⟩
  suc (tree-dim S₁) ⊔ tree-dim S₂ ⊔ tree-dim T
    ≡⟨ cong (_⊔ tree-dim T) (⊔-lem (tree-dim S₁) (tree-dim S₂)) ⟩
  suc (pred (tree-dim S₂) ⊔ tree-dim S₁) ⊔ tree-dim T ∎
  where
    open ≡-Reasoning

connect-tree-length-lem : (S : Tree Xr l n) → (T : Tree Xr l m) → connect-tree-length S T ≡ tree-size T + tree-size S
connect-tree-length-lem (Sing _) T = sym (+-identityʳ _)
connect-tree-length-lem (Join _ S₁ S₂) T = trans (cong (_+ (2 + tree-size S₁)) (connect-tree-length-lem S₂ T)) (+-assoc (tree-size T) (tree-size S₂) (2 + tree-size S₁))

tree-last-var-replace : (x : Xr l) → (T : Tree Xr l n) → tree-last-var (replace-label x T) ≃tm tree-last-var T
tree-last-var-replace x (Sing y) = refl≃tm
tree-last-var-replace x (Join y S T) = refl≃tm

connect-tree-last-var : (S : Tree Xr l n) → (T : Tree Xr l m) → tree-last-var (connect-tree S T) ≃tm tree-last-var T [ idSub≃ (sym≃c (connect-tree-to-ctx S T)) ∘ (connect-inc-right (tree-last-var S) (tree-size T)) ]tm
connect-tree-last-var {Xr = Xr} (Sing x) T = begin
  < tree-last-var (replace-label x T) >tm
    ≈⟨ tree-last-var-replace x T ⟩
  < tree-last-var T >tm
    ≈˘⟨ id-on-tm (tree-last-var T) ⟩
  < tree-last-var T [ idSub ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var T}) lem ⟩
  <
    tree-last-var T
    [ idSub≃ (sym≃c (connect-tree-to-ctx (Sing x) T))
    ∘ connect-inc-right (tree-last-var (Sing {Xr = Xr} x)) (tree-size T) ]tm >tm ∎
  where
    lem : idSub≃ (sym≃c (trans≃c (tree-to-ctx-replace x T) (sym≃c (connect-left-unit (tree-to-ctx T))))) ∘ connect-inc-right (Var zero) (tree-size T) ≃s idSub {suc (tree-size T)}
    lem = begin
      < idSub≃ (sym≃c (trans≃c (tree-to-ctx-replace x T) (sym≃c (connect-left-unit (tree-to-ctx T)))))
        ∘ connect-inc-right (Var zero) (tree-size T) >s
        ≈⟨ idSub≃-on-sub (sym≃c (trans≃c (tree-to-ctx-replace x T) (sym≃c (connect-left-unit (tree-to-ctx T))))) (connect-inc-right (Var zero) _) ⟩
      < connect-inc-right (Var zero) _ >s
        ≈⟨ connect-inc-right-left-unit ⟩
      < idSub >s ∎
      where
        open Reasoning sub-setoid
    open Reasoning tm-setoid
connect-tree-last-var (Join x S₁ S₂) T = begin
  < tree-last-var (connect-tree S₂ T) [
       connect-susp-inc-right (tree-size S₁)
       (tree-size (connect-tree S₂ T))
       ]tm >tm
    ≈⟨ sub-action-≃-tm (connect-tree-last-var S₂ T) refl≃s ⟩
  < tree-last-var T
    [ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T))
      ∘ connect-inc-right (tree-last-var S₂) (tree-size T) ]tm
    [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (tree-last-var T) ⟩
  < tree-last-var T
    [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
    ∘ (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ∘
      connect-inc-right (tree-last-var S₂) (tree-size T)) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var T}) lem ⟩
  < tree-last-var T
    [ idSub≃ (sym≃c (connect-tree-to-ctx (Join x S₁ S₂) T))
      ∘ connect-inc-right (tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm) (tree-size T) ]tm >tm ∎
  where
    l2 : (connect-susp-inc-right (tree-size S₁)
            (tree-size (connect-tree S₂ T))
            ∘ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)))
           ≃s connect-inc-right getSnd (tree-size T + tree-size S₂)
    l2 = begin
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ∘ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) >s
        ≈⟨ idSub≃-right-unit (sym≃c (connect-tree-to-ctx S₂ T)) (connect-susp-inc-right (tree-size S₁)
                                                                  (tree-size (connect-tree S₂ T))) ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) >s
        ≈⟨ connect-inc-right-≃ refl refl≃tm (connect-tree-length-lem S₂ T) ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size T + tree-size S₂) >s ∎
      where
        open Reasoning sub-setoid

    lem : (connect-susp-inc-right (tree-size S₁)
             (tree-size (connect-tree S₂ T))
             ∘
             (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ∘
              connect-inc-right (tree-last-var S₂) (tree-size T)))
            ≃s
            (idSub≃ (sym≃c (connect-tree-to-ctx (Join x S₁ S₂) T)) ∘
             connect-inc-right
             (tree-last-var S₂ [
              connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
             (tree-size T))
    lem = begin
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ∘ (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ∘ connect-inc-right (tree-last-var S₂) (tree-size T)) >s
        ≈˘⟨ ∘-assoc _ _ _ ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ∘ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T))
        ∘ connect-inc-right (tree-last-var S₂) (tree-size T) >s
        ≈⟨ sub-action-≃-sub refl≃s l2 ⟩
      < connect-inc-right getSnd (tree-size T + tree-size S₂)
        ∘ connect-inc-right (tree-last-var S₂) (tree-size T) >s
        ≈˘⟨ connect-inc-right-assoc getSnd (tree-last-var S₂) (tree-size T) ⟩
      < connect-inc-right (tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
        (tree-size T) >s
        ≈˘⟨ idSub≃-on-sub (sym≃c (connect-tree-to-ctx (Join x S₁ S₂) T)) _ ⟩
      <
        idSub≃ (sym≃c (connect-tree-to-ctx (Join x S₁ S₂) T)) ∘
        connect-inc-right
        (tree-last-var S₂ [
         connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
        (tree-size T)
        >s ∎
      where
        open Reasoning sub-setoid

    open Reasoning tm-setoid

tree-to-ctx-glob : (S : Tree Xr l n) → ctx-is-globular (tree-to-ctx S)
tree-to-ctx-glob (Sing _) = tt ,, tt
tree-to-ctx-glob (Join _ S T) = connect-susp-glob (tree-to-ctx S) ⦃ tree-to-ctx-glob S ⦄ (tree-to-ctx T) ⦃ tree-to-ctx-glob T ⦄

susp-lin-tree : (S : Tree Xr l n) → .⦃ _ : is-linear S ⦄ → suspCtx (tree-to-ctx S) ≃c tree-to-ctx S , tree-to-ctx S ‼ zero , 1V ─⟨ (liftType (tree-to-ctx S ‼ zero)) ⟩⟶ 0V
susp-lin-tree (Sing _) = refl≃c
susp-lin-tree (Join _ S (Sing _)) = begin
  < suspCtx (suspCtx (tree-to-ctx S)) >c
    ≈⟨ susp-ctx-≃ (susp-lin-tree S) ⟩
  < suspCtx (tree-to-ctx S) , suspTy (tree-to-ctx S ‼ zero) ,
       1V ─⟨ suspTy (liftType (tree-to-ctx S ‼ zero)) ⟩⟶ 0V >c
    ≈˘⟨ Add≃ (Add≃ refl≃c (susp-‼ (tree-to-ctx S) zero)) (Arr≃ refl≃tm (trans≃ty (lift-ty-≃ (susp-‼ (tree-to-ctx S) zero)) (sym≃ty (susp-ty-lift (tree-to-ctx S ‼ zero)))) refl≃tm) ⟩
  < suspCtx (tree-to-ctx S) , suspCtx (tree-to-ctx S) ‼ zero ,
       1V ─⟨ liftType (suspCtx (tree-to-ctx S) ‼ zero) ⟩⟶ 0V >c ∎
  where
    open Reasoning ctx-setoid

n-disc-≃ : n ≡ m → n-disc n ≃⊤ n-disc m
n-disc-≃ refl = refl≃⊤
