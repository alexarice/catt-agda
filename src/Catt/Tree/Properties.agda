module Catt.Tree.Properties where

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
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree

linear-tree-compat : (T : Tree n) → .⦃ _ : is-linear T ⦄ → tree-to-ctx T ≃c Disc (tree-dim T)
linear-tree-compat Sing = Add≃ Emp≃ (Star≃ refl)
linear-tree-compat (Join S Sing) = trans≃c (susp-ctx-≃ (linear-tree-compat S)) (disc-susp (tree-dim S))

linear-non-linear : (T : Tree n)
                  → .⦃ non-linear T ⦄
                  → .⦃ is-linear T ⦄
                  → ⊥
linear-non-linear (Join T Sing) = linear-non-linear T

instance
  tree-dim-n-disc : {n : ℕ} → tree-dim (n-disc n) ≃n n
  tree-dim-n-disc {zero} = tt
  tree-dim-n-disc {suc n} = inst

record TREE : Set where
  constructor <_>t
  field
    {tree-n} : ℕ
    tr : Tree tree-n

open TREE public

data _≃_ : Tree n → Tree m → Set where
  Sing≃ : Sing ≃ Sing
  Join≃ : {S : Tree n} → {S′ : Tree n′} → {T : Tree m} → {T′ : Tree m′} → S ≃ S′ → T ≃ T′ → Join S T ≃ Join S′ T′

refl≃ : T ≃ T
refl≃ {T = Sing} = Sing≃
refl≃ {T = Join S T} = Join≃ refl≃ refl≃

sym≃ : S ≃ T → T ≃ S
sym≃ Sing≃ = Sing≃
sym≃ (Join≃ p q) = Join≃ (sym≃ p) (sym≃ q)

trans≃ : S ≃ T → T ≃ U → S ≃ U
trans≃ Sing≃ Sing≃ = Sing≃
trans≃ (Join≃ p q) (Join≃ p′ q′) = Join≃ (trans≃ p p′) (trans≃ q q′)

tree-setoid : Setoid _ _
tree-setoid = record { Carrier = TREE
                     ; _≈_ = λ x y → tr x ≃ tr y
                     ; isEquivalence = record { refl = refl≃
                                              ; sym = sym≃
                                              ; trans = trans≃
                                              }
                     }

data _≃′_ : Tree n → Tree m → Set where
  Refl≃′ : T ≃′ T
  Join≃′ : {S : Tree n} → {S′ : Tree n′} → {T : Tree m} → {T′ : Tree m′} → S ≃′ S′ → T ≃′ T′ → Join S T ≃′ Join S′ T′

refl≃′ : T ≃′ T
refl≃′ = Refl≃′

sym≃′ : S ≃′ T → T ≃′ S
sym≃′ Refl≃′ = Refl≃′
sym≃′ (Join≃′ p q) = Join≃′ (sym≃′ p) (sym≃′ q)

trans≃′ : S ≃′ T → T ≃′ U → S ≃′ U
trans≃′ Refl≃′ q = q
trans≃′ (Join≃′ p p′) Refl≃′ = Join≃′ p p′
trans≃′ (Join≃′ p p′) (Join≃′ q q′) = Join≃′ (trans≃′ p q) (trans≃′ p′ q′)

tree′-setoid : Setoid _ _
tree′-setoid = record { Carrier = TREE
                     ; _≈_ = λ x y → tr x ≃′ tr y
                     ; isEquivalence = record { refl = refl≃′
                                              ; sym = sym≃′
                                              ; trans = trans≃′
                                              }
                     }

≃′-to-≃ : S ≃′ T → S ≃ T
≃′-to-≃ Refl≃′ = refl≃
≃′-to-≃ (Join≃′ p q) = Join≃ (≃′-to-≃ p) (≃′-to-≃ q)

≃-to-same-n : {S : Tree n} → {T : Tree m} → S ≃ T → n ≡ m
≃-to-same-n Sing≃ = refl
≃-to-same-n (Join≃ p q) = cong₂ (λ a b → (a + suc (suc b))) (≃-to-same-n q) (≃-to-same-n p)

≃-to-≡ : {S T : Tree n} → S ≃ T → S ≡ T
≃-to-≡ {S = S} {T = T} q = subst (λ - → subst Tree - S ≡ T) (≡-irrelevant (≃-to-same-n q) refl) (γ q)
  where
    subst-Tree : (p : n ≡ n′) → (q : m ≡ m′) → (S : Tree n) → (T : Tree m) → subst Tree (cong₂ (λ a b → (a + suc (suc b))) q p) (Join S T) ≡ Join (subst Tree p S) (subst Tree q T)
    subst-Tree refl refl S T = refl
    γ : {S : Tree n} → {T : Tree m} → (p : S ≃ T) → subst Tree (≃-to-same-n p) S ≡ T
    γ Sing≃ = refl
    γ (Join≃ q r) = trans (subst-Tree (≃-to-same-n q) (≃-to-same-n r) _ _) (cong₂ Join (γ q) (γ r))

susp-tree-≃ : S ≃ T → susp-tree S ≃ susp-tree T
susp-tree-≃ p = Join≃ p Sing≃

≃-dec : (S : Tree n) → (T : Tree m) → Dec (S ≃ T)
≃-dec Sing Sing = yes Sing≃
≃-dec Sing (Join S T) = no λ ()
≃-dec (Join S T) Sing = no λ ()
≃-dec (Join S T) (Join S′ T′) with ≃-dec S S′ | ≃-dec T T′
... | yes p | yes q = yes (Join≃ p q)
... | yes p | no q = no λ where (Join≃ x y) → q y
... | no p | q = no λ where (Join≃ x y) → p x

≃-irrel : Irrelevant (S ≃ T)
≃-irrel Sing≃ Sing≃ = refl
≃-irrel (Join≃ p q) (Join≃ p′ q′) = cong₂ Join≃ (≃-irrel p p′) (≃-irrel q q′)

connect-tree-≃ : S ≃ S′ → T ≃ T′ → connect-tree S T ≃ connect-tree S′ T′
connect-tree-≃ Sing≃ q = q
connect-tree-≃ (Join≃ p p′) q = Join≃ p (connect-tree-≃ p′ q)

connect-tree-to-ctx : (S : Tree n) → (T : Tree m)
                    → tree-to-ctx (connect-tree S T) ≃c connect (tree-to-ctx S) (tree-last-var S) (tree-to-ctx T)

connect-tree-to-ctx Sing T = sym≃c (connect-left-unit (tree-to-ctx T))
connect-tree-to-ctx (Join S₁ S₂) T = begin
  < tree-to-ctx (connect-tree (Join S₁ S₂) T) >c ≡⟨⟩
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

tree-to-ctx-≃ : S ≃ T → tree-to-ctx S ≃c tree-to-ctx T
tree-to-ctx-≃ Sing≃ = refl≃c
tree-to-ctx-≃ (Join≃ p q) = connect-susp-≃ (tree-to-ctx-≃ p) (tree-to-ctx-≃ q)

tree-last-var-is-var : (T : Tree n) → isVar (tree-last-var T)
tree-last-var-is-var Sing = tt
tree-last-var-is-var (Join S T) = var-to-var-comp-tm (tree-last-var T) ⦃ tree-last-var-is-var T ⦄ (connect-susp-inc-right (tree-size S) (tree-size T)) ⦃ connect-susp-inc-right-var-to-var (tree-size S) (tree-size T) ⦄



linear-tree-dim : (S : Tree n) → .⦃ is-linear S ⦄ → tm-height (tree-to-ctx S) 0V ≡ tree-dim S
linear-tree-dim Sing = refl
linear-tree-dim (Join S Sing) = begin
  tm-height (susp-ctx (tree-to-ctx S)) 0V
    ≡⟨ susp-tm-height 0V (tree-to-ctx S) ⟩
  suc (tm-height (tree-to-ctx S) 0V)
    ≡⟨ cong suc (linear-tree-dim S) ⟩
  suc (tree-dim S) ∎
  where
    open ≡-Reasoning

connect-tree-dim : (S : Tree n) → (T : Tree m) → tree-dim (connect-tree S T) ≡ tree-dim S ⊔ tree-dim T
connect-tree-dim Sing T = refl
connect-tree-dim (Join S₁ S₂) T = begin
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

connect-tree-length-lem : (S : Tree n) → (T : Tree m) → connect-tree-length S T ≡ tree-size T + tree-size S
connect-tree-length-lem Sing T = sym (+-identityʳ _)
connect-tree-length-lem (Join S₁ S₂) T = trans (cong (_+ (2 + tree-size S₁)) (connect-tree-length-lem S₂ T)) (+-assoc (tree-size T) (tree-size S₂) (2 + tree-size S₁))

connect-tree-last-var : (S : Tree n) → (T : Tree m) → tree-last-var (connect-tree S T) ≃tm tree-last-var T [ idSub≃ (sym≃c (connect-tree-to-ctx S T)) ● (connect-inc-right (tree-last-var S) (tree-size T)) ]tm
connect-tree-last-var Sing T = sym≃tm (trans≃tm (sub-action-≃-tm (refl≃tm {s = tree-last-var T}) lem) (id-on-tm (tree-last-var (connect-tree Sing T))))
  where
    lem : idSub≃ (sym≃c (sym≃c (connect-left-unit (tree-to-ctx T)))) ● connect-inc-right (Var zero) (tree-size T) ≃s idSub {suc (tree-size T)}
    lem = begin
      < idSub≃ (sym≃c (sym≃c (connect-left-unit (tree-to-ctx T))))
        ● connect-inc-right (Var zero) (tree-size T) >s
        ≈⟨ idSub≃-on-sub (sym≃c (sym≃c (connect-left-unit (tree-to-ctx T)))) (connect-inc-right (Var zero) _) ⟩
      < connect-inc-right (Var zero) _ >s
        ≈⟨ connect-inc-right-left-unit ⟩
      < idSub >s ∎
      where
        open Reasoning sub-setoid
connect-tree-last-var (Join S₁ S₂) T = begin
  < tree-last-var (connect-tree S₂ T) [
       connect-susp-inc-right (tree-size S₁)
       (tree-size (connect-tree S₂ T))
       ]tm >tm
    ≈⟨ sub-action-≃-tm (connect-tree-last-var S₂ T) refl≃s ⟩
  < tree-last-var T
    [ idSub≃ (sym≃c (connect-tree-to-ctx S₂ T))
      ● connect-inc-right (tree-last-var S₂) (tree-size T) ]tm
    [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (tree-last-var T) ⟩
  < tree-last-var T
    [ connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
    ● (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ●
      connect-inc-right (tree-last-var S₂) (tree-size T)) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = tree-last-var T}) lem ⟩
  < tree-last-var T
    [ idSub≃ (sym≃c (connect-tree-to-ctx (Join S₁ S₂) T))
      ● connect-inc-right (tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm) (tree-size T) ]tm >tm ∎
  where
    l2 : (connect-susp-inc-right (tree-size S₁)
            (tree-size (connect-tree S₂ T))
            ● idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)))
           ≃s connect-inc-right get-snd (tree-size T + tree-size S₂)
    l2 = begin
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ● idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) >s
        ≈⟨ idSub≃-right-unit (sym≃c (connect-tree-to-ctx S₂ T)) (connect-susp-inc-right (tree-size S₁)
                                                                  (tree-size (connect-tree S₂ T))) ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T)) >s
        ≈⟨ connect-inc-right-≃ refl refl≃tm (connect-tree-length-lem S₂ T) ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size T + tree-size S₂) >s ∎
      where
        open Reasoning sub-setoid

    lem : (connect-susp-inc-right (tree-size S₁)
             (tree-size (connect-tree S₂ T))
             ●
             (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ●
              connect-inc-right (tree-last-var S₂) (tree-size T)))
            ≃s
            (idSub≃ (sym≃c (connect-tree-to-ctx (Join S₁ S₂) T)) ●
             connect-inc-right
             (tree-last-var S₂ [
              connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
             (tree-size T))
    lem = begin
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ● (idSub≃ (sym≃c (connect-tree-to-ctx S₂ T)) ● connect-inc-right (tree-last-var S₂) (tree-size T)) >s
        ≈˘⟨ ●-assoc _ _ _ ⟩
      < connect-susp-inc-right (tree-size S₁) (tree-size (connect-tree S₂ T))
        ● idSub≃ (sym≃c (connect-tree-to-ctx S₂ T))
        ● connect-inc-right (tree-last-var S₂) (tree-size T) >s
        ≈⟨ sub-action-≃-sub refl≃s l2 ⟩
      < connect-inc-right get-snd (tree-size T + tree-size S₂)
        ● connect-inc-right (tree-last-var S₂) (tree-size T) >s
        ≈˘⟨ connect-inc-right-assoc get-snd (tree-last-var S₂) (tree-size T) ⟩
      < connect-inc-right (tree-last-var S₂ [ connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
        (tree-size T) >s
        ≈˘⟨ idSub≃-on-sub (sym≃c (connect-tree-to-ctx (Join S₁ S₂) T)) _ ⟩
      <
        idSub≃ (sym≃c (connect-tree-to-ctx (Join S₁ S₂) T)) ●
        connect-inc-right
        (tree-last-var S₂ [
         connect-susp-inc-right (tree-size S₁) (tree-size S₂) ]tm)
        (tree-size T)
        >s ∎
      where
        open Reasoning sub-setoid

    open Reasoning tm-setoid

connect-tree-right-unit : (S : Tree n)
                        → connect-tree S Sing ≃′ S
connect-tree-right-unit Sing = Refl≃′
connect-tree-right-unit (Join S T) = Join≃′ Refl≃′ (connect-tree-right-unit T)

tree-to-ctx-glob : (S : Tree n) → ctx-is-globular (tree-to-ctx S)
tree-to-ctx-glob Sing = tt ,, tt
tree-to-ctx-glob (Join S T) = connect-susp-glob (tree-to-ctx S) ⦃ tree-to-ctx-glob S ⦄ (tree-to-ctx T) ⦃ tree-to-ctx-glob T ⦄

susp-lin-tree : (S : Tree n) → .⦃ _ : is-linear S ⦄ → susp-ctx (tree-to-ctx S) ≃c tree-to-ctx S , tree-to-ctx S ‼ zero , 1V ─⟨ (lift-ty (tree-to-ctx S ‼ zero)) ⟩⟶ 0V
susp-lin-tree Sing = refl≃c
susp-lin-tree (Join S Sing) = begin
  < susp-ctx (susp-ctx (tree-to-ctx S)) >c
    ≈⟨ susp-ctx-≃ (susp-lin-tree S) ⟩
  < susp-ctx (tree-to-ctx S) , susp-ty (tree-to-ctx S ‼ zero) ,
       1V ─⟨ susp-ty (lift-ty (tree-to-ctx S ‼ zero)) ⟩⟶ 0V >c
    ≈˘⟨ Add≃ (Add≃ refl≃c (susp-‼ (tree-to-ctx S) zero)) (Arr≃ refl≃tm (trans≃ty (lift-ty-≃ (susp-‼ (tree-to-ctx S) zero)) (sym≃ty (susp-ty-lift (tree-to-ctx S ‼ zero)))) refl≃tm) ⟩
  < susp-ctx (tree-to-ctx S) , susp-ctx (tree-to-ctx S) ‼ zero ,
       1V ─⟨ lift-ty (susp-ctx (tree-to-ctx S) ‼ zero) ⟩⟶ 0V >c ∎
  where
    open Reasoning ctx-setoid

n-disc-≃ : n ≡ m → n-disc n ≃ n-disc m
n-disc-≃ refl = refl≃

tree-dim-≃ : S ≃ T → tree-dim S ≡ tree-dim T
tree-dim-≃ p with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = refl

linear-linear-height : (T : Tree n) → .⦃ is-linear T ⦄ → linear-height T ≡ tree-dim T
linear-linear-height Sing = refl
linear-linear-height (Join T Sing) = cong suc (linear-linear-height T)

linear-height-dim : (T : Tree n) → linear-height T ≤ tree-dim T
linear-height-dim Sing = z≤n
linear-height-dim (Join T Sing) = s≤s (linear-height-dim T)
linear-height-dim (Join T (Join T₁ T₂)) = z≤n

linear-tree-unique : (S : Tree n) → .⦃ is-linear S ⦄
                   → (T : Tree m) → .⦃ is-linear T ⦄
                   → .(tree-dim S ≡ tree-dim T)
                   → S ≃′ T
linear-tree-unique Sing Sing p = refl≃′
linear-tree-unique (Join S Sing) (Join T Sing) p = Join≃′ (linear-tree-unique S T (cong pred p)) refl≃′

linear-tree-compat-2 : (S : Tree n) → .⦃ _ : is-linear S ⦄ → .⦃ _ : tree-dim S ≃n m ⦄ → S ≃′ n-disc m
linear-tree-compat-2 {m = zero} Sing = Refl≃′
linear-tree-compat-2 {m = suc m} (Join S Sing) = Join≃′ (linear-tree-compat-2 S) Refl≃′

connect-tree-assoc : (S : Tree n)
                   → (T : Tree m)
                   → (U : Tree l)
                   → connect-tree S (connect-tree T U) ≃′ connect-tree (connect-tree S T) U
connect-tree-assoc Sing T U = refl≃′
connect-tree-assoc (Join S₁ S₂) T U = Join≃′ refl≃′ (connect-tree-assoc S₂ T U)

susp-tree-n-linear : (n : ℕ)
                   → (S : Tree m)
                   → ⦃ is-linear S ⦄
                   → is-linear (susp-tree-n n S)
susp-tree-n-linear zero S = it
susp-tree-n-linear (suc n) S = inst ⦃ susp-tree-n-linear n S ⦄

has-trunk-height-n-disc : (m ≤ n) → has-trunk-height m (n-disc n)
has-trunk-height-n-disc z≤n = tt
has-trunk-height-n-disc (s≤s p) = inst ⦃ has-trunk-height-n-disc p ⦄
