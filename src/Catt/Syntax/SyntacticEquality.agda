{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax.SyntacticEquality where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc;toℕ;inject₁;fromℕ)
open import Data.Fin.Properties using (toℕ-injective;toℕ-inject₁)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (Irrelevant)
open import Function.Equivalence using (equivalence)
open import Data.Empty
open import Catt.Suspension
import Relation.Binary.Reasoning.Setoid as Reasoning

no-term-in-empty-context : ¬ Tm 0
no-term-in-empty-context (Coh S A ⟨ σ , t ⟩) = no-term-in-empty-context t

n-to-0-sub-impossible : ¬ (Sub (suc n) 0 A)
n-to-0-sub-impossible ⟨ μ , t ⟩ = no-term-in-empty-context t

data _≃_ : Tree n → Tree m → Set where
  Sing≃ : Sing ≃ Sing
  Join≃ : {S : Tree n} → {S′ : Tree n′} → {T : Tree m} → {T′ : Tree m′} → S ≃ S′ → T ≃ T′ → Join S T ≃ Join S′ T′

data _≃c_ : Ctx n → Ctx m → Set
data _≃ty_ : Ty n → Ty m → Set
data _≃tm_ : Tm n → Tm m → Set
data _≃s_ : Sub n m A → Sub n′ m′ B → Set

data _≃c_ where
  Emp≃ : ∅ ≃c ∅
  Add≃ : Γ ≃c Γ′ → A ≃ty A′ → (Γ , A) ≃c (Γ′ , A′)

data _≃ty_ where
  Star≃ : n ≡ m → ⋆ {n = n} ≃ty ⋆ {n = m}
  Arr≃ : s ≃tm s′ → A ≃ty A′ → t ≃tm t′ → s ─⟨ A ⟩⟶ t ≃ty s′ ─⟨ A′ ⟩⟶ t′

data _≃tm_ where
  Var≃ : {i : Fin n} → {j : Fin m} → n ≡ m → toℕ i ≡ toℕ j → Var i ≃tm Var j
  Coh≃ : {σ : Sub (suc n) m ⋆} → {σ′ : Sub (suc n′) m′ ⋆} → S ≃ S′ → A ≃ty A′ → σ ≃s σ′ → Coh S A σ ≃tm Coh S′ A′ σ′

data _≃s_ where
  Null≃ : A ≃ty B → ⟨⟩ {A = A} ≃s ⟨⟩ {A = B}
  Ext≃ : σ ≃s σ′ → t ≃tm t′ → ⟨ σ , t ⟩ ≃s ⟨ σ′ , t′ ⟩

refl≃ : T ≃ T
refl≃c : Γ ≃c Γ
refl≃ty : A ≃ty A
refl≃tm : s ≃tm s
refl≃s : σ ≃s σ

refl≃ {T = Sing} = Sing≃
refl≃ {T = Join S T} = Join≃ refl≃ refl≃

refl≃c {Γ = ∅} = Emp≃
refl≃c {Γ = Γ , A} = Add≃ refl≃c refl≃ty

refl≃ty {A = ⋆} = Star≃ refl
refl≃ty {A = s ─⟨ A ⟩⟶ t} = Arr≃ refl≃tm refl≃ty refl≃tm

refl≃tm {s = Var i} = Var≃ refl refl
refl≃tm {s = Coh Δ A σ} = Coh≃ refl≃ refl≃ty refl≃s

refl≃s {σ = ⟨⟩} = Null≃ refl≃ty
refl≃s {σ = ⟨ σ , t ⟩} = Ext≃ refl≃s refl≃tm

sym≃ : S ≃ T → T ≃ S
sym≃c : Γ ≃c Δ → Δ ≃c Γ
sym≃ty : A ≃ty B → B ≃ty A
sym≃tm : s ≃tm t → t ≃tm s
sym≃s : σ ≃s τ → τ ≃s σ

sym≃ Sing≃ = Sing≃
sym≃ (Join≃ p q) = Join≃ (sym≃ p) (sym≃ q)

sym≃c Emp≃ = Emp≃
sym≃c (Add≃ p q) = Add≃ (sym≃c p) (sym≃ty q)

sym≃ty (Star≃ x) = Star≃ (sym x)
sym≃ty (Arr≃ p q r) = Arr≃ (sym≃tm p) (sym≃ty q) (sym≃tm r)

sym≃tm (Var≃ x y) = Var≃ (sym x) (sym y)
sym≃tm (Coh≃ p q r) = Coh≃ (sym≃ p) (sym≃ty q) (sym≃s r)

sym≃s (Null≃ x) = Null≃ (sym≃ty x)
sym≃s (Ext≃ p q) = Ext≃ (sym≃s p) (sym≃tm q)

trans≃ : S ≃ T → T ≃ U → S ≃ U
trans≃c : Γ ≃c Δ → Δ ≃c Υ → Γ ≃c Υ
trans≃ty : A ≃ty B → B ≃ty C → A ≃ty C
trans≃tm : s ≃tm t → t ≃tm u → s ≃tm u
trans≃s : σ ≃s τ → τ ≃s μ → σ ≃s μ

trans≃ Sing≃ Sing≃ = Sing≃
trans≃ (Join≃ p q) (Join≃ p′ q′) = Join≃ (trans≃ p p′) (trans≃ q q′)

trans≃c Emp≃ Emp≃ = Emp≃
trans≃c (Add≃ p q) (Add≃ r s) = Add≃ (trans≃c p r) (trans≃ty q s)

trans≃ty (Star≃ x) (Star≃ y) = Star≃ (trans x y)
trans≃ty (Arr≃ p q r) (Arr≃ s t u) = Arr≃ (trans≃tm p s) (trans≃ty q t) (trans≃tm r u)

trans≃tm (Var≃ w x) (Var≃ y z) = Var≃ (trans w y) (trans x z)
trans≃tm (Coh≃ p q r) (Coh≃ s t u) = Coh≃ (trans≃ p s) (trans≃ty q t) (trans≃s r u)

trans≃s (Null≃ x) (Null≃ y) = Null≃ (trans≃ty x y)
trans≃s (Ext≃ p q) (Ext≃ r s) = Ext≃ (trans≃s p r) (trans≃tm q s)

reflexive≃c : Γ ≡ Δ → Γ ≃c Δ
reflexive≃c refl = refl≃c

reflexive≃ty : A ≡ B → A ≃ty B
reflexive≃ty refl = refl≃ty

reflexive≃tm : s ≡ t → s ≃tm t
reflexive≃tm refl = refl≃tm

reflexive≃s : σ ≡ τ → σ ≃s τ
reflexive≃s refl = refl≃s

ctx-setoid : Setoid _ _
ctx-setoid = record { Carrier = CTX
                    ; _≈_ = λ x y → ctx x ≃c ctx y
                    ; isEquivalence = record { refl = refl≃c
                                             ; sym = sym≃c
                                             ; trans = trans≃c
                                             }
                    }

ty-setoid : Setoid _ _
ty-setoid = record { Carrier = TY
                    ; _≈_ = λ x y → ty x ≃ty ty y
                    ; isEquivalence = record { refl = refl≃ty
                                             ; sym = sym≃ty
                                             ; trans = trans≃ty
                                             }
                    }

tm-setoid : Setoid _ _
tm-setoid = record { Carrier = TM
                    ; _≈_ = λ x y → tm x ≃tm tm y
                    ; isEquivalence = record { refl = refl≃tm
                                             ; sym = sym≃tm
                                             ; trans = trans≃tm
                                             }
                    }

sub-setoid : Setoid _ _
sub-setoid = record { Carrier = SUB
                    ; _≈_ = λ x y → sub x ≃s sub y
                    ; isEquivalence = record { refl = refl≃s
                                             ; sym = sym≃s
                                             ; trans = trans≃s
                                             }
                    }

≃ty-preserve-height : {A : Ty n} → {B : Ty m} → A ≃ty B → ty-dim A ≡ ty-dim B
≃ty-preserve-height (Star≃ x) = refl
≃ty-preserve-height (Arr≃ x p x₁) = cong suc (≃ty-preserve-height p)

≃-to-same-n : {S : Tree n} → {T : Tree m} → S ≃ T → n ≡ m
≃-to-same-n Sing≃ = refl
≃-to-same-n (Join≃ p q) = cong₂ (λ a b → (a + suc (suc b))) (≃-to-same-n q) (≃-to-same-n p)

≃c-preserve-length : Γ ≃c Δ → ctxLength Γ ≡ ctxLength Δ
≃c-preserve-length Emp≃ = refl
≃c-preserve-length (Add≃ p x) = cong suc (≃c-preserve-length p)

≃ty-to-same-length : {A : Ty n} → {B : Ty m} → A ≃ty B → n ≡ m
≃ty-to-same-length (Star≃ x) = x
≃ty-to-same-length (Arr≃ x p x₁) = ≃ty-to-same-length p

≃s-to-same-ty : {σ : Sub n m A} → {τ : Sub n′ m′ B} → σ ≃s τ → A ≃ty B
≃s-to-same-ty (Null≃ x) = x
≃s-to-same-ty (Ext≃ p x) = ≃s-to-same-ty p

≃s-to-codomain-≡ : {σ : Sub n m A} → {τ : Sub n′ m′ B} → σ ≃s τ → m ≡ m′
≃s-to-codomain-≡ p = ≃ty-to-same-length (≃s-to-same-ty p)

≃-to-≡ : {S T : Tree n} → S ≃ T → S ≡ T
≃-to-≡ {S = S} {T = T} q = subst (λ - → subst Tree - S ≡ T) (≡-irrelevant (≃-to-same-n q) refl) (γ q)
  where
    subst-Tree : (p : n ≡ n′) → (q : m ≡ m′) → (S : Tree n) → (T : Tree m) → subst Tree (cong₂ (λ a b → (a + suc (suc b))) q p) (Join S T) ≡ Join (subst Tree p S) (subst Tree q T)
    subst-Tree refl refl S T = refl
    γ : {S : Tree n} → {T : Tree m} → (p : S ≃ T) → subst Tree (≃-to-same-n p) S ≡ T
    γ Sing≃ = refl
    γ (Join≃ q r) = trans (subst-Tree (≃-to-same-n q) (≃-to-same-n r) _ _) (cong₂ Join (γ q) (γ r))

≃c-to-≡ : Γ ≃c Δ → Γ ≡ Δ
≃ty-to-≡ : A ≃ty B → A ≡ B
-- ≃ty-to-subst-≡ : {A : Ty n d} → {B : Ty n d′} → A ≃ty B → (p : d ≡ d′) → subst (Ty n) p A ≡ B
≃tm-to-≡ : s ≃tm t → s ≡ t
≃s-to-≡ : σ ≃s τ → σ ≡ τ

≃c-to-≡ Emp≃ = refl
≃c-to-≡ (Add≃ p q)
  rewrite ≃c-to-≡ p
  rewrite ≃ty-to-≡ q = refl
  -- rewrite ≃c-to-≡ p
  -- = lem (≃ty-preserve-height q) (≃ty-to-subst-≡ q (≃ty-preserve-height q))
  -- where
  --   lem : {A : Ty n} {B : Ty n} → subst (Ty n) p A ≡ B → Γ , A ≡ Γ , B
  --   lem refl refl = refl

≃ty-to-≡ (Star≃ x) = refl
≃ty-to-≡ (Arr≃ p q r)
  rewrite ≃tm-to-≡ p
  rewrite ≃ty-to-≡ q
  rewrite ≃tm-to-≡ r = refl
-- ≃ty-to-subst-≡ (Star≃ x) refl = refl
-- ≃ty-to-subst-≡ (Arr≃ p q r) refl
--   rewrite ≃tm-to-≡ p
--   rewrite ≃ty-to-≡ q
--   rewrite ≃tm-to-≡ r = refl

≃tm-to-≡ (Var≃ x y) with toℕ-injective y
... | refl = refl
≃tm-to-≡ (Coh≃ p q r) with ≃-to-same-n p
... | refl
  rewrite ≃-to-≡ p
  rewrite ≃ty-to-≡ q
  rewrite ≃s-to-≡ r = refl

≃s-to-≡ (Null≃ x) = refl
≃s-to-≡ (Ext≃ p q)
  rewrite ≃s-to-≡ p
  rewrite ≃tm-to-≡ q = refl

lift-ty-≃ : B ≃ty C → liftType B ≃ty liftType C
lift-tm-≃ : s ≃tm t → liftTerm s ≃tm liftTerm t
lift-sub-≃ : σ ≃s τ → liftSub σ ≃s liftSub τ

lift-ty-≃ (Star≃ x) = Star≃ (cong suc x)
lift-ty-≃ (Arr≃ q r s) = Arr≃ (lift-tm-≃ q) (lift-ty-≃ r) (lift-tm-≃ s)

lift-tm-≃ (Var≃ x y) = Var≃ (cong suc x) (cong suc y)
lift-tm-≃ (Coh≃ q r s) = Coh≃ q r (lift-sub-≃ s)

lift-sub-≃ (Null≃ x) = Null≃ (lift-ty-≃ x)
lift-sub-≃ (Ext≃ q r) = Ext≃ (lift-sub-≃ q) (lift-tm-≃ r)

-- ty-base-≃ : A ≃ty B → ty-base A ≃ty ty-base B
-- ty-base-≃ (Arr≃ _ p _) = p

-- ty-src-≃ : A ≃ty B → ty-src A ≃tm ty-src B
-- ty-src-≃ (Arr≃ p _ _) = p

-- ty-tgt-≃ : A ≃ty B → ty-tgt A ≃tm ty-tgt B
-- ty-tgt-≃ (Arr≃ _ _ p) = p

-- ty-base-subbed : (A : Ty n (suc d)) → (σ : Sub n m) → ty-base A [ σ ]ty ≃ty ty-base (A [ σ ]ty)
-- ty-base-subbed (s ─⟨ A ⟩⟶ t) σ = refl≃ty

-- ty-src-subbed : (A : Ty n (suc d)) → (σ : Sub n m) → ty-src A [ σ ]tm ≃tm ty-src (A [ σ ]ty)
-- ty-src-subbed (s ─⟨ A ⟩⟶ t) σ = refl≃tm

-- ty-tgt-subbed : (A : Ty n (suc d)) → (σ : Sub n m) → ty-tgt A [ σ ]tm ≃tm ty-tgt (A [ σ ]ty)
-- ty-tgt-subbed (s ─⟨ A ⟩⟶ t) σ = refl≃tm

susp-tree-≃ : S ≃ T → suspTree S ≃ suspTree T
susp-ctx-≃ : Γ ≃c Δ → suspCtx Γ ≃c suspCtx Δ
susp-ty-≃ : A ≃ty B → suspTy A ≃ty suspTy B
susp-tm-≃ : s ≃tm t → suspTm s ≃tm suspTm t
susp-sub-≃ : σ ≃s τ → suspSub σ ≃s suspSub τ

susp-tree-≃ p = Join≃ p Sing≃

susp-ctx-≃ Emp≃ = refl≃c
susp-ctx-≃ (Add≃ p q) = Add≃ (susp-ctx-≃ p) (susp-ty-≃ q)

susp-ty-≃ (Star≃ x) with x
... | refl = refl≃ty
susp-ty-≃ (Arr≃ q r s) = Arr≃ (susp-tm-≃ q) (susp-ty-≃ r) (susp-tm-≃ s)

susp-tm-≃ (Var≃ p q) = Var≃ (cong suc (cong suc p)) (trans (toℕ-inject₁ (inject₁ _)) (trans (toℕ-inject₁ _) (trans q (sym (trans (toℕ-inject₁ (inject₁ _)) (toℕ-inject₁ _))))))
susp-tm-≃ (Coh≃ q r s) = Coh≃ (susp-tree-≃ q) (susp-ty-≃ r) (susp-sub-≃ s)

susp-sub-≃ (Null≃ (Star≃ refl)) = refl≃s
susp-sub-≃ (Ext≃ r s) = Ext≃ (susp-sub-≃ r) (susp-tm-≃ s)

unrestrict-≃ : σ ≃s τ → unrestrict σ ≃s unrestrict τ
unrestrict-≃ (Null≃ (Arr≃ p q r)) = Ext≃ (Ext≃ (Null≃ q) p) r
unrestrict-≃ (Ext≃ q x) = Ext≃ (unrestrict-≃ q) x

restrict-≃ : σ ≃s τ → s ≃tm s′ → t ≃tm t′ → restrict σ s t ≃s restrict τ s′ t′
restrict-≃ (Ext≃ (Ext≃ (Null≃ z) y) x) q r = Null≃ (Arr≃ q z r)
restrict-≃ (Ext≃ p@(Ext≃ (Ext≃ _ _) _) x) q r = Ext≃ (restrict-≃ p q r) x

sub-action-≃-ty : A ≃ty B → σ ≃s τ → A [ σ ]ty ≃ty B [ τ ]ty
sub-action-≃-tm : {σ : Sub n m A} → {τ : Sub n′ m′ B} → s ≃tm t → σ ≃s τ → s [ σ ]tm ≃tm t [ τ ]tm
sub-action-≃-sub : τ ≃s μ → σ ≃s σ′ → σ ∘ τ ≃s σ′ ∘ μ

sub-action-≃-ty (Star≃ x) q = ≃s-to-same-ty q
sub-action-≃-ty (Arr≃ p q r) s = Arr≃ (sub-action-≃-tm p s) (sub-action-≃-ty q s) (sub-action-≃-tm r s)

sub-action-≃-tm (Var≃ x y) q = lem _ _ y q
  where
    lem : {σ : Sub n m A} → {τ : Sub n′ m′ B} → (i : Fin n) → (j : Fin n′) → toℕ i ≡ toℕ j → σ ≃s τ → Var i [ σ ]tm ≃tm Var j [ τ ]tm
    lem zero zero p (Ext≃ q x) = x
    lem (suc i) (suc j) p (Ext≃ q x) = lem i j (cong pred p) q
sub-action-≃-tm {A = ⋆} {B = ⋆} (Coh≃ p q r) s = Coh≃ p q (sub-action-≃-sub r s)
sub-action-≃-tm {A = ⋆} {B = s₁ ─⟨ B ⟩⟶ t} (Coh≃ p q r) s with ≃s-to-same-ty s
... | ()
sub-action-≃-tm {A = s₁ ─⟨ A ⟩⟶ t} {B = ⋆} (Coh≃ p q r) s with ≃s-to-same-ty s
... | ()
sub-action-≃-tm {A = s₁ ─⟨ A ⟩⟶ t} {B = s₂ ─⟨ B ⟩⟶ t₁} (Coh≃ p q r) s = sub-action-≃-tm (Coh≃ (susp-tree-≃ p) (susp-ty-≃ q) (susp-sub-≃ r)) (unrestrict-≃ s)
sub-action-≃-sub (Null≃ x) q = Null≃ (sub-action-≃-ty x q)
sub-action-≃-sub (Ext≃ p x) q = Ext≃ (sub-action-≃-sub p q) (sub-action-≃-tm x q)

unrestrict-lift : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → unrestrict (liftSub σ) ≃s liftSub (unrestrict σ)
unrestrict-lift ⟨⟩ = refl≃s
unrestrict-lift ⟨ σ , t ⟩ = Ext≃ (unrestrict-lift σ) refl≃tm

restrict-lift : (σ : Sub (2 + n) m A) → (s t : Tm m) → restrict (liftSub σ) (liftTerm s) (liftTerm t) ≃s liftSub (restrict σ s t)
restrict-lift ⟨ ⟨ ⟨⟩ , v ⟩ , u ⟩ s t = Null≃ refl≃ty
restrict-lift ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ s t = Ext≃ (restrict-lift σ s t) refl≃tm

restrict-unrestrict : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → restrict (unrestrict σ) s t ≃s σ
restrict-unrestrict ⟨⟩ = refl≃s
restrict-unrestrict ⟨ ⟨⟩ , t ⟩ = refl≃s
restrict-unrestrict ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ = refl≃s
restrict-unrestrict ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , t ⟩ = Ext≃ (restrict-unrestrict σ) refl≃tm

apply-lifted-sub-ty-≃ : (B : Ty n) → (σ : Sub n m A) → B [ liftSub σ ]ty ≃ty liftType (B [ σ ]ty)
apply-lifted-sub-tm-≃ : (t : Tm n) → (σ : Sub n m A) → t [ liftSub σ ]tm ≃tm liftTerm (t [ σ ]tm)
apply-lifted-sub-sub-≃ : (τ : Sub l n B) → (σ : Sub n m A) → liftSub σ ∘ τ ≃s liftSub (σ ∘ τ)

apply-lifted-sub-ty-≃ ⋆ σ = refl≃ty
apply-lifted-sub-ty-≃ (s ─⟨ B ⟩⟶ t) σ = Arr≃ (apply-lifted-sub-tm-≃ s σ) (apply-lifted-sub-ty-≃ B σ) (apply-lifted-sub-tm-≃ t σ)

apply-lifted-sub-tm-≃ (Var zero) ⟨ σ , t ⟩ = refl≃tm
apply-lifted-sub-tm-≃ (Var (suc i)) ⟨ σ , t ⟩ = apply-lifted-sub-tm-≃ (Var i) σ
apply-lifted-sub-tm-≃ {A = ⋆} (Coh T B τ) σ = Coh≃ refl≃ refl≃ty (apply-lifted-sub-sub-≃ τ σ)
apply-lifted-sub-tm-≃ {A = s ─⟨ A ⟩⟶ t} (Coh T B τ) σ = begin
  < Coh (suspTree T) (suspTy B) (suspSub τ) [ unrestrict (liftSub σ) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (suspTree T) (suspTy B) (suspSub τ)}) (unrestrict-lift σ) ⟩
  < Coh (suspTree T) (suspTy B) (suspSub τ) [ liftSub (unrestrict σ) ]tm >tm
    ≈⟨ apply-lifted-sub-tm-≃ (Coh (suspTree T) (suspTy B) (suspSub τ)) (unrestrict σ) ⟩
  < liftTerm (Coh (suspTree T) (suspTy B) (suspSub τ) [ unrestrict σ ]tm) >tm ∎
  where
    open Reasoning tm-setoid

apply-lifted-sub-sub-≃ ⟨⟩ σ = Null≃ (apply-lifted-sub-ty-≃ _ σ)
apply-lifted-sub-sub-≃ ⟨ τ , t ⟩ σ = Ext≃ (apply-lifted-sub-sub-≃ τ σ) (apply-lifted-sub-tm-≃ t σ)

susp-ty-lift : (B : Ty n) → suspTy (liftType B) ≃ty liftType (suspTy B)
susp-tm-lift : (t : Tm n) → suspTm (liftTerm t) ≃tm liftTerm (suspTm t)
susp-sub-lift : (σ : Sub n m ⋆) → suspSub (liftSub σ) ≃s liftSub (suspSub σ)

susp-ty-lift ⋆ = Arr≃ refl≃tm (Star≃ refl) refl≃tm
susp-ty-lift (s ─⟨ B ⟩⟶ t) = Arr≃ (susp-tm-lift s) (susp-ty-lift B) (susp-tm-lift t)

susp-tm-lift (Var i) = refl≃tm
susp-tm-lift (Coh Δ A σ) = Coh≃ refl≃ refl≃ty (susp-sub-lift σ)

susp-sub-lift ⟨⟩ = refl≃s
susp-sub-lift ⟨ σ , t ⟩ = Ext≃ (susp-sub-lift σ) (susp-tm-lift t)

lift-subbed-ty-≃ : (B : Ty n) → (σ : Sub n m A) → {t : Tm (suc _)} → (liftType B) [ ⟨ liftSub σ , t ⟩ ]ty ≃ty liftType (B [ σ ]ty)
lift-subbed-tm-≃ : (s : Tm n) → (σ : Sub n m A) → {t : Tm (suc _)} → (liftTerm s) [ ⟨ liftSub σ , t ⟩ ]tm ≃tm liftTerm (s [ σ ]tm)
lift-subbed-sub-≃ : (τ : Sub l n B) → (σ : Sub n m A) → {t : Tm (suc _)} → ⟨ liftSub σ , t ⟩ ∘ liftSub τ ≃s liftSub (σ ∘ τ)
-- lift-subbed-var-≃ : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ) → Var i [ liftSub {A = A} σ ]tm ≃tm liftTerm {A = A} (Var i [ σ ]tm)

lift-subbed-ty-≃ ⋆ σ = refl≃ty
lift-subbed-ty-≃ (s ─⟨ B ⟩⟶ t) σ = Arr≃ (lift-subbed-tm-≃ s σ) (lift-subbed-ty-≃ B σ) (lift-subbed-tm-≃ t σ)

lift-subbed-tm-≃ (Var zero) ⟨ σ , t ⟩ = refl≃tm
lift-subbed-tm-≃ (Var (suc i)) ⟨ σ , t ⟩ = apply-lifted-sub-tm-≃ (Var i) σ
lift-subbed-tm-≃ {A = ⋆} (Coh T B τ) σ = Coh≃ refl≃ refl≃ty (lift-subbed-sub-≃ τ σ)
lift-subbed-tm-≃ {A = s ─⟨ A ⟩⟶ t} (Coh T B τ) σ {t = u} = begin
  < Coh (suspTree T) (suspTy B) (suspSub (liftSub τ)) [ ⟨ unrestrict (liftSub σ) , u ⟩ ]tm >tm
    ≈⟨ sub-action-≃-tm (Coh≃ refl≃ refl≃ty (susp-sub-lift τ)) (Ext≃ (unrestrict-lift σ) (refl≃tm {s = u})) ⟩
  < Coh (suspTree T) (suspTy B) (liftSub (suspSub τ)) [ ⟨ liftSub (unrestrict σ) , u ⟩ ]tm >tm
    ≈⟨ lift-subbed-tm-≃ (Coh (suspTree T) (suspTy B) (suspSub τ)) (unrestrict σ) ⟩
  < liftTerm (Coh (suspTree T) (suspTy B) (suspSub τ) [ unrestrict σ ]tm) >tm ∎
  where
    open Reasoning tm-setoid

lift-subbed-sub-≃ {B = B} ⟨⟩ σ {t = t} = Null≃ (lift-subbed-ty-≃ B σ {t})
lift-subbed-sub-≃ ⟨ τ , t ⟩ σ = Ext≃ (lift-subbed-sub-≃ τ σ) (lift-subbed-tm-≃ t σ)


‼-≃ : (i : Fin (ctxLength Γ)) → (j : Fin (ctxLength Δ)) → toℕ i ≡ toℕ j → Γ ≃c Δ → Γ ‼ i ≃ty Δ ‼ j
‼-≃ zero zero p (Add≃ q x) = lift-ty-≃ x
‼-≃ (suc i) (suc j) p (Add≃ q x) = lift-ty-≃ (‼-≃ i j (cong pred p) q)

≃-dec : (S : Tree n) → (T : Tree m) → Dec (S ≃ T)
≃c-dec : (Γ : Ctx n) → (Γ′ : Ctx m) → Dec (Γ ≃c Γ′)
≃ty-dec : (A : Ty n) → (B : Ty m) → Dec (A ≃ty B)
≃tm-dec : (s : Tm n) → (t : Tm m) → Dec (s ≃tm t)
≃s-dec : (σ : Sub n m A) → (τ : Sub n′ m′ B) → Dec (σ ≃s τ)

≃-dec Sing Sing = yes Sing≃
≃-dec Sing (Join S T) = no λ ()
≃-dec (Join S T) Sing = no λ ()
≃-dec (Join S T) (Join S′ T′) with ≃-dec S S′ | ≃-dec T T′
... | yes p | yes q = yes (Join≃ p q)
... | yes p | no q = no λ where (Join≃ x y) → q y
... | no p | q = no λ where (Join≃ x y) → p x

≃c-dec ∅ ∅ = yes Emp≃
≃c-dec ∅ (Γ′ , B) = no λ ()
≃c-dec (Γ , A) ∅ = no λ ()
≃c-dec (Γ , A) (Γ′ , B) with ≃c-dec Γ Γ′ | ≃ty-dec A B
... | yes p | yes q = yes (Add≃ p q)
... | yes p | no q = no (λ where (Add≃ _ x) → q x)
... | no p | q = no λ where (Add≃ x _) → p x

≃ty-dec (⋆ {n = n}) (⋆ {n = m}) with n ≟ m
... | yes p = yes (Star≃ p)
... | no p = no (λ where (Star≃ x) → p x)
≃ty-dec ⋆ (s ─⟨ B ⟩⟶ t) = no (λ ())
≃ty-dec (s ─⟨ A ⟩⟶ t) ⋆ = no (λ ())
≃ty-dec (s ─⟨ A ⟩⟶ t) (s′ ─⟨ A′ ⟩⟶ t′) with ≃tm-dec s s′ | ≃ty-dec A A′ | ≃tm-dec t t′
... | yes p | yes q | yes r = yes (Arr≃ p q r)
... | yes p | yes q | no r = no (λ where (Arr≃ _ _ x) → r x)
... | yes p | no q | r = no (λ where (Arr≃ _ x _) → q x)
... | no p | q | r = no (λ where (Arr≃ x _ _) → p x)

≃tm-dec (Var {n = n} i) (Var {n = m} j) with n ≟ m | toℕ i ≟ toℕ j
... | yes p | yes q = yes (Var≃ p q)
... | yes p | no q = no (λ where (Var≃ x y) → q y)
... | no p | q = no (λ where (Var≃ x y) → p x)

≃tm-dec (Var i) (Coh Δ A σ) = no (λ ())
≃tm-dec (Coh Δ A σ) (Var i) = no (λ ())
≃tm-dec (Coh Δ A σ) (Coh Δ′ A′ σ′) with ≃-dec Δ Δ′ | ≃ty-dec A A′ | ≃s-dec σ σ′
... | yes p | yes q | yes r = yes (Coh≃ p q r)
... | yes p | yes q | no r = no λ where (Coh≃ _ _ x) → r x
... | yes p | no q | r = no λ where (Coh≃ _ x _) → q x
... | no p | q | r = no λ where (Coh≃ x _ _) → p x

≃s-dec (⟨⟩ {A = A}) (⟨⟩ {A = B}) with ≃ty-dec A B
... | yes p = yes (Null≃ p)
... | no p = no λ where (Null≃ x) → p x
≃s-dec ⟨⟩ ⟨ τ , t ⟩ = no (λ ())
≃s-dec ⟨ σ , t ⟩ ⟨⟩ = no (λ ())
≃s-dec ⟨ σ , s ⟩ ⟨ τ , t ⟩ with ≃s-dec σ τ | ≃tm-dec s t
... | yes p | yes q = yes (Ext≃ p q)
... | yes p | no q = no (λ where (Ext≃ _ x) → q x)
... | no p | q = no (λ where (Ext≃ x _) → p x)

ctx-dec : DecidableEquality (Ctx n)
ctx-dec Γ Δ = map (equivalence ≃c-to-≡ reflexive≃c) (≃c-dec Γ Δ)

ty-dec : DecidableEquality (Ty n)
ty-dec A B = map (equivalence ≃ty-to-≡ reflexive≃ty) (≃ty-dec A B)

tm-dec : DecidableEquality (Tm n)
tm-dec s t = map (equivalence ≃tm-to-≡ reflexive≃tm) (≃tm-dec s t)

sub-dec : DecidableEquality (Sub n m A)
sub-dec σ τ = map (equivalence ≃s-to-≡ reflexive≃s) (≃s-dec σ τ)

≃-irrel : Irrelevant (S ≃ T)
≃c-irrel : Irrelevant (Γ ≃c Δ)
≃ty-irrel : Irrelevant (A ≃ty B)
≃tm-irrel : Irrelevant (s ≃tm t)
≃s-irrel : Irrelevant (σ ≃s τ)

≃-irrel Sing≃ Sing≃ = refl
≃-irrel (Join≃ p q) (Join≃ p′ q′) = cong₂ Join≃ (≃-irrel p p′) (≃-irrel q q′)

≃c-irrel Emp≃ Emp≃ = refl
≃c-irrel (Add≃ p x) (Add≃ q y) = cong₂ Add≃ (≃c-irrel p q) (≃ty-irrel x y)

≃ty-irrel (Star≃ x) (Star≃ y) = cong Star≃ (≡-irrelevant x y)
≃ty-irrel (Arr≃ p q r) (Arr≃ p′ q′ r′) = lem (≃tm-irrel p p′) (≃ty-irrel q q′) (≃tm-irrel r r′)
  where
    lem : {a b : s ≃tm s′} {c d : A ≃ty A′} {e f : t ≃tm t′} → a ≡ b → c ≡ d → e ≡ f → Arr≃ a c e ≡ Arr≃ b d f
    lem refl refl refl = refl

≃tm-irrel (Var≃ p q) (Var≃ p′ q′) = cong₂ Var≃ (≡-irrelevant p p′) (≡-irrelevant q q′)
≃tm-irrel (Coh≃ p q r) (Coh≃ p′ q′ r′) = lem (≃-irrel p p′) (≃ty-irrel q q′) (≃s-irrel r r′)
  where
    lem : {a b : S ≃ T} {c d : A ≃ty A′} {e f : σ ≃s τ} → a ≡ b → c ≡ d → e ≡ f → Coh≃ a c e ≡ Coh≃ b d f
    lem refl refl refl = refl

≃s-irrel (Null≃ x) (Null≃ y) = cong Null≃ (≃ty-irrel x y)
≃s-irrel (Ext≃ p x) (Ext≃ q y) = cong₂ Ext≃ (≃s-irrel p q) (≃tm-irrel x y)

-- categorical properties

lift-sub-comp-lem-sub : (σ : Sub n l A) → (τ : Sub m n B) → ⟨ σ , t ⟩ ∘ liftSub τ ≃s σ ∘ τ
lift-sub-comp-lem-tm : (σ : Sub n l A) → (s : Tm n) → liftTerm s [ ⟨ σ , t ⟩ ]tm ≃tm s [ σ ]tm
lift-sub-comp-lem-ty : (σ : Sub n l A) → (B : Ty n) → liftType B [ ⟨ σ , t ⟩ ]ty ≃ty B [ σ ]ty

lift-sub-comp-lem-sub {B = B} σ ⟨⟩ = Null≃ (lift-sub-comp-lem-ty σ B)
lift-sub-comp-lem-sub σ ⟨ τ , t ⟩ = Ext≃ (lift-sub-comp-lem-sub σ τ) (lift-sub-comp-lem-tm σ t)

lift-sub-comp-lem-tm σ (Var i) = refl≃tm
lift-sub-comp-lem-tm {A = ⋆} σ (Coh T B τ) = Coh≃ refl≃ refl≃ty (lift-sub-comp-lem-sub σ τ)
lift-sub-comp-lem-tm {A = s ─⟨ A ⟩⟶ t} {t = u} σ (Coh T B τ) = begin
  < Coh (suspTree T) (suspTy B) (suspSub (liftSub τ)) [ ⟨ unrestrict σ , u ⟩ ]tm >tm
    ≈⟨ sub-action-≃-tm {s = Coh (suspTree T) (suspTy B) (suspSub (liftSub τ))} {t = Coh (suspTree T) (suspTy B) (liftSub (suspSub τ))} (Coh≃ refl≃ refl≃ty (susp-sub-lift τ)) (refl≃s {σ = ⟨ unrestrict σ , u ⟩}) ⟩
  < Coh (suspTree T) (suspTy B) (liftSub (suspSub τ)) [ ⟨ unrestrict σ , u ⟩ ]tm >tm
    ≈⟨ lift-sub-comp-lem-tm (unrestrict σ) (Coh (suspTree T) (suspTy B) (suspSub τ)) ⟩
  < Coh (suspTree T) (suspTy B) (suspSub τ) [ unrestrict σ ]tm >tm ∎
  where
    open Reasoning tm-setoid

lift-sub-comp-lem-ty σ ⋆ = refl≃ty
lift-sub-comp-lem-ty σ (s ─⟨ B ⟩⟶ t) = Arr≃ (lift-sub-comp-lem-tm σ s) (lift-sub-comp-lem-ty σ B) (lift-sub-comp-lem-tm σ t)

id-right-unit : (σ : Sub n m A) → σ ∘ idSub n ≃s σ
id-right-unit ⟨⟩ = refl≃s
id-right-unit ⟨ σ , t ⟩ = Ext≃ (trans≃s (lift-sub-comp-lem-sub σ (idSub _)) (id-right-unit σ)) refl≃tm

id-left-unit : (σ : Sub m n A) → idSub n ∘ σ ≃s σ
id-on-ty : (B : Ty m) → B [ idSub m ]ty ≃ty B
id-on-tm : (t : Tm m) → t [ idSub m ]tm ≃tm t

id-left-unit ⟨⟩ = Null≃ (id-on-ty _)
id-left-unit ⟨ σ , t ⟩ = Ext≃ (id-left-unit σ) (id-on-tm t)

id-on-ty ⋆ = Star≃ refl
id-on-ty (s ─⟨ B ⟩⟶ t) = Arr≃ (id-on-tm s) (id-on-ty B) (id-on-tm t)

id-on-tm (Var i) = lem i
  where
    lem : (i : Fin m) → Var i [ idSub m ]tm ≃tm Var i
    lem {m = suc m} zero = refl≃tm
    lem {m = suc m} (suc i) = trans≃tm (apply-lifted-sub-tm-≃ (Var i) (idSub m)) (lift-tm-≃ (lem i))
id-on-tm (Coh Δ A σ) = Coh≃ refl≃ refl≃ty (id-left-unit σ)

susp-sub-preserve-getFst : (σ : Sub n m ⋆) → getFst {n = m} ≃tm getFst [ suspSub σ ]tm
susp-sub-preserve-getFst ⟨⟩ = refl≃tm
susp-sub-preserve-getFst ⟨ σ , t ⟩ = susp-sub-preserve-getFst σ

susp-sub-preserve-getSnd : (σ : Sub n m ⋆) → getSnd {n = m} ≃tm getSnd [ suspSub σ ]tm
susp-sub-preserve-getSnd ⟨⟩ = refl≃tm
susp-sub-preserve-getSnd ⟨ σ , t ⟩ = susp-sub-preserve-getSnd σ

susp-functorial : (σ : Sub m l ⋆) → (τ : Sub n m ⋆) → suspSub (σ ∘ τ) ≃s suspSub σ ∘ suspSub τ
susp-functorial-tm : (σ : Sub m l ⋆) → (t : Tm m) → suspTm (t [ σ ]tm) ≃tm suspTm t [ suspSub σ ]tm
susp-functorial-ty : (σ : Sub m l ⋆) → (A : Ty m) → suspTy (A [ σ ]ty) ≃ty suspTy A [ suspSub σ ]ty

susp-functorial σ ⟨⟩ = Ext≃ (Ext≃ refl≃s (susp-sub-preserve-getFst σ)) (susp-sub-preserve-getSnd σ)
susp-functorial σ ⟨ τ , t ⟩ = Ext≃ (susp-functorial σ τ) (susp-functorial-tm σ t)

susp-functorial-tm σ (Var i) = lem σ i
  where
    lem : (σ : Sub n m ⋆) → (i : Fin n) → suspTm (Var i [ σ ]tm) ≃tm (Var (inject₁ (inject₁ i)) [ suspSub σ ]tm)
    lem ⟨ σ , t ⟩ zero = refl≃tm
    lem ⟨ σ , t ⟩ (suc i) = lem σ i
susp-functorial-tm σ (Coh Δ A τ) = Coh≃ refl≃ refl≃ty (susp-functorial σ τ)

susp-functorial-ty σ ⋆ = Arr≃ (susp-sub-preserve-getFst σ) (Star≃ refl) (susp-sub-preserve-getSnd σ)
susp-functorial-ty σ (s ─⟨ A ⟩⟶ t) = Arr≃ (susp-functorial-tm σ s) (susp-functorial-ty σ A) (susp-functorial-tm σ t)

unrestrict-comp : (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → (τ : Sub m l ⋆) → unrestrict (σ ∘ τ) ≃s unrestrict σ ∘ suspSub τ
unrestrict-comp-tm : (u : Tm l) → (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → u [ σ ]tm ≃tm suspTm u [ unrestrict σ ]tm
unrestrict-comp-ty : (B : Ty l) → (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → B [ σ ]ty ≃ty suspTy B [ unrestrict σ ]ty
unrestrict-fst : (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → s ≃tm getFst [ unrestrict σ ]tm
unrestrict-snd : (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → t ≃tm getSnd [ unrestrict σ ]tm

unrestrict-comp σ ⟨⟩ = Ext≃ (Ext≃ refl≃s (unrestrict-fst σ)) (unrestrict-snd σ)
unrestrict-comp σ ⟨ τ , u ⟩ = Ext≃ (unrestrict-comp σ τ) (unrestrict-comp-tm u σ)

unrestrict-comp-tm (Var zero) ⟨ σ , t ⟩ = refl≃tm
unrestrict-comp-tm (Var (suc i)) ⟨ σ , t ⟩ = unrestrict-comp-tm (Var i) σ
unrestrict-comp-tm (Coh S B τ) σ = refl≃tm

unrestrict-comp-ty ⋆ σ = Arr≃ (unrestrict-fst σ) refl≃ty (unrestrict-snd σ)
unrestrict-comp-ty (s ─⟨ B ⟩⟶ t) σ = Arr≃ (unrestrict-comp-tm s σ) (unrestrict-comp-ty B σ) (unrestrict-comp-tm t σ)

unrestrict-fst ⟨⟩ = refl≃tm
unrestrict-fst ⟨ σ , u ⟩ = unrestrict-fst σ

unrestrict-snd ⟨⟩ = refl≃tm
unrestrict-snd ⟨ σ , u ⟩ = unrestrict-snd σ

unrestrict-comp-higher : (σ : Sub l o A) → (τ : Sub m l (s′ ─⟨ B ⟩⟶ t′)) → unrestrict (σ ∘ τ) ≃s σ ∘ unrestrict τ
unrestrict-comp-higher σ ⟨⟩ = refl≃s
unrestrict-comp-higher σ ⟨ τ , t ⟩ = Ext≃ (unrestrict-comp-higher σ τ) refl≃tm

∘-assoc : (σ : Sub n l A) → (τ : Sub m n B) → (μ : Sub m′ m C) → (σ ∘ τ) ∘ μ ≃s σ ∘ (τ ∘ μ)
assoc-tm : ∀ {B} {A} → (σ : Sub n l A) → (τ : Sub m n B) → (t : Tm m) → t [ σ ∘ τ ]tm ≃tm (t [ τ ]tm) [ σ ]tm
assoc-ty : (σ : Sub n l A) → (τ : Sub m n B) → (A : Ty m) → A [ σ ∘ τ ]ty ≃ty (A [ τ ]ty) [ σ ]ty

∘-assoc σ τ ⟨⟩ = Null≃ (assoc-ty σ τ _)
∘-assoc σ τ ⟨ μ , t ⟩ = Ext≃ (∘-assoc σ τ μ) (assoc-tm σ τ t)

assoc-tm σ τ (Var i) = lem σ τ i
  where
    lem : (σ : Sub n l A) → (τ : Sub m n B) → (i : Fin m) → Var i [ σ ∘ τ ]tm ≃tm (Var i [ τ ]tm) [ σ ]tm
    lem σ ⟨ τ , t ⟩ zero = refl≃tm
    lem σ ⟨ τ , t ⟩ (suc i) = lem σ τ i
assoc-tm {B = ⋆} {A = ⋆} σ τ (Coh T C μ) = Coh≃ refl≃ refl≃ty (∘-assoc σ τ μ)
assoc-tm {B = ⋆} {A = s ─⟨ A ⟩⟶ t} σ τ (Coh T C μ) = begin
  < Coh (suspTree T) (suspTy C) (suspSub μ) [ unrestrict (σ ∘ τ) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (suspTree T) (suspTy C) (suspSub μ)}) (unrestrict-comp σ τ) ⟩
  < Coh (suspTree T) (suspTy C) (suspSub μ) [ unrestrict σ ∘ suspSub τ ]tm >tm
    ≈⟨ assoc-tm (unrestrict σ) (suspSub τ) (Coh (suspTree T) (suspTy C) (suspSub μ)) ⟩
  < Coh (suspTree T) (suspTy C) (suspSub τ ∘ suspSub μ) [ unrestrict σ ]tm >tm
    ≈˘⟨ sub-action-≃-tm (Coh≃ refl≃ refl≃ty (susp-functorial τ μ)) (refl≃s {σ = unrestrict σ}) ⟩
  < Coh (suspTree T) (suspTy C) (suspSub (τ ∘ μ)) [ unrestrict σ ]tm >tm ∎
  where
    open Reasoning tm-setoid
assoc-tm {B = s′ ─⟨ B ⟩⟶ t′} σ τ (Coh T C μ) = begin
  < Coh (suspTree T) (suspTy C) (suspSub μ) [ unrestrict (σ ∘ τ) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (suspTree T) (suspTy C) (suspSub μ)}) (unrestrict-comp-higher σ τ) ⟩
  < Coh (suspTree T) (suspTy C) (suspSub μ) [ σ ∘ unrestrict τ ]tm >tm
    ≈⟨ assoc-tm σ (unrestrict τ) (Coh (suspTree T) (suspTy C) (suspSub μ)) ⟩
  < Coh (suspTree T) (suspTy C) (suspSub μ) [ unrestrict τ ]tm [ σ ]tm >tm ∎
  where
    open Reasoning tm-setoid

assoc-ty σ τ ⋆ = refl≃ty
assoc-ty σ τ (s ─⟨ A ⟩⟶ t) = Arr≃ (assoc-tm σ τ s) (assoc-ty σ τ A) (assoc-tm σ τ t)

-- Equal contexts are iso

idSub≃ : Γ ≃c Δ → Sub (ctxLength Γ) (ctxLength Δ) ⋆
idSub≃ Emp≃ = ⟨⟩
idSub≃ (Add≃ p x) = ⟨ (liftSub (idSub≃ p)) , 0V ⟩

idSub≃-on-ty : (p : Γ ≃c Δ) → (A : Ty (ctxLength Γ)) → A [ idSub≃ p ]ty ≃ty A
idSub≃-on-tm : (p : Γ ≃c Δ) → (s : Tm (ctxLength Γ)) → s [ idSub≃ p ]tm ≃tm s
idSub≃-on-sub : (p : Γ ≃c Δ) → (σ : Sub n (ctxLength Γ) A) → idSub≃ p ∘ σ ≃s σ

idSub≃-on-ty p ⋆ = Star≃ (sym (≃c-preserve-length p))
idSub≃-on-ty p (s ─⟨ A ⟩⟶ t) = Arr≃ (idSub≃-on-tm p s) (idSub≃-on-ty p A) (idSub≃-on-tm p t)

idSub≃-on-tm p (Var i) = lem p i
  where
    lem : (p : Γ ≃c Δ) → (i : Fin (ctxLength Γ)) → Var i [ idSub≃ p ]tm ≃tm Var {n = ctxLength Γ} i
    lem (Add≃ p x) zero = Var≃ (cong suc (sym (≃c-preserve-length p))) refl
    lem (Add≃ p x) (suc i) = trans≃tm (apply-lifted-sub-tm-≃ (Var i) (idSub≃ p)) (lift-tm-≃ (lem p i))
idSub≃-on-tm p (Coh Δ A σ) = Coh≃ refl≃ refl≃ty (idSub≃-on-sub p σ)

idSub≃-on-sub p ⟨⟩ = Null≃ (idSub≃-on-ty p _)
idSub≃-on-sub p ⟨ σ , t ⟩ = Ext≃ (idSub≃-on-sub p σ) (idSub≃-on-tm p t)

idSub≃-right-unit : (p : Γ ≃c Δ) → (σ : Sub (ctxLength Δ) n A) → σ ∘ idSub≃ p ≃s σ
idSub≃-right-unit Emp≃ ⟨⟩ = refl≃s
idSub≃-right-unit (Add≃ p x) ⟨ σ , t ⟩ = Ext≃ (trans≃s (lift-sub-comp-lem-sub σ (idSub≃ p)) (idSub≃-right-unit p σ)) refl≃tm

idSub≃-functorial : (p : Γ ≃c Δ) → (q : Δ ≃c Υ) → idSub≃ q ∘ idSub≃ p ≃s idSub≃ (trans≃c p q)
idSub≃-functorial Emp≃ Emp≃ = refl≃s
idSub≃-functorial (Add≃ p x) (Add≃ q y) = Ext≃ lem refl≃tm
  where
    lem : (idSub≃ (Add≃ q y) ∘ liftSub (idSub≃ p)) ≃s
            liftSub (idSub≃ (trans≃c p q))
    lem = trans≃s (lift-sub-comp-lem-sub (liftSub (idSub≃ q)) (idSub≃ p)) (trans≃s (apply-lifted-sub-sub-≃ (idSub≃ p) (idSub≃ q)) (lift-sub-≃ (idSub≃-functorial p q)))

idSub≃-fst-var : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (p : Γ ≃c Δ) → Var (fromℕ n) [ idSub≃ p ]tm ≃tm Var (fromℕ m)
idSub≃-fst-var (Add≃ Emp≃ x) = refl≃tm
idSub≃-fst-var (Add≃ (Add≃ p y) x) = trans≃tm (apply-lifted-sub-tm-≃ (Var (fromℕ _)) (idSub≃ (Add≃ p y))) (lift-tm-≃ (idSub≃-fst-var (Add≃ p y)))

idSub≃-snd-var : {Γ : Ctx (suc (suc n))} → {Δ : Ctx (suc (suc m))} → (p : Γ ≃c Δ) → Var (inject₁ (fromℕ n)) [ idSub≃ p ]tm ≃tm Var (inject₁ (fromℕ m))
idSub≃-snd-var (Add≃ (Add≃ Emp≃ y) x) = refl≃tm
idSub≃-snd-var (Add≃ (Add≃ (Add≃ p z) y) x) = trans≃tm (apply-lifted-sub-tm-≃ (Var (inject₁ (fromℕ _))) (idSub≃ (Add≃ (Add≃ p z) y))) (lift-tm-≃ (idSub≃-snd-var (Add≃ (Add≃ p z) y)))

idSub-id : {Γ Δ : Ctx n} → (p : Γ ≃c Δ) → idSub≃ p ≃s idSub n
idSub-id Emp≃ = refl≃s
idSub-id (Add≃ p x) = Ext≃ (lift-sub-≃ (idSub-id p)) refl≃tm

-- idSub≃-on-ty p (Star≃ x) = Star≃ (trans≃c (sym≃c p) x)
-- idSub≃-on-ty p (Arr≃ q r s) = Arr≃ (idSub≃-on-tm p q) (idSub≃-on-ty p r) (idSub≃-on-tm p s)

-- idSub≃-on-tm p (Var≃ x) = lem p _ _ x
--   where
--     lem : (p : Γ ≃c Δ) → (i : Fin (ctxLength Γ)) → (j : Fin (ctxLength Υ)) → toℕ i ≡ toℕ j → Var i [ idSub≃ p ]tm ≃tm Var {Γ = Υ} j
--     lem {Γ = Γ , A} {Υ = Υ , A′} (Add≃ p x) zero zero q = Var≃ refl
--     lem {Γ = Γ , A} {Υ = Υ , A′} (Add≃ p x) (suc i) (suc j) q = trans≃tm (apply-lifted-sub-tm-≃ (Var i) (idSub≃ p)) (lift-tm-≃ {!!} (lem p i j (cong pred q)))
-- idSub≃-on-tm p (Coh≃ q r s) = Coh≃ q r (idSub≃-on-sub p s)

-- idSub≃-on-sub p Null≃ = Null≃
-- idSub≃-on-sub p (Ext≃ q r) = Ext≃ (idSub≃-on-sub p q) (idSub≃-on-tm p r)

-- ⋆-is-only-0-d-ty : {A : Ty n} → (⋆ {n = n}) ≃ty A
-- ⋆-is-only-0-d-ty {A = ⋆} = Star≃ refl

⋆-is-only-ty-in-empty-context : (A : Ty 0) → A ≃ty ⋆ {n = 0}
⋆-is-only-ty-in-empty-context ⋆ = refl≃ty
⋆-is-only-ty-in-empty-context (s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)

-- sub-from-function-≃ : (f : (i : Fin n) → Tm m)
--                     → (f2 : (i : Fin n) → Tm m)
--                     → ((i : Fin n) → f i ≃tm f2 i)
--                     → sub-from-function f ≃s sub-from-function f2
-- sub-from-function-≃ {n = zero} f f2 eq = Null≃ refl
-- sub-from-function-≃ {n = suc n} f f2 eq = Ext≃ (sub-from-function-≃ (λ i → f (suc i)) (λ i → f2 (suc i)) (λ i → eq (suc i))) (eq zero)

-- lift-sub-from-function : (f : (i : Fin n) → Tm m)
--                        → liftSub (sub-from-function f) ≃s sub-from-function (λ i → liftTerm (f i))
-- lift-sub-from-function {n = zero} f = Null≃ refl
-- lift-sub-from-function {n = suc n} f = Ext≃ (lift-sub-from-function (λ i → f (suc i))) refl≃tm

-- sub-≃-term-wise : (σ : Sub n m) → (τ : Sub n m) → ((i : Fin n) → Var i [ σ ]tm ≃tm Var i [ τ ]tm) → σ ≃s τ
-- sub-≃-term-wise ⟨⟩ ⟨⟩ f = Null≃ refl
-- sub-≃-term-wise ⟨ σ , t ⟩ ⟨ τ , s ⟩ f = Ext≃ (sub-≃-term-wise σ τ (λ i → f (suc i))) (f zero)

-- sub-from-function-prop : (f : (i : Fin n) → Tm m)
--                        → (i : Fin n)
--                        → Var i [ sub-from-function f ]tm ≃tm f i
-- sub-from-function-prop f zero = refl≃tm
-- sub-from-function-prop f (suc i) = sub-from-function-prop (λ j → f (suc j)) i

liftType-inj : liftType A ≃ty liftType B → A ≃ty B
liftTerm-inj : liftTerm s ≃tm liftTerm t → s ≃tm t
liftSub-inj : liftSub σ ≃s liftSub τ → σ ≃s τ

liftType-inj {A = ⋆} {B = ⋆} (Star≃ refl) = refl≃ty
liftType-inj {A = s ─⟨ A ⟩⟶ t} {B = s′ ─⟨ B ⟩⟶ t′} (Arr≃ p q r) = Arr≃ (liftTerm-inj p) (liftType-inj q) (liftTerm-inj r)

liftTerm-inj {s = Var i} {t = Var j} (Var≃ refl p) = Var≃ refl (cong pred p)
liftTerm-inj {s = Coh Δ A σ} {t = Coh Δ′ A′ σ′} (Coh≃ p q r) = Coh≃ p q (liftSub-inj r)

liftSub-inj {σ = ⟨⟩} {τ = ⟨⟩} (Null≃ x) = Null≃ (liftType-inj x)
liftSub-inj {σ = ⟨ σ , t ⟩} {τ = ⟨ τ , s ⟩} (Ext≃ p q) = Ext≃ (liftSub-inj p) (liftTerm-inj q)
