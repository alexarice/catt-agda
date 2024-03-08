module Catt.Syntax.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Globular
open import Catt.Suspension

open import Relation.Nullary.Decidable
open import Relation.Binary hiding (Irrelevant)
open import Function.Bundles

no-term-in-empty-context : ¬ Tm 0
no-term-in-empty-context (Coh S A ⟨ σ , t ⟩) = no-term-in-empty-context t

n-to-0-sub-impossible : ¬ (Sub (suc n) 0 A)
n-to-0-sub-impossible ⟨ μ , t ⟩ = no-term-in-empty-context t

infix 4 _≃c_ _≃ty_ _≃tm_ _≃s_
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
  Coh≃ : {σ : Sub (suc n) m ⋆} → {σ′ : Sub (suc n′) m′ ⋆} → Δ ≃c Δ′ → A ≃ty A′ → σ ≃s σ′ → Coh Δ A σ ≃tm Coh Δ′ A′ σ′

data _≃s_ where
  Null≃ : A ≃ty B → ⟨ A ⟩′ ≃s ⟨ B ⟩′
  Ext≃ : σ ≃s σ′ → t ≃tm t′ → ⟨ σ , t ⟩ ≃s ⟨ σ′ , t′ ⟩

refl≃c : Γ ≃c Γ
refl≃ty : A ≃ty A
refl≃tm : s ≃tm s
refl≃s : σ ≃s σ

refl≃c {Γ = ∅} = Emp≃
refl≃c {Γ = Γ , A} = Add≃ refl≃c refl≃ty

refl≃ty {A = ⋆} = Star≃ refl
refl≃ty {A = s ─⟨ A ⟩⟶ t} = Arr≃ refl≃tm refl≃ty refl≃tm

refl≃tm {s = Var i} = Var≃ refl refl
refl≃tm {s = Coh Δ A σ} = Coh≃ refl≃c refl≃ty refl≃s

refl≃s {σ = ⟨ A ⟩′} = Null≃ refl≃ty
refl≃s {σ = ⟨ σ , t ⟩} = Ext≃ refl≃s refl≃tm

sym≃c : Γ ≃c Δ → Δ ≃c Γ
sym≃ty : A ≃ty B → B ≃ty A
sym≃tm : s ≃tm t → t ≃tm s
sym≃s : σ ≃s τ → τ ≃s σ

sym≃c Emp≃ = Emp≃
sym≃c (Add≃ p q) = Add≃ (sym≃c p) (sym≃ty q)

sym≃ty (Star≃ x) = Star≃ (sym x)
sym≃ty (Arr≃ p q r) = Arr≃ (sym≃tm p) (sym≃ty q) (sym≃tm r)

sym≃tm (Var≃ x y) = Var≃ (sym x) (sym y)
sym≃tm (Coh≃ p q r) = Coh≃ (sym≃c p) (sym≃ty q) (sym≃s r)

sym≃s (Null≃ x) = Null≃ (sym≃ty x)
sym≃s (Ext≃ p q) = Ext≃ (sym≃s p) (sym≃tm q)

trans≃c : Γ ≃c Δ → Δ ≃c Υ → Γ ≃c Υ
trans≃ty : A ≃ty B → B ≃ty C → A ≃ty C
trans≃tm : s ≃tm t → t ≃tm u → s ≃tm u
trans≃s : σ ≃s τ → τ ≃s μ → σ ≃s μ

trans≃c Emp≃ Emp≃ = Emp≃
trans≃c (Add≃ p q) (Add≃ r s) = Add≃ (trans≃c p r) (trans≃ty q s)

trans≃ty (Star≃ x) (Star≃ y) = Star≃ (trans x y)
trans≃ty (Arr≃ p q r) (Arr≃ s t u) = Arr≃ (trans≃tm p s) (trans≃ty q t) (trans≃tm r u)

trans≃tm (Var≃ w x) (Var≃ y z) = Var≃ (trans w y) (trans x z)
trans≃tm (Coh≃ p q r) (Coh≃ s t u) = Coh≃ (trans≃c p s) (trans≃ty q t) (trans≃s r u)

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

≃tm-to-same-length : {s : Tm n} → {t : Tm m} → s ≃tm t → n ≡ m
≃tm-to-same-length (Var≃ x y) = x
≃tm-to-same-length (Coh≃ x y z) = ≃s-to-codomain-≡ z

cast-ty : n ≡ m → Ty n → Ty m
cast-ty refl A = A

cast-ty-prop : (p : n ≡ m) → (A : Ty n) → A ≃ty cast-ty p A
cast-ty-prop refl A = refl≃ty

≃c-to-≡ : Γ ≃c Δ → Γ ≡ Δ
≃ty-to-≡ : A ≃ty B → A ≡ B
≃tm-to-≡ : s ≃tm t → s ≡ t
≃s-to-≡ : σ ≃s τ → σ ≡ τ

≃c-to-≡ Emp≃ = refl
≃c-to-≡ (Add≃ p q)
  rewrite ≃c-to-≡ p
  rewrite ≃ty-to-≡ q = refl

≃ty-to-≡ (Star≃ x) = refl
≃ty-to-≡ (Arr≃ p q r)
  rewrite ≃tm-to-≡ p
  rewrite ≃ty-to-≡ q
  rewrite ≃tm-to-≡ r = refl

≃tm-to-≡ (Var≃ x y) with toℕ-injective y
... | refl = refl
≃tm-to-≡ (Coh≃ p q r) with ≃c-preserve-length p
... | refl
  rewrite ≃c-to-≡ p
  rewrite ≃ty-to-≡ q
  rewrite ≃s-to-≡ r = refl

≃s-to-≡ (Null≃ x) = refl
≃s-to-≡ (Ext≃ p q)
  rewrite ≃s-to-≡ p
  rewrite ≃tm-to-≡ q = refl

wk-ty-≃ : B ≃ty C → wk-ty B ≃ty wk-ty C
wk-tm-≃ : s ≃tm t → wk-tm s ≃tm wk-tm t
wk-sub-≃ : σ ≃s τ → wk-sub σ ≃s wk-sub τ

wk-ty-≃ (Star≃ x) = Star≃ (cong suc x)
wk-ty-≃ (Arr≃ q r s) = Arr≃ (wk-tm-≃ q) (wk-ty-≃ r) (wk-tm-≃ s)

wk-tm-≃ (Var≃ x y) = Var≃ (cong suc x) (cong suc y)
wk-tm-≃ (Coh≃ q r s) = Coh≃ q r (wk-sub-≃ s)

wk-sub-≃ (Null≃ x) = Null≃ (wk-ty-≃ x)
wk-sub-≃ (Ext≃ q r) = Ext≃ (wk-sub-≃ q) (wk-tm-≃ r)

susp-ctx-≃ : Γ ≃c Δ → susp-ctx Γ ≃c susp-ctx Δ
susp-ty-≃ : A ≃ty B → susp-ty A ≃ty susp-ty B
susp-tm-≃ : s ≃tm t → susp-tm s ≃tm susp-tm t
susp-sub-≃ : σ ≃s τ → susp-sub σ ≃s susp-sub τ

susp-ctx-≃ Emp≃ = refl≃c
susp-ctx-≃ (Add≃ p q) = Add≃ (susp-ctx-≃ p) (susp-ty-≃ q)

susp-ty-≃ (Star≃ x) with x
... | refl = refl≃ty
susp-ty-≃ (Arr≃ q r s) = Arr≃ (susp-tm-≃ q) (susp-ty-≃ r) (susp-tm-≃ s)

susp-tm-≃ (Var≃ p q) = Var≃ (cong suc (cong suc p)) (trans (toℕ-inject₁ (inject₁ _)) (trans (toℕ-inject₁ _) (trans q (sym (trans (toℕ-inject₁ (inject₁ _)) (toℕ-inject₁ _))))))
susp-tm-≃ (Coh≃ q r s) = Coh≃ (susp-ctx-≃ q) (susp-ty-≃ r) (susp-sub-≃ s)

susp-sub-≃ (Null≃ (Star≃ refl)) = refl≃s
susp-sub-≃ (Ext≃ r s) = Ext≃ (susp-sub-≃ r) (susp-tm-≃ s)

↓-≃ : σ ≃s τ → ↓ σ ≃s ↓ τ
↓-≃ (Null≃ (Arr≃ p q r)) = Ext≃ (Ext≃ (Null≃ q) p) r
↓-≃ (Ext≃ q x) = Ext≃ (↓-≃ q) x

↑-≃ : σ ≃s τ → ↑ σ ≃s ↑ τ
↑-≃ (Ext≃ (Ext≃ (Null≃ z) y) x) = Null≃ (Arr≃ y z x)
↑-≃ (Ext≃ p@(Ext≃ (Ext≃ _ _) _) x) = Ext≃ (↑-≃ p) x

sub-action-≃-ty : A ≃ty B → σ ≃s τ → A [ σ ]ty ≃ty B [ τ ]ty
sub-action-≃-tm : {σ : Sub n m A} → {τ : Sub n′ m′ B} → s ≃tm t → σ ≃s τ → s [ σ ]tm ≃tm t [ τ ]tm
sub-action-≃-sub : σ ≃s σ′ → τ ≃s μ → σ ● τ ≃s σ′ ● μ

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
sub-action-≃-tm {A = s₁ ─⟨ A ⟩⟶ t} {B = s₂ ─⟨ B ⟩⟶ t₁} (Coh≃ p q r) s = sub-action-≃-tm (Coh≃ (susp-ctx-≃ p) (susp-ty-≃ q) (susp-sub-≃ r)) (↓-≃ s)
sub-action-≃-sub (Null≃ x) q = Null≃ (sub-action-≃-ty x q)
sub-action-≃-sub (Ext≃ p x) q = Ext≃ (sub-action-≃-sub p q) (sub-action-≃-tm x q)

↓-wk : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → ↓ (wk-sub σ) ≃s wk-sub (↓ σ)
↓-wk ⟨ A ⟩′ = refl≃s
↓-wk ⟨ σ , t ⟩ = Ext≃ (↓-wk σ) refl≃tm

↑-wk : (σ : Sub (2 + n) m A) → ↑ (wk-sub σ) ≃s wk-sub (↑ σ)
↑-wk ⟨ ⟨ ⟨ A ⟩′ , v ⟩ , u ⟩ = Null≃ refl≃ty
↑-wk ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , u ⟩ = Ext≃ (↑-wk σ) refl≃tm

↑-↓ : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → ↑ (↓ σ) ≃s σ
↑-↓ ⟨ A ⟩′ = refl≃s
↑-↓ ⟨ ⟨ A ⟩′ , t ⟩ = refl≃s
↑-↓ ⟨ ⟨ ⟨ A ⟩′ , s ⟩ , t ⟩ = refl≃s
↑-↓ ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , t ⟩ = Ext≃ (↑-↓ σ) refl≃tm

apply-wk-sub-ty-≃ : (B : Ty n) → (σ : Sub n m A) → B [ wk-sub σ ]ty ≃ty wk-ty (B [ σ ]ty)
apply-wk-sub-tm-≃ : (t : Tm n) → (σ : Sub n m A) → t [ wk-sub σ ]tm ≃tm wk-tm (t [ σ ]tm)
apply-wk-sub-sub-≃ : (τ : Sub l n B) → (σ : Sub n m A) → τ ● wk-sub σ ≃s wk-sub (τ ● σ)

apply-wk-sub-ty-≃ ⋆ σ = refl≃ty
apply-wk-sub-ty-≃ (s ─⟨ B ⟩⟶ t) σ = Arr≃ (apply-wk-sub-tm-≃ s σ) (apply-wk-sub-ty-≃ B σ) (apply-wk-sub-tm-≃ t σ)

apply-wk-sub-tm-≃ (Var zero) ⟨ σ , t ⟩ = refl≃tm
apply-wk-sub-tm-≃ (Var (suc i)) ⟨ σ , t ⟩ = apply-wk-sub-tm-≃ (Var i) σ
apply-wk-sub-tm-≃ {A = ⋆} (Coh T B τ) σ = Coh≃ refl≃c refl≃ty (apply-wk-sub-sub-≃ τ σ)
apply-wk-sub-tm-≃ {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) σ = begin
  < Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ ↓ (wk-sub σ) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ)}) (↓-wk σ) ⟩
  < Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ wk-sub (↓ σ) ]tm >tm
    ≈⟨ apply-wk-sub-tm-≃ (Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ)) (↓ σ) ⟩
  < wk-tm (Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ ↓ σ ]tm) >tm ∎
  where
    open Reasoning tm-setoid

apply-wk-sub-sub-≃ ⟨ A ⟩′ σ = Null≃ (apply-wk-sub-ty-≃ _ σ)
apply-wk-sub-sub-≃ ⟨ τ , t ⟩ σ = Ext≃ (apply-wk-sub-sub-≃ τ σ) (apply-wk-sub-tm-≃ t σ)

susp-ty-wk : (B : Ty n) → susp-ty (wk-ty B) ≃ty wk-ty (susp-ty B)
susp-tm-wk : (t : Tm n) → susp-tm (wk-tm t) ≃tm wk-tm (susp-tm t)
susp-sub-wk : (σ : Sub n m ⋆) → susp-sub (wk-sub σ) ≃s wk-sub (susp-sub σ)

susp-ty-wk ⋆ = Arr≃ refl≃tm (Star≃ refl) refl≃tm
susp-ty-wk (s ─⟨ B ⟩⟶ t) = Arr≃ (susp-tm-wk s) (susp-ty-wk B) (susp-tm-wk t)

susp-tm-wk (Var i) = refl≃tm
susp-tm-wk (Coh Δ A σ) = Coh≃ refl≃c refl≃ty (susp-sub-wk σ)

susp-sub-wk ⟨ A ⟩′ = refl≃s
susp-sub-wk ⟨ σ , t ⟩ = Ext≃ (susp-sub-wk σ) (susp-tm-wk t)

apply-sub-wk-ty-≃ : (B : Ty n) → (σ : Sub (suc n) m A) → (wk-ty B) [ σ ]ty ≃ty B [ sub-proj₁ σ ]ty
apply-sub-wk-tm-≃ : (s : Tm n) → (σ : Sub (suc n) m A) → (wk-tm s) [ σ ]tm ≃tm s [ sub-proj₁ σ ]tm
apply-sub-wk-sub-≃ : (τ : Sub l n B) → (σ : Sub (suc n) m A) → wk-sub τ ● σ ≃s τ ● sub-proj₁ σ

apply-sub-wk-ty-≃ ⋆ σ = refl≃ty
apply-sub-wk-ty-≃ (s ─⟨ B ⟩⟶ t) σ = Arr≃ (apply-sub-wk-tm-≃ s σ) (apply-sub-wk-ty-≃ B σ) (apply-sub-wk-tm-≃ t σ)

apply-sub-wk-tm-≃ (Var i) σ = refl≃tm
apply-sub-wk-tm-≃ {A = ⋆} (Coh Δ B τ) σ = Coh≃ refl≃c refl≃ty (apply-sub-wk-sub-≃ τ σ)
apply-sub-wk-tm-≃ {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) ⟨ σ , u ⟩ = begin
  < susp-tm (wk-tm (Coh Δ B τ)) [ ⟨ ↓ σ , u ⟩ ]tm >tm
    ≈⟨ sub-action-≃-tm (susp-tm-wk (Coh Δ B τ)) (refl≃s {σ = ⟨ ↓ σ , u ⟩}) ⟩
  < wk-tm (susp-tm (Coh Δ B τ)) [ ⟨ ↓ σ , u ⟩ ]tm >tm
    ≈⟨ apply-sub-wk-tm-≃ (susp-tm (Coh Δ B τ)) ⟨ ↓ σ , u ⟩ ⟩
  < Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ ↓ σ ]tm >tm ∎
  where
    open Reasoning tm-setoid

apply-sub-wk-sub-≃ {B = B} ⟨ A ⟩′ σ = Null≃ (apply-sub-wk-ty-≃ B σ)
apply-sub-wk-sub-≃ ⟨ τ , t ⟩ σ = Ext≃ (apply-sub-wk-sub-≃ τ σ) (apply-sub-wk-tm-≃ t σ)

‼-≃ : (i : Fin (ctxLength Γ)) → (j : Fin (ctxLength Δ)) → toℕ i ≡ toℕ j → Γ ≃c Δ → Γ ‼ i ≃ty Δ ‼ j
‼-≃ zero zero p (Add≃ q x) = wk-ty-≃ x
‼-≃ (suc i) (suc j) p (Add≃ q x) = wk-ty-≃ (‼-≃ i j (cong pred p) q)

≃c-dec : (Γ : Ctx n) → (Γ′ : Ctx m) → Dec (Γ ≃c Γ′)
≃ty-dec : (A : Ty n) → (B : Ty m) → Dec (A ≃ty B)
≃tm-dec : (s : Tm n) → (t : Tm m) → Dec (s ≃tm t)
≃s-dec : (σ : Sub n m A) → (τ : Sub n′ m′ B) → Dec (σ ≃s τ)

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
≃tm-dec (Coh Δ A σ) (Coh Δ′ A′ σ′) with ≃c-dec Δ Δ′ | ≃ty-dec A A′ | ≃s-dec σ σ′
... | yes p | yes q | yes r = yes (Coh≃ p q r)
... | yes p | yes q | no r = no λ where (Coh≃ _ _ x) → r x
... | yes p | no q | r = no λ where (Coh≃ _ x _) → q x
... | no p | q | r = no λ where (Coh≃ x _ _) → p x

≃s-dec ⟨ A ⟩′ ⟨ B ⟩′ with ≃ty-dec A B
... | yes p = yes (Null≃ p)
... | no p = no λ where (Null≃ x) → p x
≃s-dec ⟨ A ⟩′ ⟨ τ , t ⟩ = no (λ ())
≃s-dec ⟨ σ , t ⟩ ⟨ B ⟩′ = no (λ ())
≃s-dec ⟨ σ , s ⟩ ⟨ τ , t ⟩ with ≃s-dec σ τ | ≃tm-dec s t
... | yes p | yes q = yes (Ext≃ p q)
... | yes p | no q = no (λ where (Ext≃ _ x) → q x)
... | no p | q = no (λ where (Ext≃ x _) → p x)

ctx-dec : DecidableEquality (Ctx n)
ctx-dec Γ Δ = map (mk⇔ ≃c-to-≡ reflexive≃c) (≃c-dec Γ Δ)

ty-dec : DecidableEquality (Ty n)
ty-dec A B = map (mk⇔ ≃ty-to-≡ reflexive≃ty) (≃ty-dec A B)

tm-dec : DecidableEquality (Tm n)
tm-dec s t = map (mk⇔ ≃tm-to-≡ reflexive≃tm) (≃tm-dec s t)

sub-dec : DecidableEquality (Sub n m A)
sub-dec σ τ = map (mk⇔ ≃s-to-≡ reflexive≃s) (≃s-dec σ τ)

≃c-irrel : Irrelevant (Γ ≃c Δ)
≃ty-irrel : Irrelevant (A ≃ty B)
≃tm-irrel : Irrelevant (s ≃tm t)
≃s-irrel : Irrelevant (σ ≃s τ)

≃c-irrel Emp≃ Emp≃ = refl
≃c-irrel (Add≃ p x) (Add≃ q y) = cong₂ Add≃ (≃c-irrel p q) (≃ty-irrel x y)

≃ty-irrel (Star≃ x) (Star≃ y) = cong Star≃ (≡-irrelevant x y)
≃ty-irrel (Arr≃ p q r) (Arr≃ p′ q′ r′) = lem (≃tm-irrel p p′) (≃ty-irrel q q′) (≃tm-irrel r r′)
  where
    lem : {a b : s ≃tm s′} {c d : A ≃ty A′} {e f : t ≃tm t′} → a ≡ b → c ≡ d → e ≡ f → Arr≃ a c e ≡ Arr≃ b d f
    lem refl refl refl = refl

≃tm-irrel (Var≃ p q) (Var≃ p′ q′) = cong₂ Var≃ (≡-irrelevant p p′) (≡-irrelevant q q′)
≃tm-irrel (Coh≃ p q r) (Coh≃ p′ q′ r′) = lem (≃c-irrel p p′) (≃ty-irrel q q′) (≃s-irrel r r′)
  where
    lem : {a b : Δ ≃c Δ′} {c d : A ≃ty A′} {e f : σ ≃s τ} → a ≡ b → c ≡ d → e ≡ f → Coh≃ a c e ≡ Coh≃ b d f
    lem refl refl refl = refl

≃s-irrel (Null≃ x) (Null≃ y) = cong Null≃ (≃ty-irrel x y)
≃s-irrel (Ext≃ p x) (Ext≃ q y) = cong₂ Ext≃ (≃s-irrel p q) (≃tm-irrel x y)

-- categorical properties

id-left-unit : (σ : Sub n m A) → idSub ● σ ≃s σ
id-left-unit ⟨ A ⟩′ = refl≃s
id-left-unit ⟨ σ , t ⟩ = Ext≃ (trans≃s (apply-sub-wk-sub-≃ idSub ⟨ σ , t ⟩) (id-left-unit σ)) refl≃tm

id-right-unit : (σ : Sub m n A) → σ ● idSub ≃s σ
id-on-ty : (B : Ty m) → B [ idSub ]ty ≃ty B
id-on-tm : (t : Tm m) → t [ idSub ]tm ≃tm t

id-right-unit ⟨ A ⟩′ = Null≃ (id-on-ty _)
id-right-unit ⟨ σ , t ⟩ = Ext≃ (id-right-unit σ) (id-on-tm t)

id-on-ty ⋆ = Star≃ refl
id-on-ty (s ─⟨ B ⟩⟶ t) = Arr≃ (id-on-tm s) (id-on-ty B) (id-on-tm t)

id-on-tm (Var i) = lem i
  where
    lem : (i : Fin m) → Var i [ idSub ]tm ≃tm Var i
    lem {m = suc m} zero = refl≃tm
    lem {m = suc m} (suc i) = trans≃tm (apply-wk-sub-tm-≃ (Var i) idSub) (wk-tm-≃ (lem i))
id-on-tm (Coh Δ A σ) = Coh≃ refl≃c refl≃ty (id-right-unit σ)

idSub-≃ : (n ≡ m) → idSub {n = n} ≃s idSub {n = m}
idSub-≃ refl = refl≃s

susp-sub-preserve-get-fst : (σ : Sub n m ⋆) → get-fst {n = m} ≃tm get-fst [ susp-sub σ ]tm
susp-sub-preserve-get-fst ⟨ _ ⟩′ = refl≃tm
susp-sub-preserve-get-fst ⟨ σ , t ⟩ = susp-sub-preserve-get-fst σ

susp-sub-preserve-get-snd : (σ : Sub n m ⋆) → get-snd {n = m} ≃tm get-snd [ susp-sub σ ]tm
susp-sub-preserve-get-snd ⟨ _ ⟩′ = refl≃tm
susp-sub-preserve-get-snd ⟨ σ , t ⟩ = susp-sub-preserve-get-snd σ

susp-functorial : (σ : Sub m n ⋆) → (τ : Sub n l ⋆) → susp-sub (σ ● τ) ≃s susp-sub σ ● susp-sub τ
susp-functorial-tm : (σ : Sub m l ⋆) → (t : Tm m) → susp-tm (t [ σ ]tm) ≃tm susp-tm t [ susp-sub σ ]tm
susp-functorial-ty : (σ : Sub m l ⋆) → (A : Ty m) → susp-ty (A [ σ ]ty) ≃ty susp-ty A [ susp-sub σ ]ty

susp-functorial ⟨ _ ⟩′ τ = Ext≃ (Ext≃ refl≃s (susp-sub-preserve-get-fst τ)) (susp-sub-preserve-get-snd τ)
susp-functorial ⟨ σ , t ⟩ τ = Ext≃ (susp-functorial σ τ) (susp-functorial-tm τ t)

susp-functorial-tm σ (Var i) = lem σ i
  where
    lem : (σ : Sub n m ⋆) → (i : Fin n) → susp-tm (Var i [ σ ]tm) ≃tm (Var (inject₁ (inject₁ i)) [ susp-sub σ ]tm)
    lem ⟨ σ , t ⟩ zero = refl≃tm
    lem ⟨ σ , t ⟩ (suc i) = lem σ i
susp-functorial-tm σ (Coh Δ A τ) = Coh≃ refl≃c refl≃ty (susp-functorial τ σ)

susp-functorial-ty σ ⋆ = Arr≃ (susp-sub-preserve-get-fst σ) (Star≃ refl) (susp-sub-preserve-get-snd σ)
susp-functorial-ty σ (s ─⟨ A ⟩⟶ t) = Arr≃ (susp-functorial-tm σ s) (susp-functorial-ty σ A) (susp-functorial-tm σ t)

↓-comp : (τ : Sub m l ⋆) → (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → ↓ (τ ● σ) ≃s susp-sub τ ● ↓ σ
↓-comp-tm : (u : Tm l) → (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → susp-tm u [ ↓ σ ]tm ≃tm u [ σ ]tm
↓-comp-ty : (B : Ty l) → (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → susp-ty B [ ↓ σ ]ty ≃ty B [ σ ]ty
↓-fst : (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → get-fst [ ↓ σ ]tm ≃tm s
↓-snd : (σ : Sub l o (s ─⟨ A ⟩⟶ t)) → get-snd [ ↓ σ ]tm ≃tm t

↓-comp ⟨ _ ⟩′ σ = sym≃s (Ext≃ (Ext≃ refl≃s (↓-fst σ)) (↓-snd σ))
↓-comp ⟨ τ , u ⟩ σ = Ext≃ (↓-comp τ σ) (sym≃tm (↓-comp-tm u σ))

↓-comp-tm (Var zero) ⟨ σ , t ⟩ = refl≃tm
↓-comp-tm (Var (suc i)) ⟨ σ , t ⟩ = ↓-comp-tm (Var i) σ
↓-comp-tm (Coh S B τ) σ = refl≃tm

↓-comp-ty ⋆ σ = Arr≃ (↓-fst σ) refl≃ty (↓-snd σ)
↓-comp-ty (s ─⟨ B ⟩⟶ t) σ = Arr≃ (↓-comp-tm s σ) (↓-comp-ty B σ) (↓-comp-tm t σ)

↓-fst ⟨ _ ⟩′ = refl≃tm
↓-fst ⟨ σ , u ⟩ = ↓-fst σ

↓-snd ⟨ _ ⟩′ = refl≃tm
↓-snd ⟨ σ , u ⟩ = ↓-snd σ

↓-comp-higher : (τ : Sub m l (s′ ─⟨ B ⟩⟶ t′)) → (σ : Sub l o A) → ↓ (τ ● σ) ≃s ↓ τ ● σ
↓-comp-higher ⟨ _ ⟩′ σ = refl≃s
↓-comp-higher ⟨ τ , t ⟩ σ = Ext≃ (↓-comp-higher τ σ) refl≃tm

●-assoc : (σ : Sub m′ m A) → (τ : Sub m n B) → (μ : Sub n l C) → σ ● (τ ● μ) ≃s (σ ● τ) ● μ
assoc-tm : (σ : Sub m n A) → (τ : Sub n l B) → (t : Tm m) → t [ σ ● τ ]tm ≃tm (t [ σ ]tm) [ τ ]tm
assoc-ty : (σ : Sub m n C) → (τ : Sub n l B) → (A : Ty m) → A [ σ ● τ ]ty ≃ty (A [ σ ]ty) [ τ ]ty

●-assoc ⟨ _ ⟩′ τ μ = Null≃ (assoc-ty τ μ _)
●-assoc ⟨ σ , t ⟩ τ μ = Ext≃ (●-assoc σ τ μ) (assoc-tm τ μ t)

assoc-tm σ τ (Var i) = lem σ τ i
  where
    lem : (σ : Sub m n A) → (τ : Sub n l B) → (i : Fin m) → Var i [ σ ● τ ]tm ≃tm (Var i [ σ ]tm) [ τ ]tm
    lem ⟨ σ , t ⟩ τ zero = refl≃tm
    lem ⟨ σ , t ⟩ τ (suc i) = lem σ τ i
assoc-tm {A = ⋆} {B = ⋆} σ τ (Coh Δ C μ) = Coh≃ refl≃c refl≃ty (●-assoc μ σ τ)
assoc-tm {A = ⋆} {B = s ─⟨ B ⟩⟶ t} σ τ (Coh Δ C μ) = begin
  < Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ) [ ↓ (σ ● τ) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ)}) (↓-comp σ τ) ⟩
  < Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ) [ susp-sub σ ● ↓ τ ]tm >tm
    ≈⟨ assoc-tm (susp-sub σ) (↓ τ) (Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ)) ⟩
  < Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ ● susp-sub σ) [ ↓ τ ]tm >tm
    ≈˘⟨ sub-action-≃-tm (Coh≃ refl≃c refl≃ty (susp-functorial μ σ)) (refl≃s {σ = ↓ τ}) ⟩
  < Coh (susp-ctx Δ) (susp-ty C) (susp-sub (μ ● σ)) [ ↓ τ ]tm >tm ∎
  where
    open Reasoning tm-setoid
assoc-tm {A = s′ ─⟨ A ⟩⟶ t′} σ τ (Coh Δ C μ) = begin
  < Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ) [ ↓ (σ ● τ) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ)}) (↓-comp-higher σ τ) ⟩
  < Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ) [ ↓ σ ● τ ]tm >tm
    ≈⟨ assoc-tm (↓ σ) τ (Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ)) ⟩
  < Coh (susp-ctx Δ) (susp-ty C) (susp-sub μ) [ ↓ σ ]tm [ τ ]tm >tm ∎
  where
    open Reasoning tm-setoid

assoc-ty σ τ ⋆ = refl≃ty
assoc-ty σ τ (s ─⟨ A ⟩⟶ t) = Arr≃ (assoc-tm σ τ s) (assoc-ty σ τ A) (assoc-tm σ τ t)

-- Equal contexts are iso

idSub≃ : Γ ≃c Δ → Sub (ctxLength Γ) (ctxLength Δ) ⋆
idSub≃ Emp≃ = ⟨ ⋆ ⟩′
idSub≃ (Add≃ p x) = ⟨ (wk-sub (idSub≃ p)) , 0V ⟩

idSub≃-on-ty : (p : Γ ≃c Δ) → (A : Ty (ctxLength Γ)) → A [ idSub≃ p ]ty ≃ty A
idSub≃-on-tm : (p : Γ ≃c Δ) → (s : Tm (ctxLength Γ)) → s [ idSub≃ p ]tm ≃tm s
idSub≃-on-sub : (p : Γ ≃c Δ) → (σ : Sub n (ctxLength Γ) A) → σ ● idSub≃ p ≃s σ

idSub≃-on-ty p ⋆ = Star≃ (sym (≃c-preserve-length p))
idSub≃-on-ty p (s ─⟨ A ⟩⟶ t) = Arr≃ (idSub≃-on-tm p s) (idSub≃-on-ty p A) (idSub≃-on-tm p t)

idSub≃-on-tm p (Var i) = lem p i
  where
    lem : (p : Γ ≃c Δ) → (i : Fin (ctxLength Γ)) → Var i [ idSub≃ p ]tm ≃tm Var {n = ctxLength Γ} i
    lem (Add≃ p x) zero = Var≃ (cong suc (sym (≃c-preserve-length p))) refl
    lem (Add≃ p x) (suc i) = trans≃tm (apply-wk-sub-tm-≃ (Var i) (idSub≃ p)) (wk-tm-≃ (lem p i))
idSub≃-on-tm p (Coh Δ A σ) = Coh≃ refl≃c refl≃ty (idSub≃-on-sub p σ)

idSub≃-on-sub p ⟨ _ ⟩′ = Null≃ (idSub≃-on-ty p _)
idSub≃-on-sub p ⟨ σ , t ⟩ = Ext≃ (idSub≃-on-sub p σ) (idSub≃-on-tm p t)

idSub≃-left-unit : (p : Γ ≃c Δ) → (σ : Sub (ctxLength Δ) n A) → idSub≃ p ● σ ≃s σ
idSub≃-left-unit Emp≃ ⟨ _ ⟩′ = refl≃s
idSub≃-left-unit (Add≃ p x) ⟨ σ , t ⟩ = Ext≃ (trans≃s (apply-sub-wk-sub-≃ (idSub≃ p) ⟨ σ , t ⟩) (idSub≃-left-unit p σ)) refl≃tm

idSub≃-functorial : (p : Γ ≃c Δ) → (q : Δ ≃c Υ) → idSub≃ p ● idSub≃ q ≃s idSub≃ (trans≃c p q)
idSub≃-functorial Emp≃ Emp≃ = refl≃s
idSub≃-functorial (Add≃ p x) (Add≃ q y) = Ext≃ lem refl≃tm
  where
    lem : (wk-sub (idSub≃ p) ● idSub≃ (Add≃ q y)) ≃s
            wk-sub (idSub≃ (trans≃c p q))
    lem = trans≃s (apply-sub-wk-sub-≃ (idSub≃ p) (idSub≃ (Add≃ q y)))
                  (trans≃s (apply-wk-sub-sub-≃ (idSub≃ p) (idSub≃ q))
                  (wk-sub-≃ (idSub≃-functorial p q)))

idSub≃-fst-var : {Γ : Ctx (suc n)} → {Δ : Ctx (suc m)} → (p : Γ ≃c Δ) → Var (fromℕ n) [ idSub≃ p ]tm ≃tm Var (fromℕ m)
idSub≃-fst-var (Add≃ Emp≃ x) = refl≃tm
idSub≃-fst-var (Add≃ (Add≃ p y) x) = trans≃tm (apply-wk-sub-tm-≃ (Var (fromℕ _)) (idSub≃ (Add≃ p y))) (wk-tm-≃ (idSub≃-fst-var (Add≃ p y)))

idSub≃-snd-var : {Γ : Ctx (suc (suc n))} → {Δ : Ctx (suc (suc m))} → (p : Γ ≃c Δ) → Var (inject₁ (fromℕ n)) [ idSub≃ p ]tm ≃tm Var (inject₁ (fromℕ m))
idSub≃-snd-var (Add≃ (Add≃ Emp≃ y) x) = refl≃tm
idSub≃-snd-var (Add≃ (Add≃ (Add≃ p z) y) x) = trans≃tm (apply-wk-sub-tm-≃ (Var (inject₁ (fromℕ _))) (idSub≃ (Add≃ (Add≃ p z) y))) (wk-tm-≃ (idSub≃-snd-var (Add≃ (Add≃ p z) y)))

idSub-id : {Γ Δ : Ctx n} → (p : Γ ≃c Δ) → idSub≃ p ≃s idSub {n}
idSub-id Emp≃ = refl≃s
idSub-id (Add≃ p x) = Ext≃ (wk-sub-≃ (idSub-id p)) refl≃tm

⋆-is-only-0-d-ty : {A : Ty n} → .⦃ IsZero (ty-dim A) ⦄ → A ≃ty ⋆ {n = n}
⋆-is-only-0-d-ty {A = ⋆} = Star≃ refl

⋆-is-only-ty-in-empty-context : (A : Ty 0) → A ≃ty ⋆ {n = 0}
⋆-is-only-ty-in-empty-context ⋆ = refl≃ty
⋆-is-only-ty-in-empty-context (s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)

fromℕ-‼ : (Γ : Ctx (suc n)) → Γ ‼ fromℕ _ ≃ty ⋆ {n = suc n}
fromℕ-‼ {n = zero} (Γ , A) = wk-ty-≃ (⋆-is-only-ty-in-empty-context A)
fromℕ-‼ {n = suc n} (Γ , A) = wk-ty-≃ (fromℕ-‼ Γ)

wk-ty-inj : wk-ty A ≃ty wk-ty B → A ≃ty B
wk-tm-inj : wk-tm s ≃tm wk-tm t → s ≃tm t
wk-sub-inj : wk-sub σ ≃s wk-sub τ → σ ≃s τ

wk-ty-inj {A = ⋆} {B = ⋆} (Star≃ refl) = refl≃ty
wk-ty-inj {A = s ─⟨ A ⟩⟶ t} {B = s′ ─⟨ B ⟩⟶ t′} (Arr≃ p q r) = Arr≃ (wk-tm-inj p) (wk-ty-inj q) (wk-tm-inj r)

wk-tm-inj {s = Var i} {t = Var j} (Var≃ refl p) = Var≃ refl (cong pred p)
wk-tm-inj {s = Coh Δ A σ} {t = Coh Δ′ A′ σ′} (Coh≃ p q r) = Coh≃ p q (wk-sub-inj r)

wk-sub-inj {σ = ⟨ _ ⟩′} {τ = ⟨ _ ⟩′} (Null≃ x) = Null≃ (wk-ty-inj x)
wk-sub-inj {σ = ⟨ σ , t ⟩} {τ = ⟨ τ , s ⟩} (Ext≃ p q) = Ext≃ (wk-sub-inj p) (wk-tm-inj q)

replaceSub-wk : (σ : Sub (1 + n) m A) → (t : Tm m) → wk-sub (replaceSub σ t) ≃s replaceSub (wk-sub σ) (wk-tm t)
replaceSub-wk ⟨ σ , _ ⟩ t = refl≃s

apply-replaceSub-wk-ty : (A : Ty n) → (σ : Sub (1 + n) m B) → (t : Tm m) → wk-ty A [ replaceSub σ t ]ty ≃ty wk-ty A [ σ ]ty
apply-replaceSub-wk-ty A ⟨ σ , s ⟩ t = begin
  < wk-ty A [ ⟨ σ , t ⟩ ]ty >ty
    ≈⟨ apply-sub-wk-ty-≃ A ⟨ σ , t ⟩ ⟩
  < A [ σ ]ty >ty
    ≈˘⟨ apply-sub-wk-ty-≃ A ⟨ σ , s ⟩ ⟩
  < wk-ty A [ ⟨ σ , s ⟩ ]ty >ty ∎
  where
    open Reasoning ty-setoid

susp-ty-is-not-⋆ : susp-ty A ≃ty (⋆ {n = n}) → ⊥
susp-ty-is-not-⋆ {A = ⋆} ()
susp-ty-is-not-⋆ {A = s ─⟨ A ⟩⟶ t} ()

susp-tm-proj : susp-tm s ≃tm susp-tm t → s ≃tm t
susp-ty-proj : susp-ty A ≃ty susp-ty B → A ≃ty B
susp-ctx-proj : susp-ctx Γ ≃c susp-ctx Δ → Γ ≃c Δ
susp-sub-proj : susp-sub σ ≃s susp-sub τ → σ ≃s τ

susp-tm-proj {s = Var i} {t = Var j} (Var≃ p q) = Var≃ (cong (_∸ 2) p) (begin
  toℕ i
    ≡˘⟨ toℕ-inject₁ i ⟩
  toℕ (inject₁ i)
    ≡˘⟨ toℕ-inject₁ (inject₁ i) ⟩
  toℕ (inject₁ (inject₁ i))
    ≡⟨ q ⟩
  toℕ (inject₁ (inject₁ j))
    ≡⟨ toℕ-inject₁ (inject₁ j) ⟩
  toℕ (inject₁ j)
    ≡⟨ toℕ-inject₁ j ⟩
  toℕ j ∎)
  where
    open ≡-Reasoning
susp-tm-proj {s = Coh Γ A σ} {t = Coh Δ B τ} (Coh≃ p q r)
  = Coh≃ (susp-ctx-proj p) (susp-ty-proj q) (susp-sub-proj r)

susp-ty-proj {A = ⋆} {B = ⋆} (Arr≃ _ (Star≃ x) _) = Star≃ (cong (_∸ 2) x)
susp-ty-proj {A = ⋆} {B = s ─⟨ B ⟩⟶ t} (Arr≃ _ p _) = ⊥-elim (susp-ty-is-not-⋆ (sym≃ty p))
susp-ty-proj {A = s ─⟨ A ⟩⟶ t} {B = ⋆} (Arr≃ _ p _) = ⊥-elim (susp-ty-is-not-⋆ p)
susp-ty-proj {A = s ─⟨ A ⟩⟶ t} {B = s′ ─⟨ B ⟩⟶ t′} (Arr≃ p q r)
  = Arr≃ (susp-tm-proj p) (susp-ty-proj q) (susp-tm-proj r)

susp-ctx-proj {Γ = ∅} {Δ = ∅} p = Emp≃
susp-ctx-proj {Γ = ∅} {Δ = ∅ , _} (Add≃ (Add≃ () _) _)
susp-ctx-proj {Γ = ∅} {Δ = Δ , _ , _} (Add≃ (Add≃ () _) _)
susp-ctx-proj {Γ = Γ , A} {Δ = Δ , B} (Add≃ p q) = Add≃ (susp-ctx-proj p) (susp-ty-proj q)
susp-ctx-proj {Γ = ∅ , _} {Δ = ∅} (Add≃ (Add≃ () _) _)
susp-ctx-proj {Γ = Γ , _ , _} {Δ = ∅} (Add≃ (Add≃ () _) _)

susp-sub-proj {σ = ⟨ _ ⟩′} {τ = ⟨ _ ⟩′} (Ext≃ (Ext≃ (Null≃ (Star≃ x)) _) _) = Null≃ (Star≃ (cong (_∸ 2) x))
susp-sub-proj {σ = ⟨ _ ⟩′} {τ = ⟨ ⟨ _ ⟩′ , _ ⟩} (Ext≃ (Ext≃ () _) _)
susp-sub-proj {σ = ⟨ _ ⟩′} {τ = ⟨ ⟨ τ , _ ⟩ , _ ⟩} (Ext≃ (Ext≃ () _) _)
susp-sub-proj {σ = ⟨ σ , t ⟩} {τ = ⟨ τ , t₁ ⟩} (Ext≃ p q) = Ext≃ (susp-sub-proj p) (susp-tm-proj q)
susp-sub-proj {σ = ⟨ ⟨ _ ⟩′ , _ ⟩} {τ = ⟨ _ ⟩′} (Ext≃ (Ext≃ () _) _)
susp-sub-proj {σ = ⟨ ⟨ σ , _ ⟩ , _ ⟩} {τ = ⟨ _ ⟩′} (Ext≃ (Ext≃ () _) _)
