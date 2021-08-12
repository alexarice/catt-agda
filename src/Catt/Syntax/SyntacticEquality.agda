{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax.SyntacticEquality where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc;toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Relation.Binary.PropositionalEquality

data _≃c_ : Ctx n → Ctx m → Set
data _≃ty_ : Ty Γ n → Ty Γ′ m → Set
data _≃tm_ : Tm Γ n → Tm Γ′ m → Set
data _≃s_ : Sub Γ Δ → Sub Γ′ Δ′ → Set

data _≃c_ where
  Emp≃ : ∅ ≃c ∅
  Add≃ : Γ ≃c Γ′ → A ≃ty A′ → (Γ , A) ≃c (Γ′ , A′)

data _≃ty_ where
  Star≃ : ⋆ {Γ = Γ} ≃ty ⋆ {Γ = Γ′}
  Arr≃ : s ≃tm s′ → A ≃ty A′ → t ≃tm t′ → s ─⟨ A ⟩⟶ t ≃ty s′ ─⟨ A′ ⟩⟶ t′


data _≃tm_ where
  Var≃ : {i : Fin (ctxLength Γ)} → {j : Fin (ctxLength Γ′)} → toℕ i ≡ toℕ j → Var {Γ = Γ} i ≃tm Var {Γ = Γ′} j
  Coh≃ : .{p : ctx-dim Δ ≤ ty-dim A} → .{q : ctx-dim Δ′ ≤ ty-dim A′} → Δ ≃c Δ′ → A ≃ty A′ → σ ≃s σ′ → Coh Δ A p σ ≃tm Coh Δ′ A′ q σ′

data _≃s_ where
  Null≃ : ⟨⟩ {Δ = Δ} ≃s ⟨⟩ {Δ = Δ′}
  Ext≃ : σ ≃s σ′ → t ≃tm t′ → ⟨_,_⟩ σ {A} t ≃s ⟨_,_⟩ σ′ {A′} t′

refl≃c : Γ ≃c Γ
refl≃ty : A ≃ty A
refl≃tm : s ≃tm s
refl≃s : σ ≃s σ

refl≃c {Γ = ∅} = Emp≃
refl≃c {Γ = Γ , A} = Add≃ refl≃c refl≃ty

refl≃ty {A = ⋆} = Star≃
refl≃ty {A = s ─⟨ A ⟩⟶ t} = Arr≃ refl≃tm refl≃ty refl≃tm

refl≃tm {s = Var i} = Var≃ refl
refl≃tm {s = Coh Δ A x σ} = Coh≃ refl≃c refl≃ty refl≃s

refl≃s {σ = ⟨⟩} = Null≃
refl≃s {σ = ⟨ σ , t ⟩} = Ext≃ refl≃s refl≃tm

sym≃c : Γ ≃c Δ → Δ ≃c Γ
sym≃ty : A ≃ty B → B ≃ty A
sym≃tm : s ≃tm t → t ≃tm s
sym≃s : σ ≃s τ → τ ≃s σ

sym≃c Emp≃ = Emp≃
sym≃c (Add≃ p q) = Add≃ (sym≃c p) (sym≃ty q)

sym≃ty Star≃ = Star≃
sym≃ty (Arr≃ p q r) = Arr≃ (sym≃tm p) (sym≃ty q) (sym≃tm r)

sym≃tm (Var≃ x) = Var≃ (sym x)
sym≃tm (Coh≃ p q r) = Coh≃ (sym≃c p) (sym≃ty q) (sym≃s r)

sym≃s Null≃ = Null≃
sym≃s (Ext≃ p q) = Ext≃ (sym≃s p) (sym≃tm q)

trans≃c : Γ ≃c Δ → Δ ≃c Υ → Γ ≃c Υ
trans≃ty : A ≃ty B → B ≃ty C → A ≃ty C
trans≃tm : s ≃tm t → t ≃tm u → s ≃tm u
trans≃s : σ ≃s τ → τ ≃s μ → σ ≃s μ

trans≃c Emp≃ Emp≃ = Emp≃
trans≃c (Add≃ p q) (Add≃ r s) = Add≃ (trans≃c p r) (trans≃ty q s)

trans≃ty Star≃ Star≃ = Star≃
trans≃ty (Arr≃ p q r) (Arr≃ s t u) = Arr≃ (trans≃tm p s) (trans≃ty q t) (trans≃tm r u)

trans≃tm (Var≃ x) (Var≃ y) = Var≃ (trans x y)
trans≃tm (Coh≃ p q r) (Coh≃ s t u) = Coh≃ (trans≃c p s) (trans≃ty q t) (trans≃s r u)

trans≃s Null≃ Null≃ = Null≃
trans≃s (Ext≃ p q) (Ext≃ r s) = Ext≃ (trans≃s p r) (trans≃tm q s)

reflexive≃c : Γ ≡ Δ → Γ ≃c Δ
reflexive≃c refl = refl≃c

reflexive≃ty : A ≡ B → A ≃ty B
reflexive≃ty refl = refl≃ty

reflexive≃tm : s ≡ t → s ≃tm t
reflexive≃tm refl = refl≃tm

reflexive≃s : σ ≡ τ → σ ≃s τ
reflexive≃s refl = refl≃s

≃ty-preserve-dim : {A : Ty Γ d} → {B : Ty Γ′ d′} → A ≃ty B → d ≡ d′
≃ty-preserve-dim Star≃ = refl
≃ty-preserve-dim (Arr≃ x p x₁) = cong suc (≃ty-preserve-dim p)

≃-preserve-lookupDim : Γ ≃c Γ′ → {i : Fin (ctxLength Γ)} → {j : Fin (ctxLength Γ′)} → toℕ i ≡ toℕ j → lookupDim Γ i ≡ lookupDim Γ′ j
≃-preserve-lookupDim (Add≃ p q) {zero} {zero} r = ≃ty-preserve-dim q
≃-preserve-lookupDim (Add≃ p q) {suc i} {suc j} r = ≃-preserve-lookupDim p (cong pred r)

≃tm-preserve-dim : {s : Tm Γ d} → {t : Tm Γ′ d′} → Γ ≃c Γ′ → s ≃tm t → d ≡ d′
≃tm-preserve-dim p (Var≃ q) = cong suc (≃-preserve-lookupDim p q)
≃tm-preserve-dim p (Coh≃ q r s) = cong suc (≃ty-preserve-dim r)

≃c-preserve-len : {Γ : Ctx n} → {Δ : Ctx m} → Γ ≃c Δ → n ≡ m
≃c-preserve-len Emp≃ = refl
≃c-preserve-len (Add≃ p x) = cong suc (≃c-preserve-len p)

≃c-to-≡ : Γ ≃c Δ → Γ ≡ Δ
≃ty-to-≡ : {A : Ty Γ d} {B : Ty Γ d} → A ≃ty B → A ≡ B
≃ty-to-subst-≡ : {A : Ty Γ d} {B : Ty Γ d′} → (p : A ≃ty B) → (q : d ≡ d′) → subst (Ty Γ) q A ≡ B
≃tm-to-≡ : {s : Tm Γ d} {t : Tm Γ d} → s ≃tm t → s ≡ t
≃tm-to-subst-≡ : {s : Tm Γ d} {t : Tm Γ d′} → (p : s ≃tm t) → (q : d ≡ d′) → subst (Tm Γ) q s ≡ t
≃s-to-≡ : {σ : Sub Γ Δ} → {τ : Sub Γ Δ} → σ ≃s τ → σ ≡ τ


≃c-to-≡ Emp≃ = refl
≃c-to-≡ (Add≃ p q)
  rewrite ≃c-to-≡ p
  = lem (≃ty-preserve-dim q) (≃ty-to-subst-≡ q (≃ty-preserve-dim q))
  where
    lem : {Γ : Ctx n} → {A : Ty Γ d} {B : Ty Γ d′} → (p : d ≡ d′) → subst (Ty Γ) p A ≡ B → Γ , A ≡ Γ , B
    lem refl refl = refl

≃ty-to-≡ Star≃ = refl
≃ty-to-≡ (Arr≃ p q r)
  rewrite ≃tm-to-≡ p
  rewrite ≃ty-to-≡ q
  rewrite ≃tm-to-≡ r = refl

≃ty-to-subst-≡ Star≃ refl = refl
≃ty-to-subst-≡ (Arr≃ p q r) refl
  = arr-equality (≃tm-to-subst-≡ p refl)
                 (≃ty-to-subst-≡ q refl)
                 (≃tm-to-subst-≡ r refl)
  where
    subst-cong : (p : suc n ≡ suc m) → (s : Tm Γ (suc n)) → (t : Tm Γ (suc n)) → (A : Ty Γ n) → subst (Ty Γ) p (s ─⟨ A ⟩⟶ t) ≡ subst (Tm Γ) p s ─⟨ subst (Ty Γ) (cong pred p) A ⟩⟶ subst (Tm Γ) p t
    subst-cong refl s t A = refl

≃tm-to-≡ p = ≃tm-to-subst-≡ p refl

≃tm-to-subst-≡ {Γ = Γ} (Var≃ {i = i} p) q with toℕ-injective p
... | refl = subst (λ - → subst (Tm Γ) - (Var i) ≡ Var i) (≡-irrelevant refl q) refl
≃tm-to-subst-≡ (Coh≃ p q r) refl with cong pred (≃c-preserve-len p)
... | refl
  rewrite ≃c-to-≡ p
  rewrite ≃ty-to-≡ q
  rewrite ≃s-to-≡ r = refl

≃s-to-≡ Null≃ = refl
≃s-to-≡ (Ext≃ p q)
  rewrite ≃s-to-≡ p
  rewrite ≃tm-to-≡ q = refl

⋆-is-only-1-d-ty : {A : Ty Γ 1} → ⋆ {Γ = Δ} ≃ty A
⋆-is-only-1-d-ty {A = ⋆} = Star≃

sub-action-≃-ty : A ≃ty B → A [ σ ]ty ≃ty B [ σ ]ty
sub-action-≃-tm : s ≃tm t → s [ σ ]tm ≃tm t [ σ ]tm
sub-action-≃-sub : τ ≃s μ → σ ∘ τ ≃s σ ∘ μ

sub-action-≃-ty Star≃ = Star≃
sub-action-≃-ty (Arr≃ p q r) = Arr≃ (sub-action-≃-tm p) (sub-action-≃-ty q) (sub-action-≃-tm r)

sub-action-≃-tm (Var≃ x) with toℕ-injective x
... | refl = refl≃tm
sub-action-≃-tm (Coh≃ p q r) = Coh≃ p q (sub-action-≃-sub r)

sub-action-≃-sub Null≃ = Null≃
sub-action-≃-sub (Ext≃ p q) = Ext≃ (sub-action-≃-sub p) (sub-action-≃-tm q)

lift-subbed-ty-≃ : (B : Ty Γ d) → (σ : Sub Γ Δ) → {A : Ty Γ d′} → {t : Tm (Δ , A [ σ ]ty) (suc d′)} → (liftType {A = A} B) [ ⟨ liftSub σ , t ⟩ ]ty ≃ty liftType {A = A [ σ ]ty} (B [ σ ]ty)
lift-subbed-tm-≃ : (s : Tm Γ d) → (σ : Sub Γ Δ) → {A : Ty Γ d′} → {t : Tm (Δ , A [ σ ]ty) (suc d′)} → (liftTerm {A = A} s) [ ⟨ liftSub σ , t ⟩ ]tm ≃tm liftTerm {A = A [ σ ]ty} (s [ σ ]tm)
lift-subbed-sub-≃ : (τ : Sub Υ Γ) → (σ : Sub Γ Δ) → {A : Ty Γ d′} → {t : Tm (Δ , A [ σ ]ty) (suc d′)} → ⟨_,_⟩ (liftSub σ) {A = A} t ∘ liftSub τ ≃s liftSub {A = A [ σ ]ty} (σ ∘ τ)
lift-subbed-var-≃ : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ) → Var i [ liftSub {A = A} σ ]tm ≃tm liftTerm {A = A} (Var i [ σ ]tm)

lift-subbed-ty-≃ ⋆ σ = Star≃
lift-subbed-ty-≃ (s ─⟨ B ⟩⟶ t) σ = Arr≃ (lift-subbed-tm-≃ s σ) (lift-subbed-ty-≃ B σ) (lift-subbed-tm-≃ t σ)

lift-subbed-tm-≃ (Var i) σ = lift-subbed-var-≃ i σ
lift-subbed-tm-≃ (Coh Δ A x τ) σ = Coh≃ refl≃c refl≃ty (lift-subbed-sub-≃ τ σ)

lift-subbed-sub-≃ ⟨⟩ σ = Null≃
lift-subbed-sub-≃ ⟨ τ , t ⟩ σ = Ext≃ (lift-subbed-sub-≃ τ σ) (lift-subbed-tm-≃ t σ)

lift-subbed-var-≃ zero ⟨ σ , t ⟩ = refl≃tm
lift-subbed-var-≃ (suc i) ⟨ σ , t ⟩ = lift-subbed-var-≃ i σ

lift-ty-≃ : B ≃ty C → liftType {A = A} B ≃ty liftType {A = A′} C
lift-tm-≃ : s ≃tm t → liftTerm {A = A} s ≃tm liftTerm {A = A′} t
lift-sub-≃ : σ ≃s τ → liftSub {A = A} σ ≃s liftSub {A = A′} τ

lift-ty-≃ Star≃ = Star≃
lift-ty-≃ (Arr≃ p q r) = Arr≃ (lift-tm-≃ p) (lift-ty-≃ q) (lift-tm-≃ r)

lift-tm-≃ (Var≃ x) = Var≃ (cong suc x)
lift-tm-≃ (Coh≃ p q r) = Coh≃ p q (lift-sub-≃ r)

lift-sub-≃ Null≃ = Null≃
lift-sub-≃ (Ext≃ p q) = Ext≃ (lift-sub-≃ p) (lift-tm-≃ q)
