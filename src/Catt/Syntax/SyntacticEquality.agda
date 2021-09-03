{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Syntax.SyntacticEquality where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Suspension.Base
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc;toℕ;inject₁)
open import Data.Fin.Properties using (toℕ-injective)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Function.Equivalence using (equivalence)
open import Data.Product renaming (_,_ to _,,_) using (Σ; proj₁; proj₂)

data _≃c_ : Ctx → Ctx → Set
data _≃ty_ : Ty Γ → Ty Γ′ → Set
data _≃tm_ : Tm Γ → Tm Γ′ → Set
data _≃s_ : Sub Γ Δ A → Sub Γ′ Δ′ B → Set

data _≃c_ where
  Emp≃ : ∅ ≃c ∅
  Add≃ : Γ ≃c Γ′ → A ≃ty A′ → (Γ , A) ≃c (Γ′ , A′)

data _≃ty_ where
  Star≃ : ⋆ {Γ = Γ} ≃ty ⋆ {Γ = Γ′}
  Arr≃ : s ≃tm s′ → A ≃ty A′ → t ≃tm t′ → s ─⟨ A ⟩⟶ t ≃ty s′ ─⟨ A′ ⟩⟶ t′

data _≃tm_ where
  Var≃ : {i : Fin (ctxLength Γ)} → {j : Fin (ctxLength Γ′)} → toℕ i ≡ toℕ j → Var {Γ = Γ} i ≃tm Var {Γ = Γ′} j
  Coh≃ : Δ ≃c Δ′ → A ≃ty A′ → σ ≃s σ′ → Coh Δ A σ ≃tm Coh Δ′ A′ σ′

data _≃s_ where
  Null≃ : A ≃ty B → ⟨⟩ {Δ = Δ} {A = A} ≃s ⟨⟩ {Δ = Δ′} {A = B}
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
refl≃tm {s = Coh Δ A σ} = Coh≃ refl≃c refl≃ty refl≃s

refl≃s {σ = ⟨⟩} = Null≃ refl≃ty
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

sym≃s (Null≃ x) = (Null≃ (sym≃ty x))
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

trans≃s (Null≃ p) (Null≃ q) = (Null≃ (trans≃ty p q))
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
ctx-setoid = record { Carrier = Ctx
                    ; _≈_ = λ x y → x ≃c y
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

≃ty-preserve-dim : {A : Ty Γ} → {B : Ty Γ′} → A ≃ty B → ty-dim A ≡ ty-dim B
≃ty-preserve-dim Star≃ = refl
≃ty-preserve-dim (Arr≃ x p x₁) = cong suc (≃ty-preserve-dim p)

-- ≃-preserve-lookupDim : Γ ≃c Γ′ → {i : Fin (ctxLength Γ)} → {j : Fin (ctxLength Γ′)} → toℕ i ≡ toℕ j → lookupDim Γ i ≡ lookupDim Γ′ j
-- ≃-preserve-lookupDim (Add≃ p q) {zero} {zero} r = ≃ty-preserve-dim q
-- ≃-preserve-lookupDim (Add≃ p q) {suc i} {suc j} r = ≃-preserve-lookupDim p (cong pred r)

-- ≃tm-preserve-dim : {s : Tm Γ d} → {t : Tm Γ′ d′} → Γ ≃c Γ′ → s ≃tm t → d ≡ d′
-- ≃tm-preserve-dim p (Var≃ q) = cong suc (≃-preserve-lookupDim p q)
-- ≃tm-preserve-dim p (Coh≃ q r s) = cong suc (≃ty-preserve-dim r)

-- ≃c-preserve-len : {Γ : Ctx} → {Δ : Ctx} → Γ ≃c Δ → n ≡ m
-- ≃c-preserve-len Emp≃ = refl
-- ≃c-preserve-len (Add≃ p x) = cong suc (≃c-preserve-len p)

≃s-preserve-ty : {σ : Sub Γ Δ A} → {τ : Sub Γ′ Δ′ B} → σ ≃s τ → A ≃ty B
≃s-preserve-ty (Null≃ x) = x
≃s-preserve-ty (Ext≃ p x) = ≃s-preserve-ty p

≃c-to-≡ : Γ ≃c Δ → Γ ≡ Δ
≃ty-to-≡ : {A : Ty Γ} {B : Ty Γ} → A ≃ty B → A ≡ B
≃tm-to-≡ : {s : Tm Γ} {t : Tm Γ} → s ≃tm t → s ≡ t
≃s-to-≡ : {σ : Sub Γ Δ A} → {τ : Sub Γ Δ A} → σ ≃s τ → σ ≡ τ


≃c-to-≡ Emp≃ = refl
≃c-to-≡ (Add≃ p q)
  rewrite ≃c-to-≡ p
  rewrite ≃ty-to-≡ q = refl
  -- rewrite ≃c-to-≡ p
  -- = lem (≃ty-preserve-dim q) (≃ty-to-subst-≡ q (≃ty-preserve-dim q))
  -- where
  --   lem : {Γ : Ctx n} → {A : Ty Γ d} {B : Ty Γ d′} → (p : d ≡ d′) → subst (Ty Γ) p A ≡ B → Γ , A ≡ Γ , B
  --   lem refl refl = refl

≃ty-to-≡ Star≃ = refl
≃ty-to-≡ (Arr≃ p q r)
  rewrite ≃tm-to-≡ p
  rewrite ≃ty-to-≡ q
  rewrite ≃tm-to-≡ r = refl

≃tm-to-≡ (Var≃ x) with toℕ-injective x
... | refl = refl
≃tm-to-≡ (Coh≃ p q r)
  rewrite ≃c-to-≡ p
  rewrite ≃ty-to-≡ q
  rewrite ≃s-to-≡ r = refl

≃s-to-≡ (Null≃ x) = refl
≃s-to-≡ (Ext≃ p q)
  rewrite ≃s-to-≡ p
  rewrite ≃tm-to-≡ q = refl

-- ⋆-is-only-1-d-ty : {A : Ty Γ} → ⋆ {Γ = Δ} ≃ty A
-- ⋆-is-only-1-d-ty {A = ⋆} = Star≃

lift-ty-≃ : B ≃ty C → liftType {A = A} B ≃ty liftType {A = A′} C
lift-tm-≃ : s ≃tm t → liftTerm {A = A} s ≃tm liftTerm {A = A′} t
lift-sub-≃ : σ ≃s τ → liftSub {A = A} σ ≃s liftSub {A = A′} τ

lift-ty-≃ Star≃ = Star≃
lift-ty-≃ (Arr≃ p q r) = Arr≃ (lift-tm-≃ p) (lift-ty-≃ q) (lift-tm-≃ r)

lift-tm-≃ (Var≃ x) = Var≃ (cong suc x)
lift-tm-≃ (Coh≃ p q r) = Coh≃ p q (lift-sub-≃ r)

lift-sub-≃ (Null≃ p) = Null≃ (lift-ty-≃ p)
lift-sub-≃ (Ext≃ p q) = Ext≃ (lift-sub-≃ p) (lift-tm-≃ q)

convertIndex-inj : (i : Fin (ctxLength Γ)) → (j : Fin (ctxLength Δ)) → toℕ i ≡ toℕ j → toℕ (convertIndex i) ≡ toℕ (convertIndex j)
convertIndex-inj {Γ , A} {Δ , A₁} zero zero p = p
convertIndex-inj {Γ , A} {Δ , A₁} (suc i) (suc j) p = cong suc (convertIndex-inj i j (cong pred p))

susp-ctx-≃ : Γ ≃c Δ → suspCtx Γ ≃c suspCtx Δ
susp-ty-≃ : {A : Ty Γ} {B : Ty Δ} → Γ ≃c Δ → A ≃ty B → suspTy A ≃ty suspTy B
susp-tm-≃ : {s : Tm Γ} {t : Tm Δ} → Γ ≃c Δ → s ≃tm t → suspTm s ≃tm suspTm t
susp-sub-≃ : {σ : Sub Γ Δ ⋆} → {τ : Sub Γ′ Δ′ ⋆} → Δ ≃c Δ′ → σ ≃s τ → suspSub σ ≃s suspSub τ

susp-ctx-≃ Emp≃ = refl≃c
susp-ctx-≃ (Add≃ p q) = Add≃ (susp-ctx-≃ p) (susp-ty-≃ p q)

susp-ty-≃ p Star≃ with ≃c-to-≡ p
... | refl = refl≃ty
susp-ty-≃ p (Arr≃ q r s) = Arr≃ (susp-tm-≃ p q) (susp-ty-≃ p r) (susp-tm-≃ p s)

susp-tm-≃ _ (Var≃ q) = Var≃ (convertIndex-inj _ _ q)
susp-tm-≃ p (Coh≃ q r s) = Coh≃ (susp-ctx-≃ q) (susp-ty-≃ q r) (susp-sub-≃ p s)

susp-sub-≃ p (Null≃ q)with ≃c-to-≡ p
... | refl = refl≃s
susp-sub-≃ p (Ext≃ r s) = Ext≃ (susp-sub-≃ p r) (susp-tm-≃ p s)

susp-ctx-n-≃ : (n ≡ m) → Γ ≃c Δ → susp-ctx-n n Γ ≃c susp-ctx-n m Δ
susp-ctx-n-≃ {n = zero} refl p = p
susp-ctx-n-≃ {n = suc n} refl p = susp-ctx-n-≃ {n = n} refl (susp-ctx-≃ p)

susp-ty-n-≃ : (n ≡ m) → Γ ≃c Δ → {A : Ty Γ} → {B : Ty Δ} → A ≃ty B → susp-ty-n n A ≃ty susp-ty-n m B
susp-ty-n-≃ {n = zero} refl q p = p
susp-ty-n-≃ {n = suc n} refl q p = susp-ty-n-≃ {n = n} refl (susp-ctx-≃ q) (susp-ty-≃ q p)

ty-base-≃ : A ≃ty B → .⦃ _ : TyHeight A (suc d) ⦄ → .⦃ _ : TyHeight B (suc d′) ⦄ → ty-base A ≃ty ty-base B
ty-base-≃ (Arr≃ _ p _) = p

ty-src-≃ : A ≃ty B → .⦃ _ : TyHeight A (suc d) ⦄ → .⦃ _ : TyHeight B (suc d′) ⦄ → ty-src A ≃tm ty-src B
ty-src-≃ (Arr≃ p _ _) = p

ty-tgt-≃ : A ≃ty B → .⦃ _ : TyHeight A (suc d) ⦄ → .⦃ _ : TyHeight B (suc d′) ⦄ → ty-tgt A ≃tm ty-tgt B
ty-tgt-≃ (Arr≃ _ _ p) = p

susp-adjoint-≃ : σ ≃s τ → susp-adjoint σ ≃s susp-adjoint τ
susp-adjoint-≃ (Null≃ (Arr≃ p q r)) = Ext≃ (Ext≃ (Null≃ q) p) r
susp-adjoint-≃ (Ext≃ p x) = Ext≃ (susp-adjoint-≃ p) x

susp-adjoint-full-≃ : {σ : Sub Γ Δ A} → {τ : Sub Γ′ Δ′ B} → σ ≃s τ → susp-adjoint-full σ ≃s susp-adjoint-full τ
susp-adjoint-full-≃ {A = ⋆} {B = ⋆} p = p
susp-adjoint-full-≃ {A = ⋆} {B = s ─⟨ B ⟩⟶ t} p with ≃s-preserve-ty p
... | ()
susp-adjoint-full-≃ {A = s ─⟨ A ⟩⟶ t} {B = ⋆} p with ≃s-preserve-ty p
... | ()
susp-adjoint-full-≃ {A = s ─⟨ A ⟩⟶ t} {B = s₁ ─⟨ B ⟩⟶ t₁} p = susp-adjoint-full-≃ {A = A} {B = B} (susp-adjoint-≃ p)

sub-action-≃-ty : A ≃ty B → σ ≃s τ → A [ σ ]ty ≃ty B [ τ ]ty
sub-action-≃-tm : s ≃tm t → σ ≃s τ → s [ σ ]tm ≃tm t [ τ ]tm
sub-action-≃-sub : τ ≃s μ → σ ≃s σ′ → σ ∘ τ ≃s σ′ ∘ μ

sub-action-≃-ty Star≃ q = ≃s-preserve-ty q
sub-action-≃-ty (Arr≃ p q r) s = Arr≃ (sub-action-≃-tm p s) (sub-action-≃-ty q s) (sub-action-≃-tm r s)

sub-action-≃-tm (Var≃ x) q = lem _ _ x q
  where
    lem : {σ : Sub Γ Δ A} → {τ : Sub Γ′ Δ′ B} → (i : Fin (ctxLength Γ)) → (j : Fin (ctxLength Γ′)) → toℕ i ≡ toℕ j → σ ≃s τ → Var i [ σ ]tm ≃tm Var j [ τ ]tm
    lem zero zero p (Ext≃ q x) = x
    lem (suc i) (suc j) p (Ext≃ q x) = lem i j (cong pred p) q
sub-action-≃-tm (Coh≃ p q r) s
  = Coh≃ (susp-ctx-n-≃ x p) (susp-ty-n-≃ x p q) (susp-adjoint-full-≃ (sub-action-≃-sub r s))
  where
    x : ty-dim _ ≡ ty-dim _
    x = ≃ty-preserve-dim (≃s-preserve-ty s)

sub-action-≃-sub (Null≃ p) q = Null≃ (≃s-preserve-ty q)
sub-action-≃-sub (Ext≃ p x) q = Ext≃ (sub-action-≃-sub p q) (sub-action-≃-tm x q)



lift-subbed-ty-≃ : (B : Ty Γ) → (σ : Sub Γ Δ C) → {A : Ty Γ} → {t : Tm (Δ , A [ σ ]ty)} → (liftType {A = A} B) [ ⟨ liftSub σ , t ⟩ ]ty ≃ty liftType {A = A [ σ ]ty} (B [ σ ]ty)
lift-subbed-tm-≃ : (s : Tm Γ) → (σ : Sub Γ Δ C) → {A : Ty Γ} → {t : Tm (Δ , A [ σ ]ty)} → (liftTerm {A = A} s) [ ⟨ liftSub σ , t ⟩ ]tm ≃tm liftTerm {A = A [ σ ]ty} (s [ σ ]tm)
lift-subbed-sub-≃ : (τ : Sub Υ Γ ⋆) → (σ : Sub Γ Δ C) → {A : Ty Γ} → {t : Tm (Δ , A [ σ ]ty)} → ⟨_,_⟩ (liftSub σ) {A = A} t ∘ liftSub τ ≃s liftSub {A = A [ σ ]ty} (σ ∘ τ)
lift-subbed-var-≃ : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ C) → Var i [ liftSub {A = A} σ ]tm ≃tm liftTerm {A = A} (Var i [ σ ]tm)
lift-ty-dim : (C : Ty Γ) → ty-dim (liftType {A = A} C) ≡ ty-dim C
lift-susp-adjoint-full : (σ : Sub Γ Δ C) → {A : Ty Δ} → susp-adjoint-full (liftSub {A = A} σ) ≃s liftSub {A = A} (susp-adjoint-full σ)
lift-susp-adjoint : (σ : Sub Γ Δ (s ─⟨ C ⟩⟶ t)) → {A : Ty Δ} → (susp-adjoint (liftSub {A = A} σ)) ≃s liftSub {A = A} (susp-adjoint σ)

lift-subbed-ty-≃ ⋆ σ = refl≃ty
lift-subbed-ty-≃ (s ─⟨ B ⟩⟶ t) σ = Arr≃ (lift-subbed-tm-≃ s σ) (lift-subbed-ty-≃ B σ) (lift-subbed-tm-≃ t σ)

lift-subbed-tm-≃ (Var i) σ = lift-subbed-var-≃ i σ
lift-subbed-tm-≃ (Coh Δ A τ) σ {A = B} with lift-ty-dim {A = B [ σ ]ty} (sub-ty σ)
... | p = Coh≃ (susp-ctx-n-≃ p refl≃c) (susp-ty-n-≃ p refl≃c refl≃ty) (trans≃s (susp-adjoint-full-≃ (lift-subbed-sub-≃ τ σ)) (lift-susp-adjoint-full (σ ∘ τ)))

lift-subbed-sub-≃ ⟨⟩ σ = Null≃ refl≃ty
lift-subbed-sub-≃ ⟨ τ , t ⟩ σ = Ext≃ (lift-subbed-sub-≃ τ σ) (lift-subbed-tm-≃ t σ)

lift-subbed-var-≃ zero ⟨ σ , t ⟩ = refl≃tm
lift-subbed-var-≃ (suc i) ⟨ σ , t ⟩ = lift-subbed-var-≃ i σ

lift-ty-dim ⋆ = refl
lift-ty-dim (s ─⟨ C ⟩⟶ t) = cong suc (lift-ty-dim C)

lift-susp-adjoint-full {C = ⋆} σ = refl≃s
lift-susp-adjoint-full {Γ = Γ} {C = s ─⟨ C ⟩⟶ t} σ {A = A} = trans≃s (susp-adjoint-full-≃ (lift-susp-adjoint σ)) (lift-susp-adjoint-full (susp-adjoint σ))

lift-susp-adjoint ⟨⟩ = refl≃s
lift-susp-adjoint ⟨ σ , t ⟩ = Ext≃ (lift-susp-adjoint σ) refl≃tm

apply-lifted-sub-ty-≃ : (B : Ty Γ) → (σ : Sub Γ Δ C) → B [ liftSub {A = A} σ ]ty ≃ty liftType {A = A} (B [ σ ]ty)
apply-lifted-sub-tm-≃ : (t : Tm Γ) → (σ : Sub Γ Δ C) → t [ liftSub {A = A} σ ]tm ≃tm liftTerm {A = A} (t [ σ ]tm)
apply-lifted-sub-sub-≃ : (τ : Sub Υ Γ ⋆) → (σ : Sub Γ Δ C) → liftSub {A = A} σ ∘ τ ≃s liftSub {A = A} (σ ∘ τ)
apply-lifted-sub-var-≃ : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ C) → Var i [ liftSub {A = A} σ ]tm ≃tm liftTerm {A = A} (Var i [ σ ]tm)

apply-lifted-sub-ty-≃ ⋆ σ = refl≃ty
apply-lifted-sub-ty-≃ (s ─⟨ B ⟩⟶ t) σ = Arr≃ (apply-lifted-sub-tm-≃ s σ) (apply-lifted-sub-ty-≃ B σ) (apply-lifted-sub-tm-≃ t σ)

apply-lifted-sub-tm-≃ (Var i) σ = apply-lifted-sub-var-≃ i σ
apply-lifted-sub-tm-≃ {A = A} (Coh Δ B τ) σ with lift-ty-dim {A = A} (sub-ty σ)
... | x = Coh≃ (susp-ctx-n-≃ x refl≃c) (susp-ty-n-≃ x refl≃c refl≃ty) (trans≃s (susp-adjoint-full-≃ (apply-lifted-sub-sub-≃ τ σ)) (lift-susp-adjoint-full (σ ∘ τ)))

apply-lifted-sub-sub-≃ ⟨⟩ σ = Null≃ refl≃ty
apply-lifted-sub-sub-≃ ⟨ τ , t ⟩ σ = Ext≃ (apply-lifted-sub-sub-≃ τ σ) (apply-lifted-sub-tm-≃ t σ)

apply-lifted-sub-var-≃ {Γ = Γ , A} zero ⟨ σ , t ⟩ = refl≃tm
apply-lifted-sub-var-≃ {Γ = Γ , A} (suc i) ⟨ σ , t ⟩ = apply-lifted-sub-var-≃ i σ

‼-≃ : (i : Fin (ctxLength Γ)) → (j : Fin (ctxLength Δ)) → toℕ i ≡ toℕ j → Γ ≃c Δ → Γ ‼ i ≃ty Δ ‼ j
‼-≃ zero zero p (Add≃ q x) = lift-ty-≃ x
‼-≃ (suc i) (suc j) p (Add≃ q x) = lift-ty-≃ (‼-≃ i j (cong pred p) q)

≃c-dec : (Γ : Ctx) → (Γ′ : Ctx) → Dec (Γ ≃c Γ′)
≃ty-dec : (A : Ty Γ) → (B : Ty Γ′) → Dec (A ≃ty B)
≃tm-dec : (s : Tm Γ) → (t : Tm Γ′) → Dec (s ≃tm t)
≃s-dec : (σ : Sub Γ Δ A) → (τ : Sub Γ′ Δ′ B) → Dec (σ ≃s τ)

≃c-dec ∅ ∅ = yes Emp≃
≃c-dec ∅ (Γ′ , A) = no (λ ())
≃c-dec (Γ , A) ∅ = no (λ ())
≃c-dec (Γ , A) (Γ′ , B) with ≃c-dec Γ Γ′ | ≃ty-dec A B
... | yes p | yes q = yes (Add≃ p q)
... | yes p | no q = no (λ where (Add≃ _ x) → q x)
... | no p | q = no λ where (Add≃ x _) → p x

≃ty-dec ⋆ ⋆ = yes Star≃
≃ty-dec ⋆ (s ─⟨ B ⟩⟶ t) = no (λ ())
≃ty-dec (s ─⟨ A ⟩⟶ t) ⋆ = no (λ ())
≃ty-dec (s ─⟨ A ⟩⟶ t) (s′ ─⟨ A′ ⟩⟶ t′) with ≃tm-dec s s′ | ≃ty-dec A A′ | ≃tm-dec t t′
... | yes p | yes q | yes r = yes (Arr≃ p q r)
... | yes p | yes q | no r = no (λ where (Arr≃ _ _ x) → r x)
... | yes p | no q | r = no (λ where (Arr≃ _ x _) → q x)
... | no p | q | r = no (λ where (Arr≃ x _ _) → p x)

≃tm-dec (Var i) (Var j) with toℕ i ≟ toℕ j
... | yes p = yes (Var≃ p)
... | no p = no (λ where (Var≃ x) → p x)
≃tm-dec (Var i) (Coh Δ A σ) = no (λ ())
≃tm-dec (Coh Δ A σ) (Var i) = no (λ ())
≃tm-dec (Coh Δ A σ) (Coh Δ′ A′ σ′) with ≃c-dec Δ Δ′ | ≃ty-dec A A′ | ≃s-dec σ σ′
... | yes p | yes q | yes r = yes (Coh≃ p q r)
... | yes p | yes q | no r = no λ where (Coh≃ _ _ x) → r x
... | yes p | no q | r = no λ where (Coh≃ _ x _) → q x
... | no p | q | r = no λ where (Coh≃ x _ _) → p x

≃s-dec {A = A} {B = B} ⟨⟩ ⟨⟩ with ≃ty-dec A B
... | yes p = yes (Null≃ p)
... | no p = no (λ where (Null≃ x) → p x)
≃s-dec ⟨⟩ ⟨ τ , t ⟩ = no (λ ())
≃s-dec ⟨ σ , t ⟩ ⟨⟩ = no (λ ())
≃s-dec ⟨ σ , s ⟩ ⟨ τ , t ⟩ with ≃s-dec σ τ | ≃tm-dec s t
... | yes p | yes q = yes (Ext≃ p q)
... | yes p | no q = no (λ where (Ext≃ _ x) → q x)
... | no p | q = no (λ where (Ext≃ x _) → p x)


ctx-dec : DecidableEquality (Ctx)
ctx-dec Γ Δ = map (equivalence ≃c-to-≡ reflexive≃c) (≃c-dec Γ Δ)

ty-dec : DecidableEquality (Ty Γ)
ty-dec A B = map (equivalence ≃ty-to-≡ reflexive≃ty) (≃ty-dec A B)

tm-dec : DecidableEquality (Tm Γ)
tm-dec s t = map (equivalence ≃tm-to-≡ reflexive≃tm) (≃tm-dec s t)

sub-dec : DecidableEquality (Sub Γ Δ A)
sub-dec σ τ = map (equivalence ≃s-to-≡ reflexive≃s) (≃s-dec σ τ)

-- categorical properties

id-right-unit : (σ : Sub Γ Δ C) → σ ∘ idSub Γ ≃s σ
lift-sub-comp-lem-sub : (σ : Sub Δ Υ C) → (τ : Sub Γ Δ ⋆) → {A : Ty Δ} → ⟨_,_⟩ σ {A} t ∘ liftSub τ ≃s σ ∘ τ
lift-sub-comp-lem-tm : (σ : Sub Δ Υ C) → (s : Tm Δ) → {A : Ty Δ} → liftTerm s [ ⟨_,_⟩ σ {A} t ]tm ≃tm s [ σ ]tm
lift-sub-comp-lem-ty : (σ : Sub Δ Υ C) → (B : Ty Δ) → {A : Ty Δ} → liftType B [ ⟨_,_⟩ σ {A} t ]ty ≃ty B [ σ ]ty

id-right-unit ⟨⟩ = Null≃ refl≃ty
id-right-unit ⟨ σ , t ⟩ = Ext≃ (trans≃s (lift-sub-comp-lem-sub σ (idSub _)) (id-right-unit σ)) refl≃tm

lift-sub-comp-lem-sub σ ⟨⟩ = Null≃ refl≃ty
lift-sub-comp-lem-sub σ ⟨ τ , t ⟩ = Ext≃ (lift-sub-comp-lem-sub σ τ) (lift-sub-comp-lem-tm σ t)

lift-sub-comp-lem-tm σ (Var i) = refl≃tm
lift-sub-comp-lem-tm σ (Coh Δ A τ) = Coh≃ refl≃c refl≃ty (susp-adjoint-full-≃ (lift-sub-comp-lem-sub σ τ))

lift-sub-comp-lem-ty σ ⋆ = refl≃ty
lift-sub-comp-lem-ty σ (s ─⟨ B ⟩⟶ t) = Arr≃ (lift-sub-comp-lem-tm σ s) (lift-sub-comp-lem-ty σ B) (lift-sub-comp-lem-tm σ t)

id-left-unit : (σ : Sub Γ Δ ⋆) → idSub Δ ∘ σ ≃s σ
id-on-ty : (B : Ty Γ) → B [ idSub Γ ]ty ≃ty B
id-on-tm : (t : Tm Γ) → t [ idSub Γ ]tm ≃tm t
id-on-var : (i : Fin (ctxLength Γ)) → Var i [ idSub Γ ]tm ≃tm Var {Γ = Γ} i

id-left-unit ⟨⟩ = Null≃ Star≃
id-left-unit ⟨ σ , t ⟩ = Ext≃ (id-left-unit σ) (id-on-tm t)

id-on-ty ⋆ = Star≃
id-on-ty (s ─⟨ B ⟩⟶ t) = Arr≃ (id-on-tm s) (id-on-ty B) (id-on-tm t)

id-on-tm (Var i) = id-on-var i
id-on-tm (Coh Δ A σ) = Coh≃ refl≃c refl≃ty (id-left-unit σ)

id-on-var {Γ = Γ , A} zero = refl≃tm
id-on-var {Γ = Γ , A} (suc i) = trans≃tm (apply-lifted-sub-var-≃ i (idSub Γ)) (lift-tm-≃ (id-on-var i))

∘-assoc : (σ : Sub Δ Υ C) → (τ : Sub Γ Δ ⋆) → (μ : Sub Γ′ Γ ⋆) → (σ ∘ τ) ∘ μ ≃s σ ∘ (τ ∘ μ)
assoc-tm : (σ : Sub Δ Υ C) → (τ : Sub Γ Δ ⋆) → (t : Tm Γ) → t [ σ ∘ τ ]tm ≃tm (t [ τ ]tm) [ σ ]tm
assoc-ty : (σ : Sub Δ Υ C) → (τ : Sub Γ Δ ⋆) → (A : Ty Γ) → A [ σ ∘ τ ]ty ≃ty (A [ τ ]ty) [ σ ]ty
assoc-var : (σ : Sub Δ Υ C) → (τ : Sub Γ Δ ⋆) → (i : Fin (ctxLength Γ)) → Var i [ σ ∘ τ ]tm ≃tm (Var i [ τ ]tm) [ σ ]tm

∘-assoc σ τ ⟨⟩ = Null≃ refl≃ty
∘-assoc σ τ ⟨ μ , t ⟩ = Ext≃ (∘-assoc σ τ μ) (assoc-tm σ τ t)

assoc-tm σ τ (Var i) = assoc-var σ τ i
assoc-tm σ τ (Coh Δ A μ) = Coh≃ refl≃c refl≃ty (susp-adjoint-full-≃ (∘-assoc σ τ μ))

assoc-ty σ τ ⋆ = refl≃ty
assoc-ty σ τ (s ─⟨ A ⟩⟶ t) = Arr≃ (assoc-tm σ τ s) (assoc-ty σ τ A) (assoc-tm σ τ t)

assoc-var {Γ = Γ , A} σ ⟨ τ , t ⟩ zero = refl≃tm
assoc-var {Γ = Γ , A} σ ⟨ τ , t ⟩ (suc i) = assoc-var σ τ i

-- Equal contexts are iso

idSub≃ : Γ ≃c Δ → Sub Γ Δ ⋆
idSub≃ Emp≃ = ⟨⟩
idSub≃ (Add≃ p x) = ⟨ (liftSub (idSub≃ p)) , 0V ⟩

idSub≃-on-ty : (p : Γ ≃c Δ) → A ≃ty B → A [ idSub≃ p ]ty ≃ty B
idSub≃-on-tm : (p : Γ ≃c Δ) → s ≃tm t → s [ idSub≃ p ]tm ≃tm t
idSub≃-on-sub : (p : Γ ≃c Δ) → σ ≃s τ → idSub≃ p ∘ σ ≃s τ

idSub≃-on-ty p Star≃ = Star≃
idSub≃-on-ty p (Arr≃ q r s) = Arr≃ (idSub≃-on-tm p q) (idSub≃-on-ty p r) (idSub≃-on-tm p s)

idSub≃-on-tm p (Var≃ x) = lem p _ _ x
  where
    lem : (p : Γ ≃c Δ) → (i : Fin (ctxLength Γ)) → (j : Fin (ctxLength Υ)) → toℕ i ≡ toℕ j → Var i [ idSub≃ p ]tm ≃tm Var {Γ = Υ} j
    lem {Γ = Γ , A} {Υ = Υ , A₁} (Add≃ p x) zero zero q = Var≃ refl
    lem {Γ = Γ , A} {Υ = Υ , A₁} (Add≃ p x) (suc i) (suc j) q = trans≃tm (apply-lifted-sub-tm-≃ (Var i) (idSub≃ p)) (lift-tm-≃ (lem p i j (cong pred q)))
idSub≃-on-tm p (Coh≃ q r s) = Coh≃ q r (idSub≃-on-sub p s)

idSub≃-on-sub p (Null≃ x) = Null≃ (trans≃ty Star≃ x)
idSub≃-on-sub p (Ext≃ q r) = Ext≃ (idSub≃-on-sub p q) (idSub≃-on-tm p r)
{-
-- sub-from-function-≃ : (f : (i : Fin (ctxLength Γ)) → Tm Δ (suc (lookupDim Γ i)))
--                     → (f2 : (i : Fin (ctxLength Γ)) → Tm Υ (suc (lookupDim Γ i)))
--                     → ((i : Fin (ctxLength Γ)) → f i ≃tm f2 i)
--                     → sub-from-function {Γ = Γ} f ≃s sub-from-function {Γ = Γ} f2
-- sub-from-function-≃ {Γ = ∅} f f2 eq = Null≃
-- sub-from-function-≃ {Γ = Γ , A} f f2 eq = Ext≃ (sub-from-function-≃ (λ i → f (suc i)) (λ i → f2 (suc i)) (λ i → eq (suc i))) (eq zero)

-- lift-sub-from-function : (f : (i : Fin (ctxLength Γ)) → Tm Δ (suc (lookupDim Γ i)))
--                        → liftSub {A = A} (sub-from-function {Γ = Γ} f) ≃s sub-from-function {Γ = Γ} (λ i → liftTerm {A = A} (f i))
-- lift-sub-from-function {Γ = ∅} f = Null≃
-- lift-sub-from-function {Γ = Γ , A} f = Ext≃ (lift-sub-from-function (λ i → f (suc i))) refl≃tm

-- subst-dim-tm-≃ : (t : Tm Γ n) → (p : m ≡ n) → subst-dim-tm t p ≃tm t
-- subst-dim-tm-≃ t refl = refl≃tm
-}
