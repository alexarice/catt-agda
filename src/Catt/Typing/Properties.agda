{-# OPTIONS --allow-unsolved-metas --without-K #-}

module Catt.Typing.Properties where

open import Catt.Syntax
open import Catt.Typing
open import Data.Nat
open import Catt.Fin
open import Catt.FreeVars
open import Catt.FreeVars.Properties
open import Catt.Vec.Functional
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Catt.Syntax.Equality
import Relation.Binary.Reasoning.Setoid
module Reasoning = Relation.Binary.Reasoning.Setoid

private
  variable
    n m l : ℕ
    Γ Γ′ Δ Δ′ : Ctx n
    t t′ u u′ : Term n
    A A′ B B′ : Ty n
    σ σ′ : Sub m n

transport-ctx : Γ ≡ctx Γ′ → Γ ⊢ → Γ′ ⊢
transport-ty : Γ ≡ctx Γ′ → A ≡ty A′ → Γ ⊢ A → Γ′ ⊢ A′
transport-tm : Γ ≡ctx Γ′ → A ≡ty A′ → t ≡tm t′ → Γ ⊢ t ∷ A → Γ′ ⊢ t′ ∷ A′
transport-sub : Δ ≡ctx Δ′ → Γ ≡ctx Γ′ → σ ≡sub σ′ → Δ ⊢ σ :: Γ → Δ′ ⊢ σ′ :: Γ′
transport-sub-ty : A ≡ty A′ → σ ≡sub σ′ → A [ σ ]ty ≡ty A′ [ σ′ ]ty
transport-sub-tm : t ≡tm t′ → σ ≡sub σ′ → t [ σ ]tm ≡tm t′ [ σ′ ]tm
transport-sub-comp : {σ σ′ : Sub l m} {τ τ′ : Sub m n} → σ ≡sub σ′ → τ ≡sub τ′ → σ ∘ τ ≡sub σ′ ∘ τ′
liftingTypeLemma : Γ ⊢ → front Γ ⊢ A → Γ ⊢ liftType A
liftingTermLemma : Γ ⊢ → front Γ ⊢ t ∷ A → Γ ⊢ liftTerm t ∷ liftType A
liftingSubLemma : Δ ⊢ → front Δ ⊢ σ :: Γ → Δ ⊢ liftSub σ :: Γ
lift-sub-ap-ty : (A : Ty n) → (σ : Sub m n) → A [ liftSub σ ]ty ≡ty liftType (A [ σ ]ty)
lift-sub-ap-tm : (t : Term n) → (σ : Sub m n) → t [ liftSub σ ]tm ≡tm liftTerm (t [ σ ]tm)
lift-sub-ap-sub : (σ : Sub l m) → (τ : Sub m n) → liftSub σ ∘ τ ≡sub liftSub (σ ∘ τ)
transport-lift-ty : A ≡ty A′ → liftType A ≡ty liftType A′
transport-lift-tm : t ≡tm t′ → liftTerm t ≡tm liftTerm t′
transport-lift-sub : σ ≡sub σ′ → liftSub σ ≡sub liftSub σ′
transport-front-sub-ap-ty : (A : Ty n) → (σ : Sub m (suc n)) → liftType A [ σ ]ty ≡ty A [ front σ ]ty
transport-front-sub-ap-tm : (t : Term n) → (σ : Sub m (suc n)) → liftTerm t [ σ ]tm ≡tm t [ front σ ]tm
transport-sub-comp-ap-ty : (A : Ty n) → (σ : Sub m n) → (τ : Sub l m) → A [ τ ∘ σ ]ty ≡ty A [ σ ]ty [ τ ]ty
transport-sub-comp-ap-tm : (t : Term n) → (σ : Sub m n) → (τ : Sub l m) → t [ τ ∘ σ ]tm ≡tm t [ σ ]tm [ τ ]tm
transport-pd : Γ ≡ctx Γ′ → {dim : ℕ} → Γ ⊢pd₀ dim → Γ′ ⊢pd₀ dim
transport-pdb : {Γ Γ′ : Ctx (suc n)} → Γ ≡ctx Γ′ → {submax : ℕ} → {A : Ty (suc n)} → {t : Term (suc n)} → Γ ⊢pd t ∷ A [ submax ] → Γ′ ⊢pd t ∷ A [ submax ]
transport-pd-src-fv : {Γ Γ′ : Ctx (suc n)} → (p : Γ ≡ctx Γ′) → {dim : ℕ} → (pd : Γ ⊢pd₀ dim) → FVSrc (transport-pd p pd) ≡fv FVSrc pd
transport-pdb-src-fv : {Γ Γ′ : Ctx (suc n)} → (p : Γ ≡ctx Γ′) → {submax : ℕ} → {A : Ty (suc n)} → {t : Term (suc n)} → (pdb : Γ ⊢pd t ∷ A [ submax ]) → FVSrc-b (transport-pdb p pdb) ≡fv FVSrc-b pdb
transport-pd-tgt-fv : {Γ Γ′ : Ctx (suc n)} → (p : Γ ≡ctx Γ′) → {dim : ℕ} → (pd : Γ ⊢pd₀ dim) → FVTgt (transport-pd p pd) ≡fv FVTgt pd
transport-pdb-tgt-fv : {Γ Γ′ : Ctx (suc n)} → (p : Γ ≡ctx Γ′) → {submax : ℕ} → {A : Ty (suc n)} → {t : Term (suc n)} → (pdb : Γ ⊢pd t ∷ A [ submax ]) → FVTgt-b (transport-pdb p pdb) ≡fv FVTgt-b pdb
transport-front : σ ≡sub σ′ → front σ ≡sub front σ′

transport-ctx p (TypeCtxBase _) = TypeCtxBase _
transport-ctx p (TypeCtxStep _ x) = TypeCtxStep _ (transport-ty (λ i → p (inject i)) (p (fromℕ _)) x)

transport-ty p Star≡ (TypeTyStar x) = TypeTyStar (transport-ctx p x)
transport-ty p (Arr≡ q r s) (TypeTyArr a b) = TypeTyArr (transport-tm p r q a) (transport-tm p r s b)

transport-tm {n} {Γ} {Γ′} {A} {A′} p q (Var≡ refl) (TypeTermVar a b c) =
  TypeTermVar a (transport-ctx p b) i
  where
    i : Γ′ ‼ a ≡ty A′
    i = begin
      Γ′ ‼ a ≈˘⟨ ‼-cong p a ⟩
      Γ ‼ a ≈⟨ c ⟩
      A ≈⟨ q ⟩
      A′ ∎
      where open Reasoning (ty-setoid n)
transport-tm {n} {Δ} {Δ′} {A} {A′} p q (Coh≡ {n′} {_} {Γ = Γ} {Γ′} {B} {B′} {σ} {σ′} r s t) (TypeTermCoh a b c d e f) =
  TypeTermCoh (transport-pd r a) (transport-ty r s b) i (transport-ctx p d) (transport-sub p r t e) ii
  where
    i : FVCtx Γ′ ≡fv FVTy B′
    i = begin
      FVCtx Γ′ ≈˘⟨ transport-fv-ctx r ⟩
      FVCtx Γ ≈⟨ c ⟩
      FVTy B ≈⟨ transport-fv-ty s ⟩
      FVTy B′ ∎
      where open Reasoning (fv-setoid n′)

    ii : A′ ≡ty B′ [ σ′ ]ty
    ii = begin
      A′ ≈˘⟨ q ⟩
      A ≈⟨ f ⟩
      B [ σ ]ty ≈⟨ transport-sub-ty s t ⟩
      B′ [ σ′ ]ty ∎
      where open Reasoning (ty-setoid n)
transport-tm {n} {Γ} {Γ′} {A} {A′} p q (Coh≡ {n′} {A = t ─⟨ B ⟩⟶ u} {t′ ─⟨ B′ ⟩⟶ u′} {σ} {σ′} r (Arr≡ x y z) w) (TypeTermComp a b c d e f g) =
  TypeTermComp (transport-pd r a) (transport-ty r (Arr≡ x y z) b) i ii (transport-ctx p e) (transport-sub p r w f) iii
  where
    i : FVSrc (transport-pd r a) ≡fv FVTerm t′
    i = begin
      FVSrc (transport-pd r a) ≈⟨ transport-pd-src-fv r a ⟩
      FVSrc a ≈⟨ c ⟩
      FVTerm t ≈⟨ transport-fv-tm x ⟩
      FVTerm t′ ∎
      where open Reasoning (fv-setoid n′)

    ii : FVTgt (transport-pd r a) ≡fv FVTerm u′
    ii = begin
      FVTgt (transport-pd r a) ≈⟨ transport-pd-tgt-fv r a ⟩
      FVTgt a ≈⟨ d ⟩
      FVTerm u ≈⟨ transport-fv-tm z ⟩
      FVTerm u′ ∎
      where open Reasoning (fv-setoid n′)

    iii : A′ ≡ty t′ ─⟨ B′ ⟩⟶ u′ [ σ′ ]ty
    iii = begin
      A′ ≈˘⟨ q ⟩
      A ≈⟨ g ⟩
      t ─⟨ B ⟩⟶ u [ σ ]ty ≈⟨ transport-sub-ty (Arr≡ x y z) w ⟩
      t′ ─⟨ B′ ⟩⟶ u′ [ σ′ ]ty ∎
      where open Reasoning (ty-setoid n)

transport-sub p q r (TypeSubEmpty _) = TypeSubEmpty _
transport-sub p q r (TypeSubStep proof a b) = TypeSubStep (transport-sub p (λ i → q (inject i)) (λ i → r (inject i)) proof) (transport-ty (λ i → q (inject i)) (q (fromℕ _)) a) (transport-tm p (transport-sub-ty (q (fromℕ _)) (transport-front r)) (r (fromℕ _)) b)

transport-sub-ty Star≡ q = Star≡
transport-sub-ty (Arr≡ a b c) q = Arr≡ (transport-sub-tm a q) (transport-sub-ty b q) (transport-sub-tm c q)

transport-sub-tm (Var≡ refl) q = q _
transport-sub-tm (Coh≡ a b c) q = Coh≡ a b (transport-sub-comp q c)

transport-sub-comp p q i = transport-sub-tm (q i) p

transport-front p i = p (inject i)

liftingTypeLemma p (TypeTyStar x) = TypeTyStar p
liftingTypeLemma p (TypeTyArr q r) = TypeTyArr (liftingTermLemma p q) (liftingTermLemma p r)


liftingTermLemma p (TypeTermVar a b c) = TypeTermVar (inject a) p (transport-lift-ty c)
liftingTermLemma p (TypeTermCoh a {A = A} b c {σ = σ} d e f) = TypeTermCoh a b c p (liftingSubLemma p e) (ty-trans (transport-lift-ty f) (ty-sym (lift-sub-ap-ty A σ)))
liftingTermLemma p (TypeTermComp a {A} {t} {u} b c d {σ = σ} e f g) = TypeTermComp a b c d p (liftingSubLemma p f)
  (ty-trans (transport-lift-ty g) (ty-sym (lift-sub-ap-ty (t ─⟨ A ⟩⟶ u) σ)))


liftingSubLemma p (TypeSubEmpty _) = TypeSubEmpty (liftSub _)
liftingSubLemma {σ = σ} {Γ = Γ} p (TypeSubStep a b c) = TypeSubStep (transport-sub ctx-refl ctx-refl (λ i → tm-refl) (liftingSubLemma p a)) b (transport-tm ctx-refl (ty-trans (ty-sym (lift-sub-ap-ty (get Γ (fromℕ _)) (front σ))) (transport-sub-ty ty-refl (λ i → tm-refl))) tm-refl (liftingTermLemma p c))

lift-sub-ap-ty ⋆ σ = Star≡
lift-sub-ap-ty (t ─⟨ A ⟩⟶ u) σ = Arr≡ (lift-sub-ap-tm t σ) (lift-sub-ap-ty A σ) (lift-sub-ap-tm u σ)

lift-sub-ap-tm (Var x) σ = tm-refl
lift-sub-ap-tm (Coh Γ A τ) σ = Coh≡ ctx-refl ty-refl (lift-sub-ap-sub σ τ)

lift-sub-ap-sub σ τ i = lift-sub-ap-tm (get τ i) σ

transport-lift-ty Star≡ = Star≡
transport-lift-ty (Arr≡ p q r) = Arr≡ (transport-lift-tm p) (transport-lift-ty q) (transport-lift-tm r)

transport-lift-tm (Var≡ refl) = tm-refl
transport-lift-tm (Coh≡ p q r) = Coh≡ p q (transport-lift-sub r)

transport-lift-sub p i = transport-lift-tm (p i)

transport-front-sub-ap-ty ⋆ σ = Star≡
transport-front-sub-ap-ty (t ─⟨ A ⟩⟶ u) σ = Arr≡ (transport-front-sub-ap-tm t σ) (transport-front-sub-ap-ty A σ) (transport-front-sub-ap-tm u σ)

transport-front-sub-ap-tm (Var x) σ = tm-refl
transport-front-sub-ap-tm (Coh Γ A τ) σ = Coh≡ ctx-refl ty-refl (λ i → transport-front-sub-ap-tm (get τ i) σ)

transport-sub-comp-ap-ty ⋆ σ τ = Star≡
transport-sub-comp-ap-ty (t ─⟨ A ⟩⟶ u) σ τ = Arr≡ (transport-sub-comp-ap-tm t σ τ) (transport-sub-comp-ap-ty A σ τ) (transport-sub-comp-ap-tm u σ τ)

transport-sub-comp-ap-tm (Var x) σ τ = tm-refl
transport-sub-comp-ap-tm (Coh Γ A σ₁) σ τ = Coh≡ ctx-refl ty-refl (λ i → transport-sub-comp-ap-tm (get σ₁ i) σ τ)

transport-pd p (Finish x) = Finish (transport-pdb p x)

transport-pdb p (Base _) = Base _
transport-pdb {n} {Γ} {Γ′} p (Extend {n₁} {A = A} {x} a b c) = Extend (transport-pdb (λ i → p (inject (inject i))) a) i ii
  where
    i : last (front Γ′) ≡ty A
    i = begin
      last (front Γ′) ≈˘⟨ p (inject (fromℕ (suc n₁))) ⟩
      last (front Γ)  ≈⟨ b ⟩
      A ∎
      where open Reasoning (ty-setoid (suc n₁))

    ii : last Γ′ ≡ty liftTerm x ─⟨ liftType A ⟩⟶ Var (fromℕ (suc n₁))
    ii = begin
      last Γ′ ≈˘⟨ p (fromℕ (suc (suc n₁))) ⟩
      last Γ ≈⟨ c ⟩
      liftTerm x ─⟨ liftType A ⟩⟶ Var (fromℕ (suc n₁)) ∎
      where open Reasoning (ty-setoid (suc (suc n₁)))
transport-pdb p (Restr a) = Restr (transport-pdb p a)

transport-pd-src-fv p (Finish x) = transport-pdb-src-fv p x

transport-pdb-src-fv p (Base _) = fv-refl
transport-pdb-src-fv p (Extend {submax = zero} pdb a b) = fv-refl
transport-pdb-src-fv p (Extend {submax = suc zero} pdb a b) =
  ewf-cong (ewf-cong (transport-pdb-src-fv (λ i → p (inject (inject i))) pdb))
transport-pdb-src-fv p (Extend {submax = suc (suc n)} pdb a b) =
  ewt-cong (ewt-cong (transport-pdb-src-fv (λ i → p (inject (inject i))) pdb))
transport-pdb-src-fv p (Restr pdb) = transport-pdb-src-fv p pdb

transport-pd-tgt-fv p (Finish x) = transport-pdb-tgt-fv p x

transport-pdb-tgt-fv p (Base _) = fv-refl
transport-pdb-tgt-fv p (Extend {submax = zero} pdb a b) = fv-refl
transport-pdb-tgt-fv p (Extend {submax = suc zero} pdb a b) =
  ewf-cong (ewt-cong (drop-cong (transport-pdb-tgt-fv (λ i → p (inject (inject i))) pdb)))
transport-pdb-tgt-fv p (Extend {submax = suc (suc n)} pdb a b) =
  ewt-cong (ewt-cong (transport-pdb-tgt-fv (λ i → p (inject (inject i))) pdb))
transport-pdb-tgt-fv p (Restr pdb) = transport-pdb-tgt-fv p pdb

---------------------------------------------------------------

typeCheck⇒ctxCheck : Γ ⊢ A → Γ ⊢
termCheck⇒typeCheck : Γ ⊢ t ∷ A → Γ ⊢ A
subCheck⇒termCheck : Δ ⊢ σ :: Γ → Γ ⊢
sub-ty-check : Δ ⊢ → Δ ⊢ σ :: Γ → Γ ⊢ A → Δ ⊢ A [ σ ]ty
sub-tm-check : Δ ⊢ → Δ ⊢ σ :: Γ → Γ ⊢ t ∷ A → Δ ⊢ t [ σ ]tm ∷ A [ σ ]ty
sub-comp-check : {Υ : Ctx l} {Δ : Ctx m} {Γ : Ctx n} {σ : Sub m n} {τ : Sub l m} → Υ ⊢ → Δ ⊢ σ :: Γ → Υ ⊢ τ :: Δ → Υ ⊢ τ ∘ σ :: Γ

typeCheck⇒ctxCheck (TypeTyStar p) = p
typeCheck⇒ctxCheck (TypeTyArr (TypeTermVar a b c) q) = b
typeCheck⇒ctxCheck (TypeTyArr (TypeTermCoh pd a b c d e) q) = c
typeCheck⇒ctxCheck (TypeTyArr (TypeTermComp pd a b c d e f) q) = d

termCheck⇒typeCheck (TypeTermVar (fromℕ n) p@(TypeCtxStep Γ x) r) =
  transport-ty ctx-refl r (liftingTypeLemma p x)
termCheck⇒typeCheck (TypeTermVar (inject p) q@(TypeCtxStep Γ x) r) = transport-ty ctx-refl r (liftingTypeLemma q (termCheck⇒typeCheck (TypeTermVar p (typeCheck⇒ctxCheck x) ty-refl)))
termCheck⇒typeCheck (TypeTermCoh pd p q r s t) = transport-ty ctx-refl (ty-sym t) (sub-ty-check r s p)
termCheck⇒typeCheck (TypeTermComp pd p q r s t u) = transport-ty ctx-refl (ty-sym u) (sub-ty-check s t p)

subCheck⇒termCheck (TypeSubEmpty _) = TypeCtxBase _
subCheck⇒termCheck (TypeSubStep p q r) = TypeCtxStep _ q

sub-ty-check {A = ⋆} p q r = TypeTyStar p
sub-ty-check {A = t ─⟨ A ⟩⟶ u} p q (TypeTyArr a b) = TypeTyArr (sub-tm-check p q a) (sub-tm-check p q b)

sub-tm-check {m} {σ = σ} {Γ} {Var (fromℕ n)} {A} p (TypeSubStep a b c) (TypeTermVar .(fromℕ n) x y) =
  transport-tm ctx-refl i tm-refl c
  where
    i : last Γ [ front σ ]ty ≡ty A [ σ ]ty
    i = begin
      last Γ [ front σ ]ty ≈˘⟨ transport-front-sub-ap-ty (last Γ) σ ⟩
      liftType (last Γ) [ σ ]ty ≈⟨ transport-sub-ty y sub-refl ⟩
      A [ σ ]ty ∎
      where open Reasoning (ty-setoid m)
sub-tm-check {m} {σ = σ} {Γ} {Var (inject j)} {A} p (TypeSubStep a b c) (TypeTermVar .(inject j) x y) =
  transport-tm ctx-refl i tm-refl (sub-tm-check p a (TypeTermVar j (typeCheck⇒ctxCheck b) ty-refl))
  where
    i : front Γ ‼ j [ front σ ]ty ≡ty A [ σ ]ty
    i = begin
      front Γ ‼ j [ front σ ]ty ≈˘⟨ transport-front-sub-ap-ty (front Γ ‼ j) σ ⟩
      liftType (front Γ ‼ j) [ σ ]ty ≈⟨ transport-sub-ty y sub-refl ⟩
      A [ σ ]ty ∎
      where open Reasoning (ty-setoid m)
sub-tm-check {m} {σ = σ} {t = Coh Γ A τ} {B} p q (TypeTermCoh pd a b c d e) = TypeTermCoh pd a b p (sub-comp-check p d q) i
  where
    i : B [ σ ]ty ≡ty A [ σ ∘ τ ]ty
    i = begin
      B [ σ ]ty ≈⟨ transport-sub-ty e sub-refl ⟩
      A [ τ ]ty [ σ ]ty ≈˘⟨ transport-sub-comp-ap-ty A τ σ ⟩
      A [ σ ∘ τ ]ty ∎
      where open Reasoning (ty-setoid m)
sub-tm-check {n} {σ = τ} {t = Coh Γ (t ─⟨ A ⟩⟶ u) σ} p q (TypeTermComp pd a b c d e {B} f) =
  TypeTermComp pd a b c p (sub-comp-check p e q) i
  where
    i : B [ τ ]ty ≡ty t ─⟨ A ⟩⟶ u [ τ ∘ σ ]ty
    i = begin
      B [ τ ]ty ≈⟨ transport-sub-ty f sub-refl ⟩
      t ─⟨ A ⟩⟶ u [ σ ]ty [ τ ]ty ≈˘⟨ transport-sub-comp-ap-ty (t ─⟨ A ⟩⟶ u) σ τ ⟩
      t ─⟨ A ⟩⟶ u [ τ ∘ σ ]ty ∎
      where open Reasoning (ty-setoid n)

sub-comp-check x (TypeSubEmpty _) q = TypeSubEmpty _
sub-comp-check {Γ = Γ} {σ} {τ} x (TypeSubStep a b c) q = TypeSubStep (sub-comp-check x a q) b (transport-tm ctx-refl (ty-sym (transport-sub-comp-ap-ty (last Γ) (front σ) τ)) tm-refl (sub-tm-check x q c))
