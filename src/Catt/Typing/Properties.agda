{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Typing.Properties where

open import Catt.Syntax
open import Catt.Typing
open import Data.Nat
open import Catt.Fin
open import Catt.FreeVars
open import Catt.FreeVars.Properties
open import Catt.Vec.Functional
open import Relation.Binary.PropositionalEquality

private
  variable
    n m l o : ℕ
    Γ Γ′ Δ Δ′ : Ctx n
    t t′ u u′ : Term n
    A A′ B B′ : Ty n
    σ σ′ : Sub m n

transport-ctx : Γ ≡ Γ′ → Γ ⊢ → Γ′ ⊢
transport-ty : Γ ≡ Γ′ → A ≡ A′ → Γ ⊢ A → Γ′ ⊢ A′
transport-tm : Γ ≡ Γ′ → A ≡ A′ → t ≡ t′ → Γ ⊢ t ∷ A → Γ′ ⊢ t′ ∷ A′
transport-sub : Δ ≡ Δ′ → Γ ≡ Γ′ → σ ≡ σ′ → Δ ⊢ σ :: Γ → Δ′ ⊢ σ′ :: Γ′
-- transport-sub-ty : A ≡ty A′ → σ ≡sub σ′ → A [ σ ]ty ≡ty A′ [ σ′ ]ty
-- transport-sub-tm : t ≡tm t′ → σ ≡sub σ′ → t [ σ ]tm ≡tm t′ [ σ′ ]tm
-- transport-sub-comp : {σ σ′ : Sub l m} {τ τ′ : Sub m n} → σ ≡sub σ′ → τ ≡sub τ′ → σ ∘ τ ≡sub σ′ ∘ τ′
liftingTypeLemma : Γ , B ⊢ → Γ ⊢ A → Γ , B ⊢ liftType A
liftingTermLemma : Γ , B ⊢ → Γ ⊢ t ∷ A → Γ , B ⊢ liftTerm t ∷ liftType A
liftingSubLemma : Δ , B ⊢ → Δ ⊢ σ :: Γ → Δ , B ⊢ liftSub σ :: Γ
lift-sub-ap-ty : (A : Ty n) → (σ : Sub m n) → A [ liftSub σ ]ty ≡ liftType (A [ σ ]ty)
lift-sub-ap-tm : (t : Term n) → (σ : Sub m n) → t [ liftSub σ ]tm ≡ liftTerm (t [ σ ]tm)
lift-sub-ap-sub-right : (σ : Sub m n) → (τ : Sub l m) → σ ∘ liftSub τ ≡ liftSub (σ ∘ τ)
-- transport-lift-ty : A ≡ty A′ → liftType A ≡ty liftType A′
-- transport-lift-tm : t ≡tm t′ → liftTerm t ≡tm liftTerm t′
-- transport-lift-sub : σ ≡sub σ′ → liftSub σ ≡sub liftSub σ′
sub-extend-ap-ty : (A : Ty n) → (σ : Sub m n) → (t : Term m) → liftType A [ ⟨ σ , t ⟩ ]ty ≡ A [ σ ]ty
sub-extend-ap-tm : (u : Term n) → (σ : Sub m n) → (t : Term m) → liftTerm u [ ⟨ σ , t ⟩ ]tm ≡ u [ σ ]tm
sub-extend-sub : (σ : Sub m n) → (τ : Sub l m) → (t : Term l) → liftSub σ ∘ ⟨ τ , t ⟩ ≡ σ ∘ τ
sub-comp-ap-ty : (A : Ty n) → (σ : Sub m n) → (τ : Sub l m) → A [ σ ∘ τ ]ty ≡ A [ σ ]ty [ τ ]ty
sub-comp-ap-tm : (t : Term n) → (σ : Sub m n) → (τ : Sub l m) → t [ σ ∘ τ ]tm ≡ t [ σ ]tm [ τ ]tm
sub-comp-transitive : (σ : Sub m n) → (τ : Sub l m) → (θ : Sub o l) → (σ ∘ τ) ∘ θ ≡ σ ∘ (τ ∘ θ)
-- transport-pd : Γ ≡ctx Γ′ → {dim : ℕ} → Γ ⊢pd₀ dim → Γ′ ⊢pd₀ dim
-- transport-pdb : {Γ Γ′ : Ctx (suc n)} → Γ ≡ctx Γ′ → {submax : ℕ} → {A : Ty (suc n)} → {t : Term (suc n)} → Γ ⊢pd t ∷ A [ submax ] → Γ′ ⊢pd t ∷ A [ submax ]
-- transport-pd-src-fv : {Γ Γ′ : Ctx (suc n)} → (p : Γ ≡ctx Γ′) → {dim : ℕ} → (pd : Γ ⊢pd₀ dim) → FVSrc (transport-pd p pd) ≡fv FVSrc pd
-- transport-pdb-src-fv : {Γ Γ′ : Ctx (suc n)} → (p : Γ ≡ctx Γ′) → {submax : ℕ} → {A : Ty (suc n)} → {t : Term (suc n)} → (pdb : Γ ⊢pd t ∷ A [ submax ]) → FVSrc-b (transport-pdb p pdb) ≡fv FVSrc-b pdb
-- transport-pd-tgt-fv : {Γ Γ′ : Ctx (suc n)} → (p : Γ ≡ctx Γ′) → {dim : ℕ} → (pd : Γ ⊢pd₀ dim) → FVTgt (transport-pd p pd) ≡fv FVTgt pd
-- transport-pdb-tgt-fv : {Γ Γ′ : Ctx (suc n)} → (p : Γ ≡ctx Γ′) → {submax : ℕ} → {A : Ty (suc n)} → {t : Term (suc n)} → (pdb : Γ ⊢pd t ∷ A [ submax ]) → FVTgt-b (transport-pdb p pdb) ≡fv FVTgt-b pdb
-- transport-front : σ ≡sub σ′ → front σ ≡sub front σ′

transport-ctx refl p = p
transport-ty refl refl p = p
transport-tm refl refl refl p = p
transport-sub refl refl refl p = p

-- transport-ctx p (TypeCtxBase _) = TypeCtxBase _
-- transport-ctx p (TypeCtxStep _ x) = TypeCtxStep _ (transport-ty (λ i → p (inject i)) (p (fromℕ _)) x)

-- transport-ty p Star≡ (TypeTyStar x) = TypeTyStar (transport-ctx p x)
-- transport-ty p (Arr≡ q r s) (TypeTyArr a b) = TypeTyArr (transport-tm p r q a) (transport-tm p r s b)

-- transport-tm {n} {Γ} {Γ′} {A} {A′} p q (Var≡ refl) (TypeTermVar a b c) =
--   TypeTermVar a (transport-ctx p b) i
--   where
--     i : Γ′ ‼ a ≡ty A′
--     i = begin
--       Γ′ ‼ a ≈˘⟨ ‼-cong p a ⟩
--       Γ ‼ a ≈⟨ c ⟩
--       A ≈⟨ q ⟩
--       A′ ∎
--       where open Reasoning (ty-setoid n)
-- transport-tm {n} {Δ} {Δ′} {A} {A′} p q (Coh≡ {n′} {_} {Γ = Γ} {Γ′} {B} {B′} {σ} {σ′} r s t) (TypeTermCoh a b c d e f) =
--   TypeTermCoh (transport-pd r a) (transport-ty r s b) i (transport-ctx p d) (transport-sub p r t e) ii
--   where
--     i : FVCtx Γ′ ≡fv FVTy B′
--     i = begin
--       FVCtx Γ′ ≈˘⟨ transport-fv-ctx r ⟩
--       FVCtx Γ ≈⟨ c ⟩
--       FVTy B ≈⟨ transport-fv-ty s ⟩
--       FVTy B′ ∎
--       where open Reasoning (fv-setoid n′)

--     ii : A′ ≡ty B′ [ σ′ ]ty
--     ii = begin
--       A′ ≈˘⟨ q ⟩
--       A ≈⟨ f ⟩
--       B [ σ ]ty ≈⟨ transport-sub-ty s t ⟩
--       B′ [ σ′ ]ty ∎
--       where open Reasoning (ty-setoid n)
-- transport-tm {n} {Γ} {Γ′} {A} {A′} p q (Coh≡ {n′} {A = t ─⟨ B ⟩⟶ u} {t′ ─⟨ B′ ⟩⟶ u′} {σ} {σ′} r (Arr≡ x y z) w) (TypeTermComp a b c d e f g) =
--   TypeTermComp (transport-pd r a) (transport-ty r (Arr≡ x y z) b) i ii (transport-ctx p e) (transport-sub p r w f) iii
--   where
--     i : FVSrc (transport-pd r a) ≡fv FVTerm t′
--     i = begin
--       FVSrc (transport-pd r a) ≈⟨ transport-pd-src-fv r a ⟩
--       FVSrc a ≈⟨ c ⟩
--       FVTerm t ≈⟨ transport-fv-tm x ⟩
--       FVTerm t′ ∎
--       where open Reasoning (fv-setoid n′)

--     ii : FVTgt (transport-pd r a) ≡fv FVTerm u′
--     ii = begin
--       FVTgt (transport-pd r a) ≈⟨ transport-pd-tgt-fv r a ⟩
--       FVTgt a ≈⟨ d ⟩
--       FVTerm u ≈⟨ transport-fv-tm z ⟩
--       FVTerm u′ ∎
--       where open Reasoning (fv-setoid n′)

--     iii : A′ ≡ty t′ ─⟨ B′ ⟩⟶ u′ [ σ′ ]ty
--     iii = begin
--       A′ ≈˘⟨ q ⟩
--       A ≈⟨ g ⟩
--       t ─⟨ B ⟩⟶ u [ σ ]ty ≈⟨ transport-sub-ty (Arr≡ x y z) w ⟩
--       t′ ─⟨ B′ ⟩⟶ u′ [ σ′ ]ty ∎
--       where open Reasoning (ty-setoid n)

-- transport-sub p q r (TypeSubEmpty _) = TypeSubEmpty _
-- transport-sub p q r (TypeSubStep proof a b) = TypeSubStep (transport-sub p (λ i → q (inject i)) (λ i → r (inject i)) proof) (transport-ty (λ i → q (inject i)) (q (fromℕ _)) a) (transport-tm p (transport-sub-ty (q (fromℕ _)) (transport-front r)) (r (fromℕ _)) b)

-- transport-sub-ty Star≡ q = Star≡
-- transport-sub-ty (Arr≡ a b c) q = Arr≡ (transport-sub-tm a q) (transport-sub-ty b q) (transport-sub-tm c q)

-- transport-sub-tm (Var≡ refl) q = q _
-- transport-sub-tm (Coh≡ a b c) q = Coh≡ a b (transport-sub-comp q c)

-- transport-sub-comp p q i = transport-sub-tm (q i) p

-- transport-front p i = p (inject i)

liftingTypeLemma p (TypeTyStar x) = TypeTyStar p
liftingTypeLemma p (TypeTyArr q r) = TypeTyArr (liftingTermLemma p q) (liftingTermLemma p r)


liftingTermLemma p (TypeTermVar a b) = TypeTermVar (inject a) p
liftingTermLemma p (TypeTermCoh a {A = A} b c {σ = σ} d e) =
  transport-tm refl (lift-sub-ap-ty A σ) refl (TypeTermCoh a b c p (liftingSubLemma p e))
liftingTermLemma p (TypeTermComp a {A} {t} {u} b c d {σ = σ} e f) =
   transport-tm refl (lift-sub-ap-ty (t ─⟨ A ⟩⟶ u) σ) refl (TypeTermComp a b c d p (liftingSubLemma p f))


liftingSubLemma p TypeSubEmpty = TypeSubEmpty
liftingSubLemma p (TypeSubStep {σ = σ} a {A} b c) =
  TypeSubStep (liftingSubLemma p a)
              b
              (transport-tm refl (sym (lift-sub-ap-ty A σ))
              refl
              (liftingTermLemma p c))

lift-sub-ap-ty ⋆ σ = refl
lift-sub-ap-ty (t ─⟨ A ⟩⟶ u) σ
  rewrite lift-sub-ap-tm t σ
  rewrite lift-sub-ap-ty A σ
  rewrite lift-sub-ap-tm u σ = refl

lift-sub-ap-tm (Var (fromℕ n)) ⟨ σ , t ⟩ = refl
lift-sub-ap-tm (Var (inject i)) ⟨ σ , t ⟩ = lift-sub-ap-tm (Var i) σ
lift-sub-ap-tm (Coh Γ A τ) σ rewrite lift-sub-ap-sub-right τ σ = refl

lift-sub-ap-sub-right ⟨⟩ τ = refl
lift-sub-ap-sub-right ⟨ σ , t ⟩ τ
  rewrite lift-sub-ap-sub-right σ τ
  rewrite lift-sub-ap-tm t τ = refl

-- transport-lift-ty Star≡ = Star≡
-- transport-lift-ty (Arr≡ p q r) = Arr≡ (transport-lift-tm p) (transport-lift-ty q) (transport-lift-tm r)

-- transport-lift-tm (Var≡ refl) = tm-refl
-- transport-lift-tm (Coh≡ p q r) = Coh≡ p q (transport-lift-sub r)

-- transport-lift-sub p i = transport-lift-tm (p i)

sub-extend-ap-ty ⋆ σ t = refl
sub-extend-ap-ty (t ─⟨ A ⟩⟶ u) σ x
  rewrite sub-extend-ap-tm t σ x
  rewrite sub-extend-ap-ty A σ x
  rewrite sub-extend-ap-tm u σ x = refl -- Arr≡ (transport-front-sub-ap-tm t σ) (transport-front-sub-ap-ty A σ) (transport-front-sub-ap-tm u σ)

sub-extend-ap-tm (Var x) σ t = refl
sub-extend-ap-tm (Coh Γ A τ) σ t
  rewrite sub-extend-sub τ σ t = refl -- Coh≡ ctx-refl ty-refl (λ i → transport-front-sub-ap-tm (get τ i) σ)

sub-extend-sub ⟨⟩ τ x = refl
sub-extend-sub ⟨ σ , t ⟩ τ x
  rewrite sub-extend-sub σ τ x
  rewrite sub-extend-ap-tm t τ x = refl

sub-comp-ap-ty ⋆ σ τ = refl
sub-comp-ap-ty (t ─⟨ A ⟩⟶ u) σ τ
  rewrite sub-comp-ap-tm t σ τ
  rewrite sub-comp-ap-ty A σ τ
  rewrite sub-comp-ap-tm u σ τ = refl --Arr≡ (transport-sub-comp-ap-tm t σ τ) (transport-sub-comp-ap-ty A σ τ) (transport-sub-comp-ap-tm u σ τ)

sub-comp-ap-tm (Var (fromℕ n)) ⟨ σ , t ⟩ τ = refl
sub-comp-ap-tm (Var (inject i)) ⟨ σ , t ⟩ τ = sub-comp-ap-tm (Var i) σ τ
sub-comp-ap-tm (Coh Γ A θ) σ τ
  rewrite sub-comp-transitive θ σ τ = refl -- Coh≡ ctx-refl ty-refl (λ i → transport-sub-comp-ap-tm (get σ₁ i) σ τ)

sub-comp-transitive ⟨⟩ τ θ = refl
sub-comp-transitive ⟨ σ , t ⟩ τ θ
  rewrite sub-comp-transitive σ τ θ
  rewrite sub-comp-ap-tm t τ θ = refl
-- transport-pd p (Finish x) = Finish (transport-pdb p x)

-- transport-pdb p (Base _) = Base _
-- transport-pdb {n} {Γ} {Γ′} p (Extend {n₁} {A = A} {x} a b c) = Extend (transport-pdb (λ i → p (inject (inject i))) a) i ii
--   where
--     i : last (front Γ′) ≡ty A
--     i = begin
--       last (front Γ′) ≈˘⟨ p (inject (fromℕ (suc n₁))) ⟩
--       last (front Γ)  ≈⟨ b ⟩
--       A ∎
--       where open Reasoning (ty-setoid (suc n₁))

--     ii : last Γ′ ≡ty liftTerm x ─⟨ liftType A ⟩⟶ Var (fromℕ (suc n₁))
--     ii = begin
--       last Γ′ ≈˘⟨ p (fromℕ (suc (suc n₁))) ⟩
--       last Γ ≈⟨ c ⟩
--       liftTerm x ─⟨ liftType A ⟩⟶ Var (fromℕ (suc n₁)) ∎
--       where open Reasoning (ty-setoid (suc (suc n₁)))
-- transport-pdb p (Restr a) = Restr (transport-pdb p a)

-- transport-pd-src-fv p (Finish x) = transport-pdb-src-fv p x

-- transport-pdb-src-fv p (Base _) = fv-refl
-- transport-pdb-src-fv p (Extend {submax = zero} pdb a b) = fv-refl
-- transport-pdb-src-fv p (Extend {submax = suc zero} pdb a b) =
--   ewf-cong (ewf-cong (transport-pdb-src-fv (λ i → p (inject (inject i))) pdb))
-- transport-pdb-src-fv p (Extend {submax = suc (suc n)} pdb a b) =
--   ewt-cong (ewt-cong (transport-pdb-src-fv (λ i → p (inject (inject i))) pdb))
-- transport-pdb-src-fv p (Restr pdb) = transport-pdb-src-fv p pdb

-- transport-pd-tgt-fv p (Finish x) = transport-pdb-tgt-fv p x

-- transport-pdb-tgt-fv p (Base _) = fv-refl
-- transport-pdb-tgt-fv p (Extend {submax = zero} pdb a b) = fv-refl
-- transport-pdb-tgt-fv p (Extend {submax = suc zero} pdb a b) =
--   ewf-cong (ewt-cong (drop-cong (transport-pdb-tgt-fv (λ i → p (inject (inject i))) pdb)))
-- transport-pdb-tgt-fv p (Extend {submax = suc (suc n)} pdb a b) =
--   ewt-cong (ewt-cong (transport-pdb-tgt-fv (λ i → p (inject (inject i))) pdb))
-- transport-pdb-tgt-fv p (Restr pdb) = transport-pdb-tgt-fv p pdb


---------------------------------------------------------------

typeCheck⇒ctxCheck : Γ ⊢ A → Γ ⊢
termCheck⇒typeCheck : Γ ⊢ t ∷ A → Γ ⊢ A
subCheck⇒termCheck : Δ ⊢ σ :: Γ → Γ ⊢
sub-ty-check : Δ ⊢ → Δ ⊢ σ :: Γ → Γ ⊢ A → Δ ⊢ A [ σ ]ty
sub-tm-check : Δ ⊢ → Δ ⊢ σ :: Γ → Γ ⊢ t ∷ A → Δ ⊢ t [ σ ]tm ∷ A [ σ ]ty
sub-comp-check : {Υ : Ctx l} {Δ : Ctx m} {Γ : Ctx n} {σ : Sub m n} {τ : Sub l m} → Υ ⊢ → Δ ⊢ σ :: Γ → Υ ⊢ τ :: Δ → Υ ⊢ σ ∘ τ :: Γ


typeCheck⇒ctxCheck (TypeTyStar p) = p
typeCheck⇒ctxCheck (TypeTyArr (TypeTermVar a b) q) = b
typeCheck⇒ctxCheck (TypeTyArr (TypeTermCoh pd a b c d) q) = c
typeCheck⇒ctxCheck (TypeTyArr (TypeTermComp pd a b c d e) q) = d

termCheck⇒typeCheck (TypeTermVar (fromℕ n) p@(TypeCtxStep Γ x)) = liftingTypeLemma p x
termCheck⇒typeCheck (TypeTermVar (inject p) q@(TypeCtxStep Γ x)) = liftingTypeLemma q (termCheck⇒typeCheck (TypeTermVar p (typeCheck⇒ctxCheck x)))
termCheck⇒typeCheck (TypeTermCoh pd p q r s) = sub-ty-check r s p
termCheck⇒typeCheck (TypeTermComp pd p q r s t) = sub-ty-check s t p

subCheck⇒termCheck TypeSubEmpty = TypeCtxBase
subCheck⇒termCheck (TypeSubStep p q r) = TypeCtxStep _ q

sub-ty-check {A = ⋆} p q r = TypeTyStar p
sub-ty-check {A = t ─⟨ A ⟩⟶ u} p q (TypeTyArr a b) = TypeTyArr (sub-tm-check p q a) (sub-tm-check p q b)

sub-tm-check {t = Var (fromℕ n)} p (TypeSubStep {Γ = Γ} {σ} a {A} b {t} c) (TypeTermVar .(fromℕ n) x) = transport-tm refl (sym (sub-extend-ap-ty A σ t)) refl c
sub-tm-check {t = Var (inject j)} p (TypeSubStep {Γ = Γ} {σ} a {A} b {t} c) (TypeTermVar .(inject j) x) = transport-tm refl (sym (sub-extend-ap-ty (Γ ‼ j) σ t)) refl (sub-tm-check p a (TypeTermVar j (typeCheck⇒ctxCheck b)))
sub-tm-check {m} {σ = σ} {t = Coh Γ A τ} {B} p q (TypeTermCoh pd a b c d) =
  transport-tm refl
               (sub-comp-ap-ty A τ σ)
               refl
               (TypeTermCoh pd a b p (sub-comp-check p d q))
sub-tm-check {n} {σ = τ} {t = Coh Γ (t ─⟨ A ⟩⟶ u) σ} p q (TypeTermComp pd a b c d e) =
  transport-tm refl
               (sub-comp-ap-ty (t ─⟨ A ⟩⟶ u) σ τ)
               refl
               (TypeTermComp pd a b c p (sub-comp-check p e q))

sub-comp-check x TypeSubEmpty q = TypeSubEmpty
sub-comp-check {Γ = Γ , A} {⟨ σ , t ⟩} {τ} x (TypeSubStep a b c) q = TypeSubStep (sub-comp-check x a q) b (transport-tm refl (sym (sub-comp-ap-ty A σ τ)) refl (sub-tm-check x q c))
