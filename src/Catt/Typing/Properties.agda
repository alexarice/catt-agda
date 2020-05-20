{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Typing.Properties where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Typing
open import Data.Nat
open import Catt.Fin
open import Catt.FreeVars
open import Relation.Binary.PropositionalEquality

private
  variable
    n m l o : ℕ
    Γ Γ′ Δ Δ′ : Ctx n
    t t′ u : Term n
    A A′ B : Ty n
    σ σ′ : Sub m n

-- Transport lemmas

transport-ctx : Γ ≡ Γ′ → Γ ⊢ → Γ′ ⊢
transport-ty : Γ ≡ Γ′ → A ≡ A′ → Γ ⊢ A → Γ′ ⊢ A′
transport-tm : Γ ≡ Γ′ → A ≡ A′ → t ≡ t′ → Γ ⊢ t ∷ A → Γ′ ⊢ t′ ∷ A′
transport-sub : Δ ≡ Δ′ → Γ ≡ Γ′ → σ ≡ σ′ → Δ ⊢ σ :: Γ → Δ′ ⊢ σ′ :: Γ′

transport-ctx refl p = p
transport-ty refl refl p = p
transport-tm refl refl refl p = p
transport-sub refl refl refl p = p

-- Lifting Lemmas

liftingTypeLemma : Γ , B ⊢ → Γ ⊢ A → Γ , B ⊢ liftType A
liftingTermLemma : Γ , B ⊢ → Γ ⊢ t ∷ A → Γ , B ⊢ liftTerm t ∷ liftType A
liftingSubLemma : Δ , B ⊢ → Δ ⊢ σ :: Γ → Δ , B ⊢ liftSub σ :: Γ

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

-- Substitution Lemmas and lemmas from paper

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
