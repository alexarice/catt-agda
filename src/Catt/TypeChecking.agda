{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.TypeChecking where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Typing
open import Catt.TypeChecking.Monad
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

private
  variable
    n m : ℕ


ctx-typeCheck : (Γ : Ctx n) → TCM (Γ ⊢)
ty-typeCheck : (Γ : Ctx n) → (A : Ty n) → TCM (Γ ⊢ A)
tm-typeCheck : (Γ : Ctx n) → (t : Term n) → (A : Ty n) → TCM (Γ ⊢ t ∷ A)
sub-typeCheck : (Δ : Ctx m) → (σ : Sub m n) → (Γ : Ctx n) → TCM (Δ ⊢ σ :: Γ)

ctx-typeCheck ∅ = tc-ok TypeCtxBase
ctx-typeCheck (Γ , A) = TypeCtxStep Γ <$> ty-typeCheck Γ A

ty-typeCheck Γ ⋆ = TypeTyStar <$> (ctx-typeCheck Γ)
ty-typeCheck Γ (t ─⟨ A ⟩⟶ u) = do
  tt ← tm-typeCheck Γ t A
  ut ← tm-typeCheck Γ u A
  tc-ok (TypeTyArr tt ut)

tm-inferType : (Γ : Ctx n) → (t : Term n) → TCM (Σ[ A ∈ Ty n ] Γ ⊢ t ∷ A)
tm-inferType Γ (Var i) = (λ x → Γ ‼ i ,, TypeTermVar i x) <$> ctx-typeCheck Γ
tm-inferType Γ (Coh Γ₁ A σ) = {!!}

tm-typeCheck Γ t A = do
  inferred ,, p ← tm-inferType Γ t
  yes refl ← tc-ok (A ≡ty? inferred)
    where no _ → tc-fail "Inferred type did not match given type"
  tc-ok p

sub-typeCheck Δ ⟨⟩ ∅ = tc-ok TypeSubEmpty
sub-typeCheck Δ ⟨ σ , t ⟩ (Γ , A) = do
  σt ← sub-typeCheck Δ σ Γ
  At ← ty-typeCheck Γ A
  tt ← tm-typeCheck Δ t (A [ σ ]ty)
  tc-ok (TypeSubStep σt At tt)
