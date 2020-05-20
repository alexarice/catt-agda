{-# OPTIONS --without-K --safe --exact-split #-}

open import Category.Monad

module Catt.TypeChecking {F : Set → Set} (M : RawMonad F) where

open import Catt.Fin
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Typing
open import Catt.TypeChecking.Monad M
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
pd-typeCheck : (Γ : Ctx n) → TCM (Σ[ dim ∈ ℕ ] Γ ⊢pd₀ dim)
pdb-typeCheck : (Γ : Ctx (suc n)) → (A : Ty (suc n)) → TCM (Σ[ submax ∈ ℕ ] Σ[ x ∈ Term (suc n) ] Γ ⊢pd x ∷ A [ submax ])

ctx-typeCheck ∅ = tc-ok TypeCtxBase
ctx-typeCheck (Γ , A) = TypeCtxStep Γ <$> ty-typeCheck Γ A

ty-typeCheck Γ ⋆ = TypeTyStar <$> (ctx-typeCheck Γ)
ty-typeCheck Γ (t ─⟨ A ⟩⟶ u) = do
  tt ← tm-typeCheck Γ t A
  ut ← tm-typeCheck Γ u A
  tc-ok (TypeTyArr tt ut)

tm-inferType : (Γ : Ctx n) → (t : Term n) → TCM (Σ[ A ∈ Ty n ] Γ ⊢ t ∷ A)
tm-inferType Γ (Var i) = (λ x → Γ ‼ i ,, TypeTermVar i x) <$> ctx-typeCheck Γ
tm-inferType Δ (Coh Γ A σ) = do
  sm ,, pdb ← pd-typeCheck Γ
  {!!}

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

pd-typeCheck {zero} Γ = tc-fail "Empty context is not a pasting diagram"
pd-typeCheck {suc n} Γ = do
  (submax ,, x ,, pdb) ← pdb-typeCheck Γ ⋆
  tc-ok (submax ,, Finish pdb)

reduce-to-type : ∀ {Γ} {y} {A B} {sm} → Γ ⊢pd y ∷ A [ sm ] → TCM (Σ[ submax ∈ ℕ ] Σ[ x ∈ Term (suc n) ] Γ ⊢pd x ∷ B [ submax ])
reduce-to-type {y = y} {⋆} {⋆} {sm} pdb = tc-ok (sm ,, y ,, pdb)
reduce-to-type {y = y} {⋆} {t ─⟨ B ⟩⟶ u} {sm} pdb = tc-fail "error message pd"
reduce-to-type {y = y} {t ─⟨ A ⟩⟶ u} {B} {sm} pdb with t ─⟨ A ⟩⟶ u ≡ty? B
... | yes refl = tc-ok (sm ,, y ,, pdb)
... | no p = reduce-to-type (Restr pdb)

pdb-typeCheck (∅ , A) B = do
  yes refl ← tc-ok (liftType A ≡ty? B)
    where no _ → tc-fail "Two types were not equal"
  yes refl ← tc-ok (A ≡ty? ⋆)
    where no _ → tc-fail "Base must be ⋆"
  tc-ok (0 ,, Var (fromℕ 0) ,, Base)
pdb-typeCheck (∅ , tgt , fill) B = tc-fail "Pd cannot be even length"
pdb-typeCheck (Γ , src , tgt , fill) B = do
  submax ,, x ,, pdb ← pdb-typeCheck (Γ , src) tgt
  yes refl ← tc-ok (fill ≡ty? liftTerm x ─⟨ liftType tgt ⟩⟶ Var (fromℕ _))
    where no _ → tc-fail "fill has wrong type"
  reduce-to-type (Extend pdb)
