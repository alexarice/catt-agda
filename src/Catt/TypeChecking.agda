{-# OPTIONS --without-K --safe --exact-split #-}

open import Category.Monad

module Catt.TypeChecking {F : Set → Set} (M : RawMonad F) where

open import Catt.Fin
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Typing
open import Catt.Typing.Properties
open import Catt.FreeVars
open import Catt.FreeVars.Properties
open import Catt.TypeChecking.Monad M
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool.Properties

private
  variable
    n m : ℕ

ctx-typeCheck : (Γ : Ctx n) → TCM (Γ ⊢)
ty-typeCheck : (Γ : Ctx n) → (A : Ty n) → TCM (Γ ⊢ A)
tm-typeCheck : (Γ : Ctx n) → (t : Term n) → (A : Ty n) → TCM (Γ ⊢ t ∷ A)
sub-typeCheck : (Δ : Ctx m) → (σ : Sub m n) → (Γ : Ctx n) → TCM (Δ ⊢ σ :: Γ)
pd-typeCheck : (Γ : Ctx n) → TCM (Γ ⊢pd₀)
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
tm-inferType Δ (Coh {zero} Γ A σ) = tc-fail "Pasting diagrams cannot be empty"
tm-inferType Δ (Coh {suc n} Γ A σ) = typeCoh ∣ typeComp A
  where
    typeCoh : TCM (Σ[ B ∈ Ty _ ] Δ ⊢ Coh Γ A σ ∷ B )
    typeCoh = do
      Γt ← pd-typeCheck Γ
      At ← ty-typeCheck Γ A
      fv ← decToTCM "Free variables did not match" (FVCtx Γ ≡fv? FVTy A)
      Δt ← ctx-typeCheck Δ
      σt ← sub-typeCheck Δ σ Γ
      tc-ok (A [ σ ]ty ,, TypeTermCoh Γt At fv Δt σt)

    typeComp : (B : Ty (suc n)) → TCM (Σ[ C ∈ Ty _ ] Δ ⊢ Coh Γ B σ ∷ C)
    typeComp ⋆ = tc-fail "Compositions can not have type dimension 0"
    typeComp B@(t ─⟨ _ ⟩⟶ u) = do
      Γt ← pd-typeCheck Γ
      Bt ← ty-typeCheck Γ B
      fvs ← decToTCM "Source free variables did not match" (FVSrc Γt ≡fv? FVTerm t)
      fvt ← decToTCM "Target free variables did not match" (FVTgt Γt ≡fv? FVTerm u)
      Δt ← ctx-typeCheck Δ
      σt ← sub-typeCheck Δ σ Γ
      tc-ok (B [ σ ]ty ,, TypeTermComp Γt Bt fvs fvt Δt σt)


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
  tc-ok (Finish pdb)

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
  refl ← decToTCM "fill has wrong type" (fill ≡ty? liftTerm x ─⟨ liftType tgt ⟩⟶ Var (fromℕ _))
  reduce-to-type (Extend pdb)
