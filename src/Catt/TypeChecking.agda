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
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

private
  variable
    n m dim : ℕ

ctx-typeCheck : (Γ : Ctx n) → TCM (Γ ⊢)
ty-typeCheck : (Γ : Ctx n) → (A : Ty n dim) → TCM (Γ ⊢ A)
tm-typeCheck : (Γ : Ctx n) → (t : Term n) → (A : Ty n dim) → TCM (Γ ⊢ t ∷ A)
sub-typeCheck : (Δ : Ctx m) → (σ : Sub m n) → (Γ : Ctx n) → TCM (Δ ⊢ σ :: Γ)
pd-typeCheck : (Γ : Ctx n) → TCM (Σ[ pdd ∈ ℕ ] Γ ⊢pd₀ pdd)
pdb-typeCheck : (Γ : Ctx (suc n)) → (resDim : ℕ) → TCM (Σ[ submax ∈ ℕ ] Σ[ x ∈ Term (suc n) ] Σ[ A ∈ Ty (suc n) resDim ] Σ[ pdd ∈ ℕ ] Γ ⊢pd x ∷ A [ submax ][ pdd ])

ctx-typeCheck ∅ = tc-ok TypeCtxBase
ctx-typeCheck (Γ , A) = TypeCtxStep Γ <$> ty-typeCheck Γ A

ty-typeCheck Γ ⋆ = TypeTyStar <$> (ctx-typeCheck Γ)
ty-typeCheck Γ (t ─⟨ A ⟩⟶ u) = do
  tt ← tm-typeCheck Γ t A
  ut ← tm-typeCheck Γ u A
  tc-ok (TypeTyArr tt ut)

tm-inferType : (Γ : Ctx n) → (t : Term n) → TCM (Σ[ dim ∈ ℕ ] Σ[ A ∈ Ty n dim ] Γ ⊢ t ∷ A)
tm-inferType Γ (Var i) = (λ x → -, proj₂ (Γ ‼ i) ,, TypeTermVar i x) <$> ctx-typeCheck Γ
tm-inferType Δ (Coh {zero} Γ A σ) = tc-fail "Pasting diagrams cannot be empty"
tm-inferType Δ (Coh {suc n} Γ B@(t ─⟨ A ⟩⟶ u) σ) = do
  _ ,, Γt ← pd-typeCheck Γ
  tt ← tm-typeCheck Γ t A
  ut ← tm-typeCheck Γ u A
  Δt ← ctx-typeCheck Δ
  σt ← sub-typeCheck Δ σ Γ
  let Bt = TypeTyArr tt ut
      fvs? = decToTCM "Source free variables did not match" (FVSrc Γt ≡fv? FVTerm t)
      fvt? = decToTCM "Target free variables did not match" (FVTgt Γt ≡fv? FVTerm u)
      fv? = decToTCM "Free variables did not match" (FVCtx Γ ≡fv? FVTy B)
  (λ x → -, B [ σ ]ty ,, x) <$>
    (⦇ (λ p → TypeTermCoh Γt Bt p Δt σt) fv? ⦈
    ∣ ⦇ (λ p q → TypeTermComp Γt Bt p q Δt σt) fvs? fvt? ⦈)


tm-typeCheck Γ t A = do
  dim ,, inferred ,, p ← tm-inferType Γ t
  refl ← decToTCM "Inferred type had wrong dimension" (ty-dim A ≟ dim)
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
  (submax ,, x ,, ⋆ ,, pdd  ,, pdb) ← pdb-typeCheck Γ 0
  tc-ok (pdd ,, Finish pdb)

reduce-to-dim : ∀ {Γ} {y} {dim} {newDim} {pdd} {A : Ty (suc n) dim} {sm} →
                (p : newDim ≤′ dim) →
                Γ ⊢pd y ∷ A [ sm ][ pdd ] → Σ[ submax ∈ ℕ ] Σ[ x ∈ Term (suc n) ] Γ ⊢pd x ∷ (ty-base-≤ p A) [ submax ][ pdd ]
reduce-to-dim ≤′-refl pdb = -, -, pdb
reduce-to-dim {A = t ─⟨ A ⟩⟶ u} (≤′-step p) pdb = reduce-to-dim p (Restr pdb)

extend : (submax : ℕ) →
         {Γ : Ctx (suc n)} →
         {A : Ty (suc n) dim} →
         {x : Term (suc n)} →
         {pdd : ℕ} →
         Γ ⊢pd x ∷ A [ submax ][ pdd ] →
         Σ[ d ∈ ℕ ] Γ , A , liftTerm x ─⟨ liftType A ⟩⟶ Var (fromℕ _) ⊢pd (Var (fromℕ _)) ∷ liftTerm (liftTerm x) ─⟨ liftType (liftType A) ⟩⟶ Var (inject (fromℕ _)) [ pred submax ][ d ]
extend zero pdb = -, ExtendM pdb
extend (suc sm) pdb with pdb-dim-lemma pdb
... | refl = -, Extend pdb

pdb-typeCheck (∅ , A) zero = do
  refl ← decToTCM "First type must be ⋆" (ty-dim A ≟ 0)
  refl ← decToTCM "First type must be ⋆" (A ≡ty? ⋆)
  tc-ok (0 ,, Var (fromℕ 0) ,, ⋆ ,, 0 ,, Base)
pdb-typeCheck (∅ , A) (suc resDim) = tc-fail "Dimensions did not line up"
pdb-typeCheck (∅ , tgt , fill) resDim = tc-fail "Pd cannot be even length"
pdb-typeCheck (Γ , src , tgt , fill) resDim = do
  submax ,, x ,, A ,, dim ,, pdb ← pdb-typeCheck (Γ , src) (ty-dim tgt)
  refl ← decToTCM "Types did not match" (tgt ≡ty? A)
  refl ← decToTCM "Fill had wrong dimension" (ty-dim fill ≟ suc (ty-dim tgt))
  refl ← decToTCM "fill has wrong type" (fill ≡ty? liftTerm x ─⟨ liftType tgt ⟩⟶ Var (fromℕ _))
  let newDim ,, pdbExtended = extend submax pdb
  p ← decToTCM "Dimensions did not line up" (resDim ≤′? ty-dim fill)
  _ ,, _ ,, pdbR ← tc-ok (reduce-to-dim p (pdbExtended))
  tc-ok (-, -, -, -, pdbR)
