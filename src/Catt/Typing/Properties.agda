{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Typing.Properties where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Typing
open import Data.Nat
open import Data.Nat.Properties
open import Catt.Fin
open import Catt.FreeVars
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)

private
  variable
    n m l o dim submax pdd : ℕ
    Γ Γ′ Δ Δ′ : Ctx n
    t t′ u : Term n
    A A′ B : Ty n dim
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
sub-tm-check {t = Var (inject j)} p (TypeSubStep {Γ = Γ} {σ} a {A} b {t} c) (TypeTermVar .(inject j) x) = transport-tm refl (sym (sub-extend-ap-ty (proj₂ (Γ ‼ j)) σ t)) refl (sub-tm-check p a (TypeTermVar j (typeCheck⇒ctxCheck b)))
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

-- Dimension lemmas

pdb-dim-lemma : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n) dim} → (Γ ⊢pd x ∷ A [ submax ][ pdd ]) → submax + dim ≡ pdd
pdb-dim-lemma Base = refl
pdb-dim-lemma (ExtendM pdb) = refl
pdb-dim-lemma (Extend pdb) = +-suc _ _
pdb-dim-lemma {dim = dim} (Restr {submax = submax} pdb) = trans (sym (+-suc submax dim)) (pdb-dim-lemma pdb)


-- liftType-dim : (A : Ty n) → ty-dim (liftType A) ≡ ty-dim A
-- liftType-dim ⋆ = refl
-- liftType-dim (t ─⟨ A ⟩⟶ u) = cong suc (liftType-dim A)

-- pdb-dim : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n)} → (Γ ⊢pd x ∷ A [ submax ]) → ty-dim A + submax ≡ ctx-dim Γ
-- pdb-dim Base = refl
-- pdb-dim (Extend {submax = zero} {Γ = Γ} {A} pdb) =
--   suc (ty-dim (liftType (liftType A)) + zero) ≡⟨ cong suc (+-identityʳ _) ⟩
--   suc (ty-dim (liftType (liftType A)))        ≡⟨ cong suc (liftType-dim (liftType A)) ⟩
--   suc (ty-dim (liftType A))                   ≡˘⟨ m≤n⇒m⊔n≡n i ⟩
--   ty-dim A ⊔ suc (ty-dim (liftType A))        ≡˘⟨ cong (_⊔ suc (ty-dim (liftType A))) (m≤n⇒m⊔n≡n ii) ⟩
--   ctx-dim Γ ⊔ ty-dim A ⊔ suc (ty-dim (liftType A)) ∎
--   where
--     i : ty-dim A ≤ suc (ty-dim (liftType A))
--     i = begin
--       ty-dim A ≤⟨ n≤1+n (ty-dim A) ⟩
--       suc (ty-dim A) ≡˘⟨ cong suc (liftType-dim A) ⟩
--       suc (ty-dim (liftType A)) ∎
--       where
--         open ≤-Reasoning

--     ii : ctx-dim Γ ≤ ty-dim A
--     ii = begin
--       ctx-dim Γ ≡˘⟨ pdb-dim pdb ⟩
--       ty-dim A + zero ≡⟨ +-identityʳ (ty-dim A) ⟩
--       ty-dim A ∎
--       where
--         open ≤-Reasoning

--     open ≡-Reasoning
-- pdb-dim (Extend {submax = suc n} {Γ = Γ} {A} pdb) =
--   suc (ty-dim (liftType (liftType A)) + n) ≡˘⟨ +-suc _ _ ⟩
--   ty-dim (liftType (liftType A)) + suc n ≡⟨ cong (_+ suc n) (liftType-dim (liftType A)) ⟩
--     ty-dim (liftType A) + suc n ≡⟨ cong (_+ suc n) (liftType-dim A) ⟩
--   ty-dim A + suc n ≡˘⟨ m≤n⇒n⊔m≡n i ⟩
--   ty-dim A + suc n ⊔ suc (ty-dim (liftType A)) ≡⟨ cong (_⊔ suc (ty-dim (liftType A))) (pdb-dim pdb) ⟩
--   ctx-dim Γ ⊔ suc (ty-dim (liftType A)) ≡˘⟨ cong (ctx-dim Γ ⊔_) (m≤n⇒m⊔n≡n ii) ⟩
--   ctx-dim Γ ⊔ (ty-dim A ⊔ suc (ty-dim (liftType A))) ≡˘⟨ ⊔-assoc (ctx-dim Γ) _ _ ⟩
--   ctx-dim Γ ⊔ ty-dim A ⊔ suc (ty-dim (liftType A)) ∎
--     where
--       i : suc (ty-dim (liftType A)) ≤ ty-dim A + suc n
--       i = begin
--         suc (ty-dim (liftType A)) ≡⟨ cong suc (liftType-dim A) ⟩
--         suc (ty-dim A) ≤⟨ m≤m+n (suc (ty-dim A)) n ⟩
--         suc (ty-dim A) + n ≡˘⟨ +-suc (ty-dim A) n ⟩
--         ty-dim A + suc n ∎
--         where
--           open ≤-Reasoning

--       ii : ty-dim A ≤ suc (ty-dim (liftType A))
--       ii = begin
--         ty-dim A ≡˘⟨ liftType-dim A ⟩
--         ty-dim (liftType A) ≤⟨ n≤1+n (ty-dim (liftType A)) ⟩
--         suc (ty-dim (liftType A)) ∎
--         where
--           open ≤-Reasoning
--       open ≡-Reasoning
-- pdb-dim (Restr {submax = n} {Γ = Γ} {A = A} pdb) =
--   ty-dim A + suc n ≡⟨ +-suc (ty-dim A) n ⟩
--   suc (ty-dim A) + n ≡⟨ pdb-dim pdb ⟩
--   ctx-dim Γ ∎
--     where
--       open ≡-Reasoning

-- pd-dim : {Γ : Ctx n} → {dim : ℕ} → (Γ ⊢pd₀ dim) → dim ≡ ctx-dim Γ
-- pd-dim (Finish pdb) = pdb-dim pdb
