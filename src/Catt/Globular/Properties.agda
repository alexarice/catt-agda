{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Globular.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Globular
open import Catt.Suspension
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Data.Fin using (Fin;suc;zero;inject₁)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning

-- src-subbed_:_(A_:_Ty_Γ_(suc_(suc_d)))_→_(σ_:_Sub_Γ_Δ)_→_(ty-src_A)_[_σ_]tm_≡_ty-src_(A_[_σ_]ty)
-- src-subbed_(s_─⟨_A_⟩⟶_t)_σ_=_refl

-- tgt-subbed_:_(A_:_Ty_Γ_(suc_(suc_d)))_→_(σ_:_Sub_Γ_Δ)_→_ty-tgt_A_[_σ_]tm_≡_ty-tgt_(A_[_σ_]ty)
-- tgt-subbed_(s_─⟨_A_⟩⟶_t)_σ_=_refl

-- base-subbed_:_(A_:_Ty_Γ_(suc_(suc_d)))_→_(σ_:_Sub_Γ_Δ)_→_ty-base_A_[_σ_]ty_≡_ty-base_(A_[_σ_]ty)
-- base-subbed_(s_─⟨_A_⟩⟶_t)_σ_=_refl

tm-to-ty-≃ : Γ ≃c Δ → s ≃tm t → tm-to-ty Γ s ≃ty tm-to-ty Δ t
tm-to-ty-≃ p (Var≃ x y) = ‼-≃ _ _ y p
tm-to-ty-≃ p (Coh≃ q r s) = sub-action-≃-ty r s

sub-dim : (σ : Sub n m ⋆) → (A : Ty n) → ty-dim A ≡ ty-dim (A [ σ ]ty)
sub-dim σ ⋆ = refl
sub-dim σ (s ─⟨ A ⟩⟶ t) = cong suc (sub-dim σ A)

sub-dim′ : (σ : Sub n m B) → (A : Ty n) → ty-dim A + ty-dim B ≡ ty-dim (A [ σ ]ty)
sub-dim′ σ ⋆ = refl
sub-dim′ σ (s ─⟨ A ⟩⟶ t) = cong suc (sub-dim′ σ A)

ty-dim-≃ : A ≃ty B → ty-dim A ≡ ty-dim B
ty-dim-≃ (Star≃ x) = refl
ty-dim-≃ (Arr≃ _ p _) = cong suc (ty-dim-≃ p)

susp-dim : (A : Ty n) → ty-dim (suspTy A) ≡ suc (ty-dim A)
susp-dim ⋆ = refl
susp-dim (s ─⟨ A ⟩⟶ t) = cong suc (susp-dim A)

lift-ty-dim : (A : Ty n) → ty-dim (liftType A) ≡ ty-dim A
lift-ty-dim ⋆ = refl
lift-ty-dim (s ─⟨ A ⟩⟶ t) = cong suc (lift-ty-dim A)

ty-dim-ty-base : (A : Ty n) → ty-dim (ty-base A) ≡ pred (ty-dim A)
ty-dim-ty-base ⋆ = refl
ty-dim-ty-base (s ─⟨ A ⟩⟶ t) = refl

tm-to-ty-coh-sub : (S : Tree n) → (B : Ty (suc n)) → (τ : Sub (suc n) m ⋆) → (Δ : Ctx l) → (σ : Sub m l A) → tm-to-ty Δ (Coh S B τ [ σ ]tm) ≃ty B [ σ ∘ τ ]ty
tm-to-ty-coh-sub {A = ⋆} S B τ Δ σ = refl≃ty
tm-to-ty-coh-sub {A = s ─⟨ A ⟩⟶ t} S B τ Δ σ = begin
  < tm-to-ty Δ (Coh (suspTree S) (suspTy B) (suspSub τ) [ unrestrict σ ]tm) >ty
    ≈⟨ tm-to-ty-coh-sub (suspTree S) (suspTy B) (suspSub τ) Δ (unrestrict σ) ⟩
  < suspTy B [ unrestrict σ ∘ suspSub τ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (refl≃ty {A = suspTy B}) (unrestrict-comp σ τ) ⟩
  < suspTy B [ unrestrict (σ ∘ τ) ]ty >ty
    ≈˘⟨ unrestrict-comp-ty B (σ ∘ τ) ⟩
  < B [ σ ∘ τ ]ty >ty ∎
  where
    open Reasoning ty-setoid

susp-tm-height : (t : Tm n) → (Δ : Ctx n) → tm-height (suspCtx Δ) (suspTm t) ≡ suc (tm-height Δ t)
susp-tm-height (Var zero) (Δ , A) = begin
  ty-dim (liftType (suspTy A))
    ≡⟨ lift-ty-dim (suspTy A) ⟩
  ty-dim (suspTy A)
    ≡⟨ susp-dim A ⟩
  suc (ty-dim A)
    ≡˘⟨ cong suc (lift-ty-dim A) ⟩
  suc (ty-dim (liftType A)) ∎
  where
    open ≡-Reasoning
susp-tm-height (Var (suc i)) (Δ , A) = begin
  ty-dim (liftType (suspCtx Δ ‼ inject₁ (inject₁ i)))
    ≡⟨ lift-ty-dim (suspCtx Δ ‼ inject₁ (inject₁ i)) ⟩
  ty-dim (suspCtx Δ ‼ inject₁ (inject₁ i))
    ≡⟨ susp-tm-height (Var i) Δ ⟩
  suc (ty-dim (Δ ‼ i))
    ≡˘⟨ cong suc (lift-ty-dim (Δ ‼ i)) ⟩
  suc (ty-dim (liftType (Δ ‼ i))) ∎
  where
    open ≡-Reasoning
susp-tm-height (Coh S A σ) Δ = begin
  ty-dim (suspTy A [ suspSub σ ]ty)
    ≡˘⟨ cong ty-dim (≃ty-to-≡ (susp-functorial-ty σ A)) ⟩
  ty-dim (suspTy (A [ σ ]ty))
    ≡⟨ susp-dim (A [ σ ]ty) ⟩
  suc (ty-dim (A [ σ ]ty)) ∎
  where
    open ≡-Reasoning

tm-height-≃ : (Γ : Ctx n) → s ≃tm t → tm-height Γ s ≡ tm-height Γ t
tm-height-≃ Γ p with ≃tm-to-≡ p
... | refl = refl

ty-src-≃ : A ≃ty B → ty-src A ≃tm ty-src B
ty-src-≃ (Star≃ p) = Var≃ p refl
ty-src-≃ (Arr≃ p q r) = p

ty-tgt-≃ : A ≃ty B → ty-tgt A ≃tm ty-tgt B
ty-tgt-≃ (Star≃ p) = Var≃ p refl
ty-tgt-≃ (Arr≃ p q r) = r

ty-base-≃ : A ≃ty B → ty-base A ≃ty ty-base B
ty-base-≃ (Star≃ p) = Star≃ p
ty-base-≃ (Arr≃ p q r) = q

ty-base-sub : (A : Ty n) → (σ : Sub n m ⋆) → ty-base A [ σ ]ty ≃ty ty-base (A [ σ ]ty)
ty-base-sub ⋆ σ = refl≃ty
ty-base-sub (s ─⟨ A ⟩⟶ t) σ = refl≃ty

ty-src-sub : (A : Ty (suc n)) → (σ : Sub (suc n) (suc m) ⋆) → (ty-dim A > 0) → ty-src A [ σ ]tm ≃tm ty-src (A [ σ ]ty)
ty-src-sub (s ─⟨ A ⟩⟶ t) σ p = refl≃tm

ty-tgt-sub : (A : Ty (suc n)) → (σ : Sub (suc n) (suc m) ⋆) → (ty-dim A > 0) → ty-tgt A [ σ ]tm ≃tm ty-tgt (A [ σ ]ty)
ty-tgt-sub (s ─⟨ A ⟩⟶ t) σ p = refl≃tm

-- ty-src-lift : (A : Ty n (suc d)) → ty-src (liftType A) ≃tm liftTerm (ty-src A)
-- ty-src-lift (s ─⟨ A ⟩⟶ t) = refl≃tm

-- ty-tgt-lift : (A : Ty n (suc d)) → ty-tgt (liftType A) ≃tm liftTerm (ty-tgt A)
-- ty-tgt-lift (s ─⟨ A ⟩⟶ t) = refl≃tm

-- ty-base-lift : (A : Ty n (suc d)) → ty-base (liftType A) ≃ty liftType (ty-base A)
-- ty-base-lift (s ─⟨ A ⟩⟶ t) = refl≃ty

-- get-right-base-tm-≃ : {A : Ty n d} {B : Ty n′ d′} → .⦃ _ : NonZero′ d ⦄ → .⦃ _ : NonZero′ d′ ⦄ → A ≃ty B → get-right-base-tm A ≃tm get-right-base-tm B
-- get-right-base-tm-≃ {d = suc zero} {d′ = suc zero} p = ty-tgt-≃ p
-- get-right-base-tm-≃ {d = suc zero} {d′ = suc (suc d′)} (Arr≃ _ () _)
-- get-right-base-tm-≃ {d = suc (suc d)} {d′ = suc zero} (Arr≃ _ () _)
-- get-right-base-tm-≃ {d = suc (suc d)} {d′ = suc (suc d′)} p = get-right-base-tm-≃ (ty-base-≃ p)

-- get-right-base-tm-lift : (A : Ty n d) → .⦃ _ : NonZero′ d ⦄ → get-right-base-tm (liftType A) ≃tm liftTerm (get-right-base-tm A)
-- get-right-base-tm-lift {d = suc zero} A = ty-tgt-lift A
-- get-right-base-tm-lift {d = suc (suc d)} A = trans≃tm (get-right-base-tm-≃ (ty-base-lift A)) (get-right-base-tm-lift (ty-base A))

-- get-right-base-ty-base : (A : Ty n (suc d)) → .⦃ _ : NonZero′ d ⦄ → get-right-base-tm (ty-base A) ≃tm get-right-base-tm A
-- get-right-base-ty-base {d = suc d} A = refl≃tm

-- get-right-base-subbed : (A : Ty n d) → .⦃ _ : NonZero′ d ⦄ → (σ : Sub n m) → get-right-base-tm (A [ σ ]ty) ≃tm get-right-base-tm A [ σ ]tm
-- get-right-base-subbed {d = suc zero} (s ─⟨ A ⟩⟶ t) σ = refl≃tm
-- get-right-base-subbed {d = suc (suc d)} (s ─⟨ A ⟩⟶ t) σ = get-right-base-subbed A σ

-- tm-to-ty-sub : (t : Tm Γ (suc d)) → (σ : Sub Γ Δ) → tm-to-ty (t [ σ ]tm) ≃ty tm-to-ty t [ σ ]ty
-- tm-to-ty-sub (Var i) σ = {!!}
--   where
--     lem : (i : Fin (ctxLength Γ)) → (σ : Sub Γ Δ) → tm-to-ty (Var i [ σ ]tm) ≃ty (Γ ‼ i [ σ ]ty)
--     lem {Γ = Γ , A} zero ⟨ σ , t ⟩ = trans≃ty {!!} (sym≃ty (lift-sub-comp-lem-ty σ A))
--     lem {Γ = Γ , A} (suc i) ⟨ σ , t ⟩ = {!!}
-- tm-to-ty-sub (Coh Δ A x τ) σ = assoc-ty σ τ

BoundedSucTm : BoundedTm d Γ t → BoundedTm (suc d) Γ t
BoundedSucTy : BoundedTy d Γ A → BoundedTy (suc d) Γ A
BoundedSucSub : BoundedSub d Γ σ → BoundedSub (suc d) Γ σ

BoundedSucTm (VarBoundZ p) = VarBoundZ (BoundedSucTy p)
BoundedSucTm (VarBoundS i p) = VarBoundS i (BoundedSucTm p)
BoundedSucTm (CohBound S p q) = CohBound S (BoundedSucTy p) (BoundedSucSub q)

BoundedSucTy StarBound = StarBound
BoundedSucTy (ArrBound a b c) = ArrBound (BoundedSucTm a) (BoundedSucTy b) (BoundedSucTm c)

BoundedSucSub NullBound = NullBound
BoundedSucSub (ExtBound b x) = ExtBound (BoundedSucSub b) (BoundedSucTm x)

BoundedLiftTm : BoundedTm d Γ t → BoundedTm d (Γ , A) (liftTerm t)
BoundedLiftTy : BoundedTy d Γ B → BoundedTy d (Γ , A) (liftType B)
BoundedLiftSub : BoundedSub d Γ σ → BoundedSub d (Γ , A) (liftSub σ)

BoundedLiftTm (VarBoundZ p) = VarBoundS zero (VarBoundZ p)
BoundedLiftTm (VarBoundS i p) = VarBoundS (suc i) (VarBoundS i p)
BoundedLiftTm (CohBound S p q) = CohBound S p (BoundedLiftSub q)

BoundedLiftTy StarBound = StarBound
BoundedLiftTy (ArrBound p q r) = ArrBound (BoundedLiftTm p) (BoundedLiftTy q) (BoundedLiftTm r)

BoundedLiftSub NullBound = NullBound
BoundedLiftSub (ExtBound b x) = ExtBound (BoundedLiftSub b) (BoundedLiftTm x)

BoundedGetFst : BoundedTm d (suspCtx Γ) getFst
BoundedGetSnd : BoundedTm d (suspCtx Γ) getSnd

BoundedGetFst {Γ = ∅} = VarBoundS zero (VarBoundZ StarBound)
BoundedGetFst {Γ = Γ , A} = VarBoundS (Data.Fin.fromℕ (suc _)) BoundedGetFst
BoundedGetSnd {Γ = ∅} = VarBoundZ StarBound
BoundedGetSnd {Γ = Γ , A} = VarBoundS (inject₁ (Data.Fin.fromℕ _)) BoundedGetSnd

BoundedSuspTm : BoundedTm d Γ t → BoundedTm (suc d) (suspCtx Γ) (suspTm t)
BoundedSuspTy : BoundedTy d Γ A → BoundedTy (suc d) (suspCtx Γ) (suspTy A)
BoundedSuspSub : BoundedSub d Γ σ → BoundedSub (suc d) (suspCtx Γ) (suspSub σ)

BoundedSuspTm (VarBoundZ x) = VarBoundZ (BoundedSuspTy x)
BoundedSuspTm (VarBoundS i b) = VarBoundS (inject₁ (inject₁ i)) (BoundedSuspTm b)
BoundedSuspTm (CohBound S p q) = CohBound (suspTree S) (BoundedSuspTy p) (BoundedSuspSub q)

BoundedSuspTy StarBound = ArrBound BoundedGetFst StarBound BoundedGetSnd
BoundedSuspTy (ArrBound p q r) = ArrBound (BoundedSuspTm p) (BoundedSuspTy q) (BoundedSuspTm r)

BoundedSuspSub NullBound = ExtBound (ExtBound NullBound BoundedGetFst) BoundedGetSnd
BoundedSuspSub (ExtBound b x) = ExtBound (BoundedSuspSub b) (BoundedSuspTm x)
