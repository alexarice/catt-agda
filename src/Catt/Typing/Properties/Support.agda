{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.Properties.Support (index : ℕ)
                                      (rule : Fin index → Rule)
                                      (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                      (supp-rule : ∀ i a → P.SupportRule index rule {i} a) where

open import Catt.Syntax
open import Catt.Typing index rule
open P index rule
open import Catt.Support
open import Catt.Support.Properties
open import Relation.Binary.PropositionalEquality
open import Catt.Dimension
open import Catt.Globular.Typing index rule lift-rule
open import Data.Product renaming (_,_ to _,,_)
open import Tactic.MonoidSolver
import Relation.Binary.Reasoning.PartialOrder as PReasoning
open import Data.Unit
open import Data.Fin.Properties using (toℕ-injective)
open ≡-Reasoning

tm-is-supporting : (tty : Typing-Tm Γ t A) → Supporting-Tm tty
ty-is-supporting : (Aty : Typing-Ty Γ A) → Supporting-Ty Aty
sub-is-supporting : (σty : Typing-Sub Γ Δ σ) → Supporting-Sub σty

tm-eq-supp : (p : s ≈[ Γ ]tm t) → Preserve-Supp-Tm p
ty-eq-supp : (p : A ≈[ Γ ]ty B) → Preserve-Supp-Ty p
sub-eq-supp : (p : σ ≈[ Γ ]s τ) → Preserve-Supp-Sub p

tm-is-supporting (TyVarZ Aty p) = ty-is-supporting Aty ,, ty-eq-supp p
tm-is-supporting (TyVarS i tty x) = (tm-is-supporting tty) ,, (ty-eq-supp x)
tm-is-supporting (TyCoh Aty σty b sc p) = ty-is-supporting Aty ,, sub-is-supporting σty ,, ty-eq-supp p

ty-is-supporting TyStar = tt
ty-is-supporting (TyArr sty Aty tty) = tm-is-supporting sty ,, ty-is-supporting Aty ,, tm-is-supporting tty

sub-is-supporting (TyNull Aty) = ty-is-supporting Aty
sub-is-supporting (TyExt σty Aty tty) = (sub-is-supporting σty) ,, ty-is-supporting Aty ,, tm-is-supporting tty

tm-eq-supp (Var≈ x) with toℕ-injective x
... | refl = refl
tm-eq-supp (Sym≈ p) = sym (tm-eq-supp p)
tm-eq-supp (Trans≈ p q) = trans (tm-eq-supp p) (tm-eq-supp q)
tm-eq-supp (Coh≈ x p) = sub-eq-supp p
tm-eq-supp (Rule≈ i a tty) = supp-rule i a tty (tm-is-supporting tty)

ty-eq-supp Star≈ = refl
ty-eq-supp (Arr≈ {s = s} {Γ} {s′} {A} {A′} {t} {t′} p q r) = begin
  SuppTy Γ (s ─⟨ A ⟩⟶ t)
    ≡⟨ DC-cup Γ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  DC Γ (FVTy A ∪ FVTm s) ∪ SuppTm Γ t
    ≡⟨ cong (_∪ SuppTm Γ t) (DC-cup Γ (FVTy A) (FVTm s)) ⟩
  SuppTy Γ A ∪ SuppTm Γ s ∪ SuppTm Γ t
    ≡⟨ cong₂ _∪_ (cong₂ _∪_ (ty-eq-supp q) (tm-eq-supp p)) (tm-eq-supp r) ⟩
  SuppTy Γ A′ ∪ SuppTm Γ s′ ∪ SuppTm Γ t′
    ≡˘⟨ cong (_∪ SuppTm Γ t′) (DC-cup Γ (FVTy A′) (FVTm s′)) ⟩
  DC Γ (FVTy A′ ∪ FVTm s′) ∪ SuppTm Γ t′
    ≡˘⟨ DC-cup Γ (FVTy A′ ∪ FVTm s′) (FVTm t′) ⟩
  SuppTy Γ (s′ ─⟨ A′ ⟩⟶ t′) ∎

sub-eq-supp (Null≈ x) = ty-eq-supp x
sub-eq-supp (Ext≈ {σ = σ} {Δ = Δ} {τ = τ} {s} {t} p x) = begin
  SuppSub Δ ⟨ σ , s ⟩
    ≡⟨ DC-cup Δ (FVSub σ) (FVTm s) ⟩
  SuppSub Δ σ ∪ SuppTm Δ s
    ≡⟨ cong₂ _∪_ (sub-eq-supp p) (tm-eq-supp x) ⟩
  SuppSub Δ τ ∪ SuppTm Δ t
    ≡˘⟨ DC-cup Δ (FVSub τ) (FVTm t) ⟩
  SuppSub Δ ⟨ τ , t ⟩ ∎

supp-to-fv-tm : (tty : Typing-Tm Γ t A) → Supporting-Tm tty → SuppTm Γ t ≡ FVTy A ∪ FVTm t
supp-to-fv-ty : (Aty : Typing-Ty Γ A) → Supporting-Ty Aty → SuppTy Γ A ≡ FVTy A
supp-to-fv-sub : {σ : Sub n m ⋆} → (σty : Typing-Sub Γ Δ σ) → Supporting-Sub σty → SuppSub Δ σ ≡ FVSub σ

supp-to-fv-tm (TyVarZ {Γ = Γ} {A = A} {B = B} Aty p) (st ,, st2) = begin
  ewt (DC Γ (empty ∪ FVTy A))
    ≡⟨ cong (λ - → ewt (DC Γ -)) (∪-left-unit (FVTy A)) ⟩
  ewt (DC Γ (FVTy A))
    ≡˘⟨ cong ewt (∪-right-unit (DC Γ (FVTy A))) ⟩
  DC (Γ , A) (ewf (FVTy A)) ∪ ewt empty
    ≡˘⟨ cong (λ - → DC (Γ , A) - ∪ ewt empty) (supp-lift-ty A) ⟩
  SuppTy (Γ , A) (liftType A) ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) st2 ⟩
  SuppTy (Γ , A) B ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) (supp-to-fv-ty {!!} {!!}) ⟩
  FVTy B ∪ ewt empty ∎
supp-to-fv-tm (TyVarS {Γ = Γ} {A = A} {B = B} i tty x) (st ,, st2) = begin
  ewf (SuppTm Γ (Var i))
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ cong (_∪ FVTm (Var (suc i))) (supp-to-fv-ty {!!} {!!}) ⟩
  FVTy B ∪ FVTm (Var (suc i)) ∎
supp-to-fv-tm (TyCoh x x₁ b x₂ x₃) st = {!!}

supp-to-fv-ty = {!!}

supp-to-fv-sub (TyNull x) st = {!!}
supp-to-fv-sub (TyExt σty x x₁) st = {!!}

{-
supp-to-fv-tm : (tty : Typing-Tm Γ t A) → Supporting-Tm tty → Supp (CtxTm t Γ) ≡ FVTy A ∪ FVTm t
supp-to-fv-ty : (Aty : Typing-Ty Γ A) → Supporting-Ty Aty → Supp (CtxTy A Γ) ≡ FVTy A
supp-to-fv-sub : {σ : Sub n m ⋆} → (σty : Typing-Sub Γ Δ σ) → Supporting-Sub σty → Supp (CtxSub σ Δ) ≡ FVSub σ

supp-to-fv-tm (TyVarZ {Γ = Γ} {A = A} {B = B} Aty p) st = begin
  ewt (Supp (CtxTy A Γ))
    ≡⟨ cong ewt (supp-to-fv-ty Aty (proj₁ st)) ⟩
  ewt (FVTy A)
    ≡˘⟨ cong ewt (∪-right-unit (FVTy A)) ⟩
  ewf (FVTy A) ∪ ewt empty
    ≡˘⟨ cong (_∪ ewt empty) (supp-lift-ty A) ⟩
  FVTy (liftType A) ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) (proj₂ st) ⟩
  FVTy B ∪ ewt empty ∎
  where
    open ≡-Reasoning
supp-to-fv-tm (TyVarS {Γ = Γ} {A = A} {C = C} {B = B} i tty x) st = begin
  ewf (Supp (CtxTm (Var i) Γ))
    ≡⟨ cong ewf (supp-to-fv-tm tty (proj₁ st)) ⟩
  ewf (FVTy A ∪ FVTm (Var i))
    ≡˘⟨ cong (_∪ ewf (FVTm (Var i))) (supp-lift-ty A) ⟩
  FVTy (liftType A) ∪ ewf (FVTm (Var i))
    ≡⟨ cong (_∪ ewf (trueAt i)) (proj₂ st) ⟩
  FVTy B ∪ ewf (trueAt i) ∎
  where
    open ≡-Reasoning
supp-to-fv-tm (TyCoh {T = T} {A = A} {Γ = Γ} {σ = σ} {B = B} Aty σty _ sc p) (a ,, b ,, c) = begin
  Supp (CtxSub σ Γ)
    ≡⟨ supp-to-fv-sub σty b ⟩
  FVSub σ
    ≡˘⟨ TransportVarSet-full σ ⟩
  TransportVarSet full σ
    ≡˘⟨ cong (λ - → TransportVarSet - σ) (∪-right-zero (FVTy A)) ⟩
  TransportVarSet (FVTy A ∪ full) σ
    ≡⟨ TransportVarSet-∪ (FVTy A) full σ ⟩
  TransportVarSet (FVTy A) σ ∪ TransportVarSet full σ
    ≡⟨ cong₂ _∪_ (TransportVarSet-ty A σ) (TransportVarSet-full σ) ⟩
  FVTy (A [ σ ]ty) ∪ FVSub σ
    ≡⟨ cong (_∪ FVSub σ) c ⟩
  FVTy B ∪ FVSub σ ∎
  where
    open ≡-Reasoning

supp-to-fv-ty TyStar st = refl
supp-to-fv-ty (TyArr {Γ = Γ} {s = s} {A = A} {t = t} sty Aty tty) (a ,, b ,, c) = begin
  Supp (CtxTy A Γ) ∪ Supp (CtxTm s Γ) ∪ Supp (CtxTm t Γ)
    ≡⟨ cong₂ _∪_ (cong₂ _∪_ (supp-to-fv-ty Aty b) (supp-to-fv-tm sty a)) (supp-to-fv-tm tty c) ⟩
  FVTy A ∪ (FVTy A ∪ FVTm s) ∪ (FVTy A ∪ FVTm t)
    ≡⟨ solve (∪-monoid {ctxLength Γ}) ⟩
  (FVTy A ∪ FVTy A) ∪ (FVTm s ∪ FVTy A) ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (cong₂ _∪_ (∪-idem (FVTy A)) (∪-comm (FVTm s) (FVTy A))) ⟩
  FVTy A ∪ (FVTy A ∪ FVTm s) ∪ FVTm t
    ≡⟨ solve (∪-monoid {ctxLength Γ}) ⟩
  (FVTy A ∪ FVTy A) ∪ FVTm s ∪ FVTm t
    ≡⟨ cong (λ - → - ∪ FVTm s ∪ FVTm t) (∪-idem (FVTy A)) ⟩
  FVTy A ∪ FVTm s ∪ FVTm t ∎
  where
    open ≡-Reasoning

supp-to-fv-sub (TyNull x) st = supp-to-fv-ty x st
supp-to-fv-sub (TyExt {Δ = Δ} {σ = σ} {A = A} {t = t} σty Aty tty) (a ,, b ,, c) = begin
  Supp (CtxSub σ Δ) ∪ Supp (CtxTm t Δ)
    ≡⟨ cong₂ _∪_ (supp-to-fv-sub σty a) (supp-to-fv-tm tty c) ⟩
  FVSub σ ∪ (FVTy (A [ σ ]ty) ∪ FVTm t)
    ≡˘⟨ ∪-assoc (FVSub σ) (FVTy (A [ σ ]ty)) (FVTm t) ⟩
  FVSub σ ∪ FVTy (A [ σ ]ty) ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (sym lem) ⟩
  FVSub σ ∪ FVTm t ∎
  where
    lem : FVTy (A [ σ ]ty) ⊆ FVSub σ
    lem = begin
      FVTy (A [ σ ]ty)
        ≡˘⟨ TransportVarSet-ty A σ ⟩
      TransportVarSet (FVTy A) σ
        ≤⟨ ⊆-TransportVarSet σ (⊆-top (FVTy A)) ⟩
      TransportVarSet full σ
        ≡⟨ TransportVarSet-full σ ⟩
      FVSub σ ∎
      where open PReasoning (⊆-poset _)
    open ≡-Reasoning
-}
