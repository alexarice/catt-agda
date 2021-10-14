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

tm-is-supporting : (tty : Typing-Tm Γ t A) → Supporting-Tm tty
ty-is-supporting : (Aty : Typing-Ty Γ A) → Supporting-Ty Aty
sub-is-supporting : (σty : Typing-Sub Γ Δ σ) → Supporting-Sub σty

tm-eq-supp : s ≈[ Γ ]tm t → FVTmTy Γ s ≡ FVTmTy Γ t
ty-eq-supp : A ≈[ Γ ]ty B → FVTy A ≡ FVTy B
sub-eq-supp : σ ≈[ Γ ]s τ → FVSub σ ≡ FVSub τ

tm-is-supporting tty = {!!}

ty-is-supporting Aty = {!!}

sub-is-supporting σty = {!!}

tm-eq-supp (Var≈ x) = {!!}
tm-eq-supp (Sym≈ p) = sym (tm-eq-supp p)
tm-eq-supp (Trans≈ p q) = trans (tm-eq-supp p) (tm-eq-supp q)
tm-eq-supp (Coh≈ x p) = {!!}
tm-eq-supp (Rule≈ i a tty) = supp-rule i a tty (tm-is-supporting tty)

ty-eq-supp Star≈ = refl
ty-eq-supp (Arr≈ p q r) = {!!}

sub-eq-supp (Null≈ x) = ty-eq-supp x
sub-eq-supp (Ext≈ p x) = {!!}

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
