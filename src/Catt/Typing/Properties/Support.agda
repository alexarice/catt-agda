{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.Properties.Support (index : ℕ)
                                      (rule : Fin index → Rule)
                                      (supp-rule : ∀ i a → P.SupportRule index rule {i} a) where

open import Catt.Syntax
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Typing index rule
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Bool using (Bool; true; false)
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Tree
open import Tactic.MonoidSolver

open ≡-Reasoning

EqSuppTy : A ≈[ Γ ]ty B → SuppTy Γ A ≡ SuppTy Γ B
EqSuppTm : s ≈[ Γ ]tm t → SuppTm Γ s ≡ SuppTm Γ t
EqSuppSub : σ ≈[ Γ ]s τ → SuppSub Γ σ ≡ SuppSub Γ τ

EqSuppTy Star≈ = refl
EqSuppTy (Arr≈ {s = s} {Γ = Γ} {s′} {A} {A′} {t} {t′} p q r) = begin
  DC Γ (FVTy A ∪ FVTm s ∪ FVTm t)
    ≡⟨ DC-cup Γ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  DC Γ (FVTy A ∪ FVTm s) ∪ DC Γ (FVTm t)
    ≡⟨ cong (_∪ DC Γ (FVTm t)) (DC-cup Γ (FVTy A) (FVTm s)) ⟩
  DC Γ (FVTy A) ∪ DC Γ (FVTm s) ∪ DC Γ (FVTm t)
    ≡⟨ cong₂ _∪_ (cong₂ _∪_ (EqSuppTy q) (EqSuppTm p)) (EqSuppTm r) ⟩
  DC Γ (FVTy A′) ∪ SuppTm Γ s′ ∪ SuppTm Γ t′
    ≡˘⟨ cong (_∪ DC Γ (FVTm t′)) (DC-cup Γ (FVTy A′) (FVTm s′)) ⟩
  DC Γ (FVTy A′ ∪ FVTm s′) ∪ DC Γ (FVTm t′)
    ≡˘⟨ DC-cup Γ (FVTy A′ ∪ FVTm s′) (FVTm t′) ⟩
  DC Γ (FVTy A′ ∪ FVTm s′ ∪ FVTm t′) ∎

EqSuppTm (Var≈ x) with toℕ-injective x
... | refl = refl
EqSuppTm (Sym≈ p) = sym (EqSuppTm p)
EqSuppTm (Trans≈ p q) = trans (EqSuppTm p) (EqSuppTm q)
EqSuppTm (Coh≈ p q) = EqSuppSub q
EqSuppTm (Rule≈ i a x) = supp-rule i a x

EqSuppSub (Null≈ x) = EqSuppTy x
EqSuppSub (Ext≈ {σ = σ} {Δ = Δ} {τ = τ} {s} {t} p x) = begin
  DC Δ (FVSub σ ∪ FVTm s)
    ≡⟨ DC-cup Δ (FVSub σ) (FVTm s) ⟩
  DC Δ (FVSub σ) ∪ DC Δ (FVTm s)
    ≡⟨ cong₂ _∪_ (EqSuppSub p) (EqSuppTm x) ⟩
  DC Δ (FVSub τ) ∪ DC Δ (FVTm t)
    ≡˘⟨ DC-cup Δ (FVSub τ) (FVTm t) ⟩
  DC Δ (FVSub τ ∪ FVTm t) ∎

SuppTyFV : Typing-Ty Γ A → SuppTy Γ A ≡ FVTy A
SuppSubFV : Typing-Sub Γ Δ σ → SuppSub Δ σ ≡ FVSub σ
SuppTmChar : Typing-Tm Γ t A → SuppTm Γ t ≡ SuppTy Γ A ∪ FVTm t
SuppTmChar′ : Typing-Tm Γ t A → Typing-Ty Γ A → SuppTm Γ t ≡ FVTy A ∪ FVTm t

SuppTyFV TyStar = DC-empty _
SuppTyFV (TyArr {n} {Γ = Γ} {s} {A} {t} sty Aty tty) = begin
  DC Γ (FVTy A ∪ FVTm s ∪ FVTm t)
    ≡⟨ DC-cup Γ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  DC Γ (FVTy A ∪ FVTm s) ∪ SuppTm Γ t
    ≡⟨ cong (_∪ SuppTm Γ t) (DC-cup Γ (FVTy A) (FVTm s)) ⟩
  SuppTy Γ A ∪ SuppTm Γ s ∪ SuppTm Γ t
    ≡⟨ cong₂ _∪_ (cong₂ _∪_ (SuppTyFV Aty) (SuppTmChar′ sty Aty)) (SuppTmChar′ tty Aty) ⟩
  FVTy A ∪ (FVTy A ∪ FVTm s) ∪ (FVTy A ∪ FVTm t)
    ≡⟨ solve (∪-monoid {n}) ⟩
  FVTy A ∪ FVTy A ∪ (FVTm s ∪ FVTy A) ∪ FVTm t
    ≡⟨ cong₂ (λ a b → a ∪ b ∪ FVTm t) (∪-idem (FVTy A)) (∪-comm (FVTm s) (FVTy A)) ⟩
  FVTy A ∪ (FVTy A ∪ FVTm s) ∪ FVTm t
    ≡⟨ solve (∪-monoid {n}) ⟩
  FVTy A ∪ FVTy A ∪ FVTm s ∪ FVTm t
    ≡⟨ cong (λ a → a ∪ FVTm s ∪ FVTm t) (∪-idem (FVTy A)) ⟩
  FVTy A ∪ FVTm s ∪ FVTm t ∎

SuppSubFV (TyNull x) = SuppTyFV x
SuppSubFV {Δ = Δ} (TyExt {σ = σ} {A = A} {t = t} σty Aty tty) = begin
  DC Δ (FVSub σ ∪ FVTm t)
    ≡⟨ DC-cup Δ (FVSub σ) (FVTm t) ⟩
  SuppSub Δ σ ∪ SuppTm Δ t
    ≡⟨ cong (SuppSub Δ σ ∪_) (SuppTmChar tty) ⟩
  SuppSub Δ σ ∪ (SuppTy Δ (A [ σ ]ty) ∪ FVTm t)
    ≡˘⟨ ∪-assoc (SuppSub Δ σ) (SuppTy Δ (A [ σ ]ty)) (FVTm t) ⟩
  SuppSub Δ σ ∪ SuppTy Δ (A [ σ ]ty) ∪ FVTm t
    ≡˘⟨ cong (_∪ FVTm t) (DC-cup Δ (FVSub σ) (FVTy (A [ σ ]ty))) ⟩
  DC Δ (FVSub σ ∪ FVTy (A [ σ ]ty)) ∪ FVTm t
    ≡˘⟨ cong (λ - → DC Δ - ∪ FVTm t) (FVTy-comp-⊆ A σ) ⟩
  SuppSub Δ σ ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (SuppSubFV σty) ⟩
  FVSub σ ∪ FVTm t ∎

SuppTmChar (TyVarZ {Γ = Γ} {A = A} {B = B} Aty p) = begin
  ewt (DC Γ (empty ∪ FVTy A))
    ≡⟨ cong (λ - → ewt (DC Γ -)) (∪-left-unit (FVTy A)) ⟩
  ewt (DC Γ (FVTy A))
    ≡˘⟨ cong ewt (∪-right-unit (SuppTy Γ A)) ⟩
  ewt (SuppTy Γ A ∪ empty)
    ≡˘⟨ cong (λ - → DC (Γ , A) - ∪ ewt empty) (supp-lift-ty A) ⟩
  SuppTy (Γ , A) (liftType A) ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) (EqSuppTy p) ⟩
  SuppTy (Γ , A) B ∪ ewt empty ∎

SuppTmChar (TyVarS {Γ = Γ} {A = A} {C = C} {B = B} i tty x) = begin
  ewf (SuppTm Γ (Var i))
    ≡⟨ cong ewf (SuppTmChar tty) ⟩
  ewf (SuppTy Γ A ∪ FVTm (Var i))
    ≡˘⟨ cong (λ - → DC (Γ , C) - ∪ ewf (FVTm (Var i))) (supp-lift-ty A) ⟩
  SuppTy (Γ , C) (liftType A) ∪ ewf (FVTm (Var i))
    ≡⟨ cong (_∪ ewf (FVTm (Var i))) (EqSuppTy x) ⟩
  SuppTy (Γ , C) B ∪ ewf (FVTm (Var i)) ∎

SuppTmChar {Γ = Γ} (TyCoh {A = A} {σ = σ} {B = B} Aty σty b s p) = begin
  SuppSub Γ σ
    ≡⟨ cong (DC Γ) (trans (FVTy-comp-⊆ A σ) (∪-comm (FVSub σ) (FVTy (A [ σ ]ty)))) ⟩
  DC Γ (FVTy (A [ σ ]ty) ∪ FVSub σ)
    ≡⟨ DC-cup Γ (FVTy (A [ σ ]ty)) (FVSub σ) ⟩
  SuppTy Γ (A [ σ ]ty) ∪ SuppSub Γ σ
    ≡⟨ cong (SuppTy Γ (A [ σ ]ty) ∪_) (SuppSubFV σty) ⟩
  SuppTy Γ (A [ σ ]ty) ∪ FVSub σ
    ≡⟨ cong (_∪ FVSub σ) (EqSuppTy p) ⟩
  SuppTy Γ B ∪ FVSub σ ∎

SuppTmChar′ {Γ = Γ} {t = t} {A = A} tty Aty = begin
  SuppTm Γ t
    ≡⟨ SuppTmChar tty ⟩
  SuppTy Γ A ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (SuppTyFV Aty) ⟩
  FVTy A ∪ FVTm t ∎

TransportVarSet-DC : {σ : Sub n m ⋆} → (xs : VarSet n) → Typing-Sub Γ Δ σ → DC Δ (TransportVarSet xs σ) ≡ TransportVarSet (DC Γ xs) σ
TransportVarSet-DC emp (TyNull x) = DC-empty _
TransportVarSet-DC (ewf xs) (TyExt σty Aty tty) = TransportVarSet-DC xs σty
TransportVarSet-DC {Γ = Γ , A} {Δ = Δ} (ewt xs) (TyExt {σ = σ} {t = t} σty Aty tty) = begin
  DC Δ (TransportVarSet xs σ ∪ FVTm t)
    ≡⟨ DC-cup Δ (TransportVarSet xs σ) (FVTm t) ⟩
  DC Δ (TransportVarSet xs σ) ∪ DC Δ (FVTm t)
    ≡⟨ cong₂ _∪_ (TransportVarSet-DC xs σty) (SuppTmChar tty) ⟩
  TransportVarSet (DC Γ xs) σ ∪ (SuppTy Δ (A [ σ ]ty) ∪ FVTm t)
    ≡˘⟨ ∪-assoc (TransportVarSet (DC Γ xs) σ) (SuppTy Δ (A [ σ ]ty)) (FVTm t) ⟩
  TransportVarSet (DC Γ xs) σ ∪ SuppTy Δ (A [ σ ]ty) ∪ FVTm t
    ≡˘⟨ cong (λ - → TransportVarSet (DC Γ xs) σ ∪ DC Δ - ∪ FVTm t) (TransportVarSet-ty A σ) ⟩
  TransportVarSet (DC Γ xs) σ ∪ DC Δ (TransportVarSet (FVTy A) σ) ∪ FVTm t
    ≡⟨ cong (λ - → TransportVarSet (DC Γ xs) σ ∪ - ∪ FVTm t) (TransportVarSet-DC (FVTy A) σty) ⟩
  TransportVarSet (DC Γ xs) σ ∪ TransportVarSet (DC Γ (FVTy A)) σ ∪ FVTm t
    ≡˘⟨ cong (_∪ FVTm t) (TransportVarSet-∪ (DC Γ xs) (DC Γ (FVTy A)) σ) ⟩
  TransportVarSet (DC Γ xs ∪ DC Γ (FVTy A)) σ ∪ FVTm t
    ≡˘⟨ cong (λ - → TransportVarSet - σ ∪ FVTm t) (DC-cup Γ xs (FVTy A)) ⟩
  TransportVarSet (DC Γ (xs ∪ FVTy A)) σ ∪ FVTm t ∎

supp-condition-preserved : (b : Bool)
                         → A ≈[ tree-to-ctx T ]ty B
                         → Typing-Ty (tree-to-ctx T) A
                         → Typing-Ty (tree-to-ctx T) B
                         → supp-condition b A T
                         → supp-condition b B T
supp-condition-preserved {A = A} {T = T} {B = B} false p Aty Bty sc = begin
  FVTy B
    ≡˘⟨ SuppTyFV Bty ⟩
  SuppTy (tree-to-ctx T) B
    ≡˘⟨ EqSuppTy p ⟩
  SuppTy (tree-to-ctx T) A
    ≡⟨ SuppTyFV Aty ⟩
  FVTy A
    ≡⟨ sc ⟩
  full ∎
supp-condition-preserved {T = T} true (Arr≈ p q r) (TyArr {s = s} {A} {t} sty Aty tty) (TyArr {s = s′} {B} {t′} sty′ Bty tty′) (nz ,, sc1 ,, sc2)
  = nz ,, l1 ,, l2
  where
    l1 : FVTy B ∪ FVTm s′ ≡ supp-bd (pred (tree-dim T)) T false
    l1 = begin
      FVTy B ∪ FVTm s′
        ≡˘⟨ SuppTmChar′ sty′ Bty ⟩
      SuppTm (tree-to-ctx T) s′
        ≡˘⟨ EqSuppTm p ⟩
      SuppTm (tree-to-ctx T) s
        ≡⟨ SuppTmChar′ sty Aty ⟩
      FVTy A ∪ FVTm s
        ≡⟨ sc1 ⟩
      supp-bd (pred (tree-dim T)) T false ∎

    l2 : FVTy B ∪ FVTm t′ ≡ supp-bd (pred (tree-dim T)) T true
    l2 = begin
      FVTy B ∪ FVTm t′
        ≡˘⟨ SuppTmChar′ tty′ Bty ⟩
      SuppTm (tree-to-ctx T) t′
        ≡˘⟨ EqSuppTm r ⟩
      SuppTm (tree-to-ctx T) t
        ≡⟨ SuppTmChar′ tty Aty ⟩
      FVTy A ∪ FVTm t
        ≡⟨ sc2 ⟩
      supp-bd (pred (tree-dim T)) T true ∎
