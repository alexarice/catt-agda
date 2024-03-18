open import Catt.Typing.Rule

module Catt.Typing.Properties.Support (ops : Op)
                                      (rules : RuleSet)
                                      (supp-cond : SupportCond ops rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Globular
open import Catt.Pasting
open import Catt.Tree

open import Catt.Typing ops rules

open import Catt.Support
open import Catt.Support.Properties

import Algebra.Solver.IdempotentCommutativeMonoid as Solver

open ≡-Reasoning

EqSuppTy : A ≈[ Γ ]ty B → SuppTy Γ A ≡ SuppTy Γ B
EqSuppTm : s ≈[ Γ ]tm t → SuppTm Γ s ≡ SuppTm Γ t
EqSuppSub : σ ≈[ Γ ]s τ → SuppSub Γ σ ≡ SuppSub Γ τ

EqSuppTy Star≈ = refl
EqSuppTy (Arr≈ {s = s} {Γ = Γ} {s′} {A} {A′} {t} {t′} p q r) = begin
  DC Γ (FVTy A ∪ FVTm s ∪ FVTm t)
    ≡⟨ DC-∪ Γ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  DC Γ (FVTy A ∪ FVTm s) ∪ DC Γ (FVTm t)
    ≡⟨ cong (_∪ DC Γ (FVTm t)) (DC-∪ Γ (FVTy A) (FVTm s)) ⟩
  DC Γ (FVTy A) ∪ DC Γ (FVTm s) ∪ DC Γ (FVTm t)
    ≡⟨ cong₂ _∪_ (cong₂ _∪_ (EqSuppTy q) (EqSuppTm p)) (EqSuppTm r) ⟩
  DC Γ (FVTy A′) ∪ SuppTm Γ s′ ∪ SuppTm Γ t′
    ≡˘⟨ cong (_∪ DC Γ (FVTm t′)) (DC-∪ Γ (FVTy A′) (FVTm s′)) ⟩
  DC Γ (FVTy A′ ∪ FVTm s′) ∪ DC Γ (FVTm t′)
    ≡˘⟨ DC-∪ Γ (FVTy A′ ∪ FVTm s′) (FVTm t′) ⟩
  DC Γ (FVTy A′ ∪ FVTm s′ ∪ FVTm t′) ∎

EqSuppTm (Var≈ x) with toℕ-injective x
... | refl = refl
EqSuppTm (Sym≈ p) = sym (EqSuppTm p)
EqSuppTm (Trans≈ p q) = trans (EqSuppTm p) (EqSuppTm q)
EqSuppTm (Coh≈ p q) = EqSuppSub q
EqSuppTm (Rule≈ r p tty) = supp-cond p tty

EqSuppSub (Null≈ x) = EqSuppTy x
EqSuppSub (Ext≈ {σ = σ} {Δ = Δ} {τ = τ} {s} {t} p x) = begin
  DC Δ (FVSub σ ∪ FVTm s)
    ≡⟨ DC-∪ Δ (FVSub σ) (FVTm s) ⟩
  DC Δ (FVSub σ) ∪ DC Δ (FVTm s)
    ≡⟨ cong₂ _∪_ (EqSuppSub p) (EqSuppTm x) ⟩
  DC Δ (FVSub τ) ∪ DC Δ (FVTm t)
    ≡˘⟨ DC-∪ Δ (FVSub τ) (FVTm t) ⟩
  DC Δ (FVSub τ ∪ FVTm t) ∎

SuppTyFV : Typing-Ty Γ A → SuppTy Γ A ≡ FVTy A
SuppSubFV : Typing-Sub Γ Δ σ → SuppSub Δ σ ≡ FVSub σ
SuppTmChar : Typing-Tm Γ t A → SuppTm Γ t ≡ SuppTy Γ A ∪ FVTm t
SuppTmChar′ : Typing-Tm Γ t A → Typing-Ty Γ A → SuppTm Γ t ≡ FVTy A ∪ FVTm t
SuppTmChar″ : Typing-Tm Γ t A → Typing-Ty Γ A → SuppTm Γ t ≡ SuppTy Γ A ∪ SuppTm Γ t

SuppTyFV TyStar = DC-empty _
SuppTyFV (TyArr {n} {Γ = Γ} {s} {A} {t} sty Aty tty) = begin
  DC Γ (FVTy A ∪ FVTm s ∪ FVTm t)
    ≡⟨ DC-∪ Γ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  DC Γ (FVTy A ∪ FVTm s) ∪ SuppTm Γ t
    ≡⟨ cong (_∪ SuppTm Γ t) (DC-∪ Γ (FVTy A) (FVTm s)) ⟩
  SuppTy Γ A ∪ SuppTm Γ s ∪ SuppTm Γ t
    ≡⟨ cong₂ _∪_ (cong₂ _∪_ (SuppTyFV Aty) (SuppTmChar′ sty Aty)) (SuppTmChar′ tty Aty) ⟩
  FVTy A ∪ (FVTy A ∪ FVTm s) ∪ (FVTy A ∪ FVTm t)
    ≡⟨ prove 3 ((var 0F ⊕ (var 0F ⊕ var 1F)) ⊕ (var 0F ⊕ var 2F))
               ((var 0F ⊕ var 1F) ⊕ var 2F)
               (FVTy A ∷ FVTm s ∷ FVTm t ∷ emp) ⟩
  FVTy A ∪ FVTm s ∪ FVTm t ∎
  where
    open Solver ∪-idempotentCommutativeMonoid

SuppSubFV (TyNull x) = SuppTyFV x
SuppSubFV {Δ = Δ} (TyExt {σ = σ} {t = t} {A = A} σty tty) = begin
  DC Δ (FVSub σ ∪ FVTm t)
    ≡⟨ DC-∪ Δ (FVSub σ) (FVTm t) ⟩
  SuppSub Δ σ ∪ SuppTm Δ t
    ≡⟨ cong (SuppSub Δ σ ∪_) (SuppTmChar tty) ⟩
  SuppSub Δ σ ∪ (SuppTy Δ (A [ σ ]ty) ∪ FVTm t)
    ≡˘⟨ ∪-assoc (SuppSub Δ σ) (SuppTy Δ (A [ σ ]ty)) (FVTm t) ⟩
  SuppSub Δ σ ∪ SuppTy Δ (A [ σ ]ty) ∪ FVTm t
    ≡˘⟨ cong (_∪ FVTm t) (DC-∪ Δ (FVSub σ) (FVTy (A [ σ ]ty))) ⟩
  DC Δ (FVSub σ ∪ FVTy (A [ σ ]ty)) ∪ FVTm t
    ≡˘⟨ cong (λ - → DC Δ - ∪ FVTm t) (FVTy-comp-⊆ A σ) ⟩
  SuppSub Δ σ ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (SuppSubFV σty) ⟩
  FVSub σ ∪ FVTm t ∎

SuppTmChar (TyConv {Γ = Γ} {s = s} {A = A} {B = B} tty p) = begin
  SuppTm Γ s
    ≡⟨ SuppTmChar tty ⟩
  SuppTy Γ A ∪ FVTm s
    ≡⟨ cong (_∪ FVTm s) (EqSuppTy p) ⟩
  SuppTy Γ B ∪ FVTm s ∎

SuppTmChar (TyVar {Γ = Γ , A} zero) = begin
  ewt (DC Γ (empty ∪ FVTy A))
    ≡⟨ cong (λ - → ewt (DC Γ -)) (∪-left-unit (FVTy A)) ⟩
  ewt (SuppTy Γ A)
    ≡˘⟨ cong ewt (∪-right-unit (SuppTy Γ A)) ⟩
  ewt (SuppTy Γ A ∪ empty)
    ≡˘⟨ cong (λ - → DC (Γ , A) - ∪ ewt empty) (fv-wk-ty A) ⟩
  SuppTy (Γ , A) (wk-ty A) ∪ ewt empty ∎

SuppTmChar (TyVar {Γ = Γ , A} (suc i)) = begin
  ewf (SuppTm Γ (Var i))
    ≡⟨ cong ewf (SuppTmChar (TyVar i)) ⟩
  ewf (SuppTy Γ (Γ ‼ i) ∪ FVTm (Var i))
    ≡˘⟨ cong (λ - → DC (Γ , A) - ∪ ewf (FVTm (Var i))) (fv-wk-ty (Γ ‼ i)) ⟩
  SuppTy (Γ , A) (wk-ty (Γ ‼ i)) ∪ ewf (FVTm (Var i)) ∎

SuppTmChar {Γ = Γ} (TyCoh {Δ = Δ} {A = A} {σ = σ} x Aty σty) = begin
  SuppSub Γ σ
    ≡⟨ cong (DC Γ) (trans (FVTy-comp-⊆ A σ) (∪-comm (FVSub σ) (FVTy (A [ σ ]ty)))) ⟩
  DC Γ (FVTy (A [ σ ]ty) ∪ FVSub σ)
    ≡⟨ DC-∪ Γ (FVTy (A [ σ ]ty)) (FVSub σ) ⟩
  SuppTy Γ (A [ σ ]ty) ∪ SuppSub Γ σ
    ≡⟨ cong (SuppTy Γ (A [ σ ]ty) ∪_) (SuppSubFV σty) ⟩
  SuppTy Γ (A [ σ ]ty) ∪ FVSub σ ∎

SuppTmChar′ {Γ = Γ} {t = t} {A = A} tty Aty = begin
  SuppTm Γ t
    ≡⟨ SuppTmChar tty ⟩
  SuppTy Γ A ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (SuppTyFV Aty) ⟩
  FVTy A ∪ FVTm t ∎

SuppTmChar″ {Γ = Γ} {t = t} {A = A} tty Aty = begin
  SuppTm Γ t
    ≡˘⟨ DC-idem Γ (FVTm t) ⟩
  DC Γ (DC Γ (FVTm t))
    ≡⟨ cong (DC Γ) (SuppTmChar′ tty Aty) ⟩
  DC Γ (FVTy A ∪ FVTm t)
    ≡⟨ DC-∪ Γ (FVTy A) (FVTm t) ⟩
  SuppTy Γ A ∪ SuppTm Γ t ∎

vs-sub-DC : {σ : Sub n m ⋆} → (xs : VarSet n) → Typing-Sub Γ Δ σ → DC Δ (xs [ σ ]vs) ≡ DC Γ xs [ σ ]vs
vs-sub-DC emp (TyNull x) = DC-empty _
vs-sub-DC (ewf xs) (TyExt σty tty) = vs-sub-DC xs σty
vs-sub-DC {Γ = Γ , A} {Δ = Δ} (ewt xs) (TyExt {σ = σ} {t = t} σty tty) = begin
  DC Δ (xs [ σ ]vs ∪ FVTm t)
    ≡⟨ DC-∪ Δ (xs [ σ ]vs) (FVTm t) ⟩
  DC Δ (xs [ σ ]vs) ∪ DC Δ (FVTm t)
    ≡⟨ cong₂ _∪_ (vs-sub-DC xs σty) (SuppTmChar tty) ⟩
  DC Γ xs [ σ ]vs ∪ (SuppTy Δ (A [ σ ]ty) ∪ FVTm t)
    ≡˘⟨ ∪-assoc (DC Γ xs [ σ ]vs) (SuppTy Δ (A [ σ ]ty)) (FVTm t) ⟩
  DC Γ xs [ σ ]vs ∪ SuppTy Δ (A [ σ ]ty) ∪ FVTm t
    ≡˘⟨ cong (λ - → DC Γ xs [ σ ]vs ∪ DC Δ - ∪ FVTm t) (vs-sub-ty A σ) ⟩
  DC Γ xs [ σ ]vs ∪ DC Δ (FVTy A [ σ ]vs) ∪ FVTm t
    ≡⟨ cong (λ - → DC Γ xs [ σ ]vs ∪ - ∪ FVTm t) (vs-sub-DC (FVTy A) σty) ⟩
  DC Γ xs [ σ ]vs ∪ DC Γ (FVTy A) [ σ ]vs ∪ FVTm t
    ≡˘⟨ cong (_∪ FVTm t) (vs-sub-∪ (DC Γ xs) (DC Γ (FVTy A)) σ) ⟩
  (DC Γ xs ∪ DC Γ (FVTy A)) [ σ ]vs ∪ FVTm t
    ≡˘⟨ cong (λ - → - [ σ ]vs ∪ FVTm t) (DC-∪ Γ xs (FVTy A)) ⟩
  (DC Γ (xs ∪ FVTy A)) [ σ ]vs ∪ FVTm t ∎

supp-condition-preserved : (b : Bool)
                         → A ≈[ Γ ]ty B
                         → .⦃ _ : Γ ⊢pd ⦄
                         → Typing-Ty Γ A
                         → Typing-Ty Γ B
                         → supp-condition b A Γ
                         → supp-condition b B Γ
supp-condition-preserved {A = A} {Γ = Γ} {B = B} false p Aty Bty sc = begin
  SuppTy Γ B
    ≡˘⟨ EqSuppTy p ⟩
  SuppTy Γ A
    ≡⟨ sc ⟩
  full ∎
supp-condition-preserved {Γ = Γ} true (Arr≈ p q r) (TyArr {s = s} {A} {t} sty Aty tty) (TyArr {s = s′} {B} {t′} sty′ Bty tty′) (pd ,, nz ,, sc1 ,, sc2)
  = pd ,, nz ,, l1 ,, l2
  where
    l1 : SuppTm Γ s′ ≡ pd-bd-vs (pred (ctx-dim Γ)) Γ false
    l1 = begin
      SuppTm Γ s′
        ≡˘⟨ EqSuppTm p ⟩
      SuppTm Γ s
        ≡⟨ sc1 ⟩
      pd-bd-vs (pred (ctx-dim Γ)) Γ false ∎

    l2 : SuppTm Γ t′ ≡ pd-bd-vs (pred (ctx-dim Γ)) Γ true
    l2 = begin
      SuppTm Γ t′
        ≡˘⟨ EqSuppTm r ⟩
      SuppTm Γ t
        ≡⟨ sc2 ⟩
      pd-bd-vs (pred (ctx-dim Γ)) Γ true ∎
