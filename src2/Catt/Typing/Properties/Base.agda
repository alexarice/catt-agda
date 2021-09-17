{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
open import Data.Fin using (Fin)
open import Data.Nat

module Catt.Typing.Properties.Base (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Catt.Suspension
open import Catt.Pasting
open import Catt.Pasting.Properties

private
  Index : Set
  Index = Fin index

-- refl≈c : Γ ≈c Γ
refl≈ty : A ≈[ Γ ]ty A
refl≈tm : t ≈[ Γ ]tm t
refl≈s : σ ≈[ Γ ]s σ

-- refl≈c {Γ = ∅} = Emp≈
-- refl≈c {Γ = Γ , A} = Add≈ refl≈c refl≈ty

refl≈ty {A = ⋆} = Star≈
refl≈ty {A = s ─⟨ A ⟩⟶ t} = Arr≈ refl≈tm refl≈ty refl≈tm

refl≈tm {t = Var i} = Var≈ refl
refl≈tm {t = Coh Δ A σ} = Coh≈ refl≈ty refl≈s

refl≈s {σ = ⟨⟩} = Null≈
refl≈s {σ = ⟨ σ , t ⟩} = Ext≈ refl≈s refl≈tm

-- reflexive≈c : Γ ≃c Δ → Γ ≈c Δ
reflexive≈ty : A ≃ty B → A ≈[ Γ ]ty B
reflexive≈tm : s ≃tm t → s ≈[ Γ ]tm t
reflexive≈s : σ ≃s τ → σ ≈[ Γ ]s τ

-- reflexive≈c Emp≃ = Emp≈
-- reflexive≈c (Add≃ eq x) = Add≈ (reflexive≈c eq) (reflexive≈ty x)

reflexive≈ty (Star≃ x) = Star≈
reflexive≈ty (Arr≃ p q r) = Arr≈ (reflexive≈tm p) (reflexive≈ty q) (reflexive≈tm r)

reflexive≈tm (Var≃ x y) = Var≈ y
reflexive≈tm (Coh≃ p q r) with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = Coh≈ (reflexive≈ty q) (reflexive≈s r)

reflexive≈s (Null≃ x) = Null≈
reflexive≈s (Ext≃ eq x) = Ext≈ (reflexive≈s eq) (reflexive≈tm x)

-- sym≈c : Γ ≈c Δ → Δ ≈c Γ
sym≈ty : A ≈[ Γ ]ty B → B ≈[ Γ ]ty A
sym≈tm : s ≈[ Γ ]tm t → t ≈[ Γ ]tm s
sym≈s : σ ≈[ Γ ]s τ → τ ≈[ Γ ]s σ

-- sym≈c Emp≈ = Emp≈
-- sym≈c (Add≈ eq x) = Add≈ (sym≈c eq) (sym≈ty x)

sym≈ty Star≈ = Star≈
sym≈ty (Arr≈ p q r) = Arr≈ (sym≈tm p) (sym≈ty q) (sym≈tm r)

sym≈tm eq = Sym≈ eq

sym≈s Null≈ = Null≈
sym≈s (Ext≈ eq x) = Ext≈ (sym≈s eq) (sym≈tm x)

-- trans≈c : Γ ≈c Δ → Δ ≈c Υ → Γ ≈c Υ
trans≈ty : A ≈[ Γ ]ty B → B ≈[ Γ ]ty C → A ≈[ Γ ]ty C
trans≈tm : s ≈[ Γ ]tm t → t ≈[ Γ ]tm u → s ≈[ Γ ]tm u
trans≈s : σ ≈[ Γ ]s τ → τ ≈[ Γ ]s μ → σ ≈[ Γ ]s μ

-- trans≈c Emp≈ Emp≈ = Emp≈
-- trans≈c (Add≈ eq x) (Add≈ eq′ y) = Add≈ (trans≈c eq eq′) (trans≈ty x y)

trans≈ty Star≈ Star≈ = Star≈
trans≈ty (Arr≈ p q r) (Arr≈ p′ q′ r′) = Arr≈ (trans≈tm p p′) (trans≈ty q q′) (trans≈tm r r′)

trans≈tm eq eq′ = Trans≈ eq eq′

trans≈s Null≈ Null≈ = Null≈
trans≈s (Ext≈ eq x) (Ext≈ eq′ y) = Ext≈ (trans≈s eq eq′) (trans≈tm x y)

-- ctx-setoid-≈ : ℕ → Setoid _ _
-- ctx-setoid-≈ n = record { Carrier = Ctx n
--                     ; _≈_ = λ x y → x ≈c y
--                     ; isEquivalence = record { refl = refl≈c
--                                              ; sym = sym≈c
--                                              ; trans = trans≈c
--                                              }
--                     }

ty-setoid-≈ : Ctx n → Setoid _ _
ty-setoid-≈ {n} Γ = record { Carrier = TY′ n
                    ; _≈_ = λ x y → ty′ x ≈[ Γ ]ty ty′ y
                    ; isEquivalence = record { refl = refl≈ty
                                             ; sym = sym≈ty
                                             ; trans = trans≈ty
                                             }
                    }

tm-setoid-≈ : Ctx n → Setoid _ _
tm-setoid-≈ {n} Γ = record { Carrier = Tm n
                    ; _≈_ = λ x y → x ≈[ Γ ]tm y
                    ; isEquivalence = record { refl = refl≈tm
                                             ; sym = sym≈tm
                                             ; trans = trans≈tm
                                             }
                    }

sub-setoid-≈ : ℕ → Ctx m → Setoid _ _
sub-setoid-≈ {m} n Δ = record { Carrier = Sub n m
                    ; _≈_ = λ x y → x ≈[ Δ ]s y
                    ; isEquivalence = record { refl = refl≈s
                                             ; sym = sym≈s
                                             ; trans = trans≈s
                                             }
                    }

-- ≈c-preserve-len : Γ ≈c Δ → ctxLength Γ ≡ ctxLength Δ
-- ≈c-preserve-len Emp≈ = refl
-- ≈c-preserve-len (Add≈ p x) = cong suc (≈c-preserve-len p)

-- ≈s-to-codomain-≡ : {σ : Sub n m} → {τ : Sub n′ m′} → σ ≈s τ → m ≡ m′
-- ≈s-to-codomain-≡ (Null≈ x) = x
-- ≈s-to-codomain-≡ (Ext≈ p x) = ≈s-to-codomain-≡ p

-- pd-dim-lem : Δ ⊢pd₀ d → Δ ⊢pd₀ pred (ctx-dim Δ)
-- pd-dim-lem pd with cong pred (sym (pd-dim-is-ctx-dim pd))
-- ... | refl = pd

-- typing-implies-pd : Typing-Tm Γ (Coh Δ A σ) B → Δ ⊢pd₀ pred (ctx-dim Δ)
-- typing-implies-pd (TyCoh x x₁ x₂ x₃ x₄) = pd-dim-lem x
-- typing-implies-pd (TyComp x x₁ x₂ x₃ x₄ x₅) = pd-dim-lem x

record Props (i : Index) : Set where
  field
    -- ctx-eq : (a : rule i .Args)
    --        → (tct : (j : rule i .tctIndex) → Typing-Tm ((rule i .tctCtx j a)) (rule i .tct j a) (rule i .tctTy j a))
    --        → (eqt : (j : rule i .eqtIndex) → ((rule i .eqtlhs j a)) ≈tm (rule i .eqtrhs j a))
    --        → rule i .lhsCtx a ≈c rule i .rhsCtx a
    lift-rule : (a : rule i .Args)
              → (eqt : ∀ {d} (j : eqtIndex (rule i)) → {A : Ty (rule i .eqtLen j a) d} → (liftTerm (rule i .eqtlhs j a)) ≈[ rule i .eqtCtx j a , A ]tm (liftTerm (rule i .eqtrhs j a)))
              → {A : Ty (rule i .len a) d}
              → {C : Ty (rule i .len a) d′}
              → Typing-Tm (rule i .tgtCtx a , A) (liftTerm (rule i .lhs a)) (liftType C)
              → (liftTerm (rule i .lhs a)) ≈[ rule i .tgtCtx a , A ]tm (liftTerm (rule i .rhs a))
    susp-rule : (a : rule i .Args)
              → (eqt : (j : eqtIndex (rule i)) → (suspTm (rule i .eqtlhs j a)) ≈[ suspCtx (rule i .eqtCtx j a) ]tm (suspTm (rule i .eqtrhs j a)))
              → {C : Ty (rule i .len a) d}
              → Typing-Tm (suspCtx (rule i .tgtCtx a)) (suspTm (rule i .lhs a)) (suspTy C)
              → suspTm (rule i .lhs a) ≈[ suspCtx (rule i .tgtCtx a) ]tm suspTm (rule i .rhs a)
    sub-rule : (a : rule i .Args)
             → (eqt : ∀ {n} (j : eqtIndex (rule i)) → {σ : Sub (rule i .eqtLen j a) n} → {Δ : Ctx n} → Typing-Sub (rule i .eqtCtx j a) Δ σ → rule i .eqtlhs j a [ σ ]tm ≈[ Δ ]tm rule i .eqtrhs j a [ σ ]tm)
             → {σ : Sub (rule i .len a) n}
             → {Δ : Ctx n}
             → Typing-Sub (rule i .tgtCtx a) Δ σ
             → {C : Ty (rule i .len a) d}
             → Typing-Tm Δ (rule i .lhs a [ σ ]tm) (C [ σ ]ty)
             → rule i .lhs a [ σ ]tm ≈[ Δ ]tm rule i .rhs a [ σ ]tm

open Props public
