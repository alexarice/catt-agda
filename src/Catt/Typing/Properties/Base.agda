{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base

module Catt.Typing.Properties.Base (Index : Set) (rule : Index → Rule) where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing Index rule
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Catt.Suspension
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Data.Nat

refl≈c : Γ ≈c Γ
refl≈ty : A ≈ty A
refl≈tm : t ≈tm t
refl≈s : σ ≈s σ

refl≈c {Γ = ∅} = Emp≈
refl≈c {Γ = Γ , A} = Add≈ refl≈c refl≈ty

refl≈ty {A = ⋆} = Star≈ refl≈c
refl≈ty {A = s ─⟨ A ⟩⟶ t} = Arr≈ refl≈tm refl≈ty refl≈tm

refl≈tm {t = Var i} = Var≈ refl≈c refl
refl≈tm {t = Coh Δ A σ} = Coh≈ refl≈c refl≈ty refl≈s

refl≈s {σ = ⟨⟩} = Null≈ refl≈c
refl≈s {σ = ⟨ σ , t ⟩} = Ext≈ refl≈s refl≈tm

reflexive≈c : Γ ≃c Δ → Γ ≈c Δ
reflexive≈ty : A ≃ty B → A ≈ty B
reflexive≈tm : s ≃tm t → s ≈tm t
reflexive≈s : σ ≃s τ → σ ≈s τ

reflexive≈c Emp≃ = Emp≈
reflexive≈c (Add≃ eq x) = Add≈ (reflexive≈c eq) (reflexive≈ty x)

reflexive≈ty (Star≃ x) = Star≈ (reflexive≈c x)
reflexive≈ty (Arr≃ p q r) = Arr≈ (reflexive≈tm p) (reflexive≈ty q) (reflexive≈tm r)

reflexive≈tm (Var≃ x y) = Var≈ (reflexive≈c x) y
reflexive≈tm (Coh≃ p q r) = Coh≈ (reflexive≈c p) (reflexive≈ty q) (reflexive≈s r)

reflexive≈s (Null≃ x) = Null≈ (reflexive≈c x)
reflexive≈s (Ext≃ eq x) = Ext≈ (reflexive≈s eq) (reflexive≈tm x)

sym≈c : Γ ≈c Δ → Δ ≈c Γ
sym≈ty : A ≈ty B → B ≈ty A
sym≈tm : s ≈tm t → t ≈tm s
sym≈s : σ ≈s τ → τ ≈s σ

sym≈c Emp≈ = Emp≈
sym≈c (Add≈ eq x) = Add≈ (sym≈c eq) (sym≈ty x)

sym≈ty (Star≈ x) = Star≈ (sym≈c x)
sym≈ty (Arr≈ p q r) = Arr≈ (sym≈tm p) (sym≈ty q) (sym≈tm r)

sym≈tm eq = Sym≈ eq

sym≈s (Null≈ x) = Null≈ (sym≈c x)
sym≈s (Ext≈ eq x) = Ext≈ (sym≈s eq) (sym≈tm x)

trans≈c : Γ ≈c Δ → Δ ≈c Υ → Γ ≈c Υ
trans≈ty : A ≈ty B → B ≈ty C → A ≈ty C
trans≈tm : s ≈tm t → t ≈tm u → s ≈tm u
trans≈s : σ ≈s τ → τ ≈s μ → σ ≈s μ

trans≈c Emp≈ Emp≈ = Emp≈
trans≈c (Add≈ eq x) (Add≈ eq′ y) = Add≈ (trans≈c eq eq′) (trans≈ty x y)

trans≈ty (Star≈ x) (Star≈ y) = (Star≈ (trans≈c x y))
trans≈ty (Arr≈ p q r) (Arr≈ p′ q′ r′) = Arr≈ (trans≈tm p p′) (trans≈ty q q′) (trans≈tm r r′)

trans≈tm eq eq′ = Trans≈ eq eq′

trans≈s (Null≈ x) (Null≈ y) = Null≈ (trans≈c x y)
trans≈s (Ext≈ eq x) (Ext≈ eq′ y) = Ext≈ (trans≈s eq eq′) (trans≈tm x y)

ctx-setoid-≈ : Setoid _ _
ctx-setoid-≈ = record { Carrier = CTX
                    ; _≈_ = λ x y → ctx x ≈c ctx y
                    ; isEquivalence = record { refl = refl≈c
                                             ; sym = sym≈c
                                             ; trans = trans≈c
                                             }
                    }

ty-setoid-≈ : Setoid _ _
ty-setoid-≈ = record { Carrier = TY
                    ; _≈_ = λ x y → ty x ≈ty ty y
                    ; isEquivalence = record { refl = refl≈ty
                                             ; sym = sym≈ty
                                             ; trans = trans≈ty
                                             }
                    }

tm-setoid-≈ : Setoid _ _
tm-setoid-≈ = record { Carrier = TM
                    ; _≈_ = λ x y → tm x ≈tm tm y
                    ; isEquivalence = record { refl = refl≈tm
                                             ; sym = sym≈tm
                                             ; trans = trans≈tm
                                             }
                    }

sub-setoid-≈ : Setoid _ _
sub-setoid-≈ = record { Carrier = SUB
                    ; _≈_ = λ x y → sub x ≈s sub y
                    ; isEquivalence = record { refl = refl≈s
                                             ; sym = sym≈s
                                             ; trans = trans≈s
                                             }
                    }

≈c-preserve-len : Γ ≈c Δ → ctxLength Γ ≡ ctxLength Δ
≈c-preserve-len Emp≈ = refl
≈c-preserve-len (Add≈ p x) = cong suc (≈c-preserve-len p)

≈s-to-codomain-≈c : {σ : Sub Γ Δ} → {τ : Sub Γ′ Δ′} → σ ≈s τ → Δ ≈c Δ′
≈s-to-codomain-≈c (Null≈ x) = x
≈s-to-codomain-≈c (Ext≈ p x) = ≈s-to-codomain-≈c p

-- pd-dim-lem : Δ ⊢pd₀ d → Δ ⊢pd₀ pred (ctx-dim Δ)
-- pd-dim-lem pd with cong pred (sym (pd-dim-is-ctx-dim pd))
-- ... | refl = pd

-- typing-implies-pd : Typing-Tm Γ (Coh Δ A σ) B → Δ ⊢pd₀ pred (ctx-dim Δ)
-- typing-implies-pd (TyCoh x x₁ x₂ x₃ x₄) = pd-dim-lem x
-- typing-implies-pd (TyComp x x₁ x₂ x₃ x₄ x₅) = pd-dim-lem x

record Props (i : Index) : Set where
  field
    ctx-eq : (a : rule i .Args)
           → (tct : (j : rule i .tctIndex) → Typing-Tm ((rule i .tctCtx j a)) (rule i .tct j a) (rule i .tctTy j a))
           → (eqt : (j : rule i .eqtIndex) → ((rule i .eqtlhs j a)) ≈tm (rule i .eqtrhs j a))
           → rule i .lhsCtx a ≈c rule i .rhsCtx a
    lift-rule : ∀ {d} {d′}
              → (a : rule i .Args)
              → (tct : ∀ {d} (j : rule i .tctIndex) → {A : Ty (rule i .tctCtx j a) d} → Typing-Tm ((rule i .tctCtx j a) , A) (liftTerm (rule i .tct j a)) (liftType (rule i .tctTy j a)))
              → (eqt : ∀ {d} {d′} (j : rule i .eqtIndex) → {A : Ty (rule i .eqtlhsCtx j a) d} → {B : Ty (rule i .eqtrhsCtx j a) d′} → (liftTerm {A = A} (rule i .eqtlhs j a)) ≈tm (liftTerm {A = B} (rule i .eqtrhs j a)))
              → {A : Ty (rule i .lhsCtx a) d}
              → {B : Ty (rule i .rhsCtx a) d′}
              → (liftTerm {A = A} (rule i .lhs a)) ≈tm (liftTerm {A = B} (rule i .rhs a))
    susp-rule : (a : rule i .Args)
              → (tct : (j : rule i .tctIndex) → Typing-Tm (suspCtx (rule i .tctCtx j a)) (suspTm (rule i .tct j a)) (suspTy (rule i .tctTy j a)))
              → (eqt : (j : rule i .eqtIndex) → (suspTm (rule i .eqtlhs j a)) ≈tm (suspTm (rule i .eqtrhs j a)))
              → suspTm (rule i .lhs a) ≈tm suspTm (rule i .rhs a)

open Props public
