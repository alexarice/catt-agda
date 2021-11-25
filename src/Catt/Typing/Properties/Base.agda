{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat

module Catt.Typing.Properties.Base (index : ℕ) (rule : Fin index → Rule) where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (Setoid)
open import Catt.Suspension
open import Catt.Tree
open import Catt.Globular
open import Function.Bundles
open import Catt.Support
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit
open import Catt.Variables

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

refl≈s {σ = ⟨⟩} = Null≈ refl≈ty
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
reflexive≈tm (Coh≃ p q r) with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = Coh≈ (reflexive≈ty q) (reflexive≈s r)

reflexive≈s (Null≃ x) = Null≈ (reflexive≈ty x)
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

sym≈s (Null≈ x) = Null≈ (sym≈ty x)
sym≈s (Ext≈ eq x) = Ext≈ (sym≈s eq) (sym≈tm x)

trans≈ty : A ≈[ Γ ]ty B → B ≈[ Γ ]ty C → A ≈[ Γ ]ty C
trans≈tm : s ≈[ Γ ]tm t → t ≈[ Γ ]tm u → s ≈[ Γ ]tm u
trans≈s : σ ≈[ Γ ]s τ → τ ≈[ Γ ]s μ → σ ≈[ Γ ]s μ

-- trans≈c Emp≈ Emp≈ = Emp≈
-- trans≈c (Add≈ eq x) (Add≈ eq′ y) = Add≈ (trans≈c eq eq′) (trans≈ty x y)

trans≈ty Star≈ Star≈ = Star≈
trans≈ty (Arr≈ p q r) (Arr≈ p′ q′ r′) = Arr≈ (trans≈tm p p′) (trans≈ty q q′) (trans≈tm r r′)

trans≈tm eq eq′ = Trans≈ eq eq′

trans≈s (Null≈ x) (Null≈ y) = Null≈ (trans≈ty x y)
trans≈s (Ext≈ eq x) (Ext≈ eq′ y) = Ext≈ (trans≈s eq eq′) (trans≈tm x y)
-- trans≈s Null≈ Null≈ = Null≈
-- trans≈s (Ext≈ eq x) (Ext≈ eq′ y) = Ext≈ (trans≈s eq eq′) (trans≈tm x y)

-- ctx-setoid-≈ : ℕ → Setoid _ _
-- ctx-setoid-≈ n = record { Carrier = Ctx n
--                     ; _≈_ = λ x y → x ≈c y
--                     ; isEquivalence = record { refl = refl≈c
--                                              ; sym = sym≈c
--                                              ; trans = trans≈c
--                                              }
--                     }

ty-setoid-≈ : Ctx n → Setoid _ _
ty-setoid-≈ {n} Γ = record { Carrier = Ty n
                    ; _≈_ = λ x y → x ≈[ Γ ]ty y
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
sub-setoid-≈ {m} n Δ = record { Carrier = SUB′ n m
                    ; _≈_ = λ x y → sub′ x ≈[ Δ ]s sub′ y
                    ; isEquivalence = record { refl = refl≈s
                                             ; sym = sym≈s
                                             ; trans = trans≈s
                                             }
                    }

≈ty-preserve-height : A ≈[ Γ ]ty B → ty-dim A ≡ ty-dim B
≈ty-preserve-height Star≈ = refl
≈ty-preserve-height (Arr≈ x p x₁) = cong suc (≈ty-preserve-height p)

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

-- record Props (i : Index) : Set where
--   field
--     -- ctx-eq : (a : rule i .Args)
--     --        → (tct : (j : rule i .tctIndex) → Typing-Tm ((rule i .tctCtx j a)) (rule i .tct j a) (rule i .tctTy j a))
--     --        → (eqt : (j : rule i .eqtIndex) → ((rule i .eqtlhs j a)) ≈tm (rule i .eqtrhs j a))
--     --        → rule i .lhsCtx a ≈c rule i .rhsCtx a
--     lift-rule : (a : rule i .Args)
--               → {A : Ty (rule i .len a)}
--               → {C : Ty (rule i .len a)}
--               → Typing-Tm (rule i .tgtCtx a , A) (liftTerm (rule i .lhs a)) (liftType C)
--               → (liftTerm (rule i .lhs a)) ≈[ rule i .tgtCtx a , A ]tm (liftTerm (rule i .rhs a))
--     susp-rule : (a : rule i .Args)
--               → {C : Ty (rule i .len a)}
--               → Typing-Tm (suspCtx (rule i .tgtCtx a)) (suspTm (rule i .lhs a)) (suspTy C)
--               → suspTm (rule i .lhs a) ≈[ suspCtx (rule i .tgtCtx a) ]tm suspTm (rule i .rhs a)
--     sub-rule : (a : rule i .Args)
--              → {σ : Sub (rule i .len a) n A}
--              → {Δ : Ctx n}
--              → Typing-Sub (rule i .tgtCtx a) Δ σ
--              → {C : Ty (rule i .len a)}
--              → Typing-Tm Δ (rule i .lhs a [ σ ]tm) (C [ σ ]ty)
--              → rule i .lhs a [ σ ]tm ≈[ Δ ]tm rule i .rhs a [ σ ]tm

term-conversion : Typing-Tm Γ t A → A ≈[ Γ ]ty B → Typing-Tm Γ t B
term-conversion (TyVarZ x y) eq = TyVarZ x (trans≈ty y eq)
term-conversion (TyVarS i tvi x) eq = TyVarS i tvi (trans≈ty x eq)
term-conversion (TyCoh Aty σty b sc p) eq = TyCoh Aty σty b sc (trans≈ty p eq)

src-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → s ≈[ Γ ]tm s′
src-eq (Arr≈ p q r) = p

tgt-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → t ≈[ Γ ]tm t′
tgt-eq (Arr≈ p q r) = r

base-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → A ≈[ Γ ]ty A′
base-eq (Arr≈ p q r) = q

transport-typing : Typing-Tm Γ t A → t ≃tm s → Typing-Tm Γ s A
transport-typing tty p with ≃tm-to-≡ p
... | refl = tty

transport-typing-ctx : Typing-Ctx Γ → Γ ≃c Δ → Typing-Ctx Δ
transport-typing-ctx Γty p with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = Γty

transport-typing-ty : Typing-Ty Γ A → Γ ≃c Δ → A ≃ty B → Typing-Ty Δ B
transport-typing-ty Γty p q with ≃c-preserve-length p
... | refl with ≃c-to-≡ p | ≃ty-to-≡ q
... | refl | refl = Γty

coh-sub-ty : Typing-Tm Γ (Coh T A τ) B → Typing-Sub (tree-to-ctx T) Γ τ
coh-sub-ty (TyCoh x τty b x₂ x₃) = τty

coh-ty-ty : Typing-Tm Γ (Coh T A τ) B → Typing-Ty (tree-to-ctx T) A
coh-ty-ty (TyCoh Aty τty b a c) = Aty

sub-to-ctx-Ty : Typing-Sub Γ Δ σ → Typing-Ctx Γ
sub-to-ctx-Ty (TyNull x) = TyEmp
sub-to-ctx-Ty (TyExt σty Aty tty) = TyAdd (sub-to-ctx-Ty σty) Aty

var-Ty : Typing-Ctx Γ → (i : Fin n) → Typing-Tm Γ (Var i) (Γ ‼ i)
var-Ty (TyAdd Γty Aty) zero = TyVarZ Aty refl≈ty
var-Ty (TyAdd Γty Aty) (suc i) = TyVarS i (var-Ty Γty i) refl≈ty

isVar-Ty : Typing-Ctx Γ → (t : Tm n) → .⦃ _ : isVar t ⦄ → Typing-Tm Γ t (Γ ‼ getVarFin t)
isVar-Ty Γty (Var i) = var-Ty Γty i

module _ {i : Index} (a : rule i .Rule.Args) where
  open Rule (rule i)

  BoundRule : Set
  BoundRule = ∀ {d}
            → (BoundedTm d (tgtCtx a) (lhs a)) ⇔ (BoundedTm d (tgtCtx a) (rhs a))

  LiftRule : Set
  LiftRule = {A : Ty (len a)}
           → {C : Ty (len a)}
           → Typing-Tm (tgtCtx a , A) (liftTerm (lhs a)) (liftType C)
           → (liftTerm (lhs a)) ≈[ tgtCtx a , A ]tm (liftTerm (rhs a))

  SuspRule : Set
  SuspRule = {C : Ty (len a)}
           → Typing-Tm (suspCtx (tgtCtx a)) (suspTm (lhs a)) (suspTy C)
           → suspTm (lhs a) ≈[ suspCtx (tgtCtx a) ]tm suspTm (rhs a)

  SubRule : Set
  SubRule = ∀ {n}
          → {σ : Sub (len a) n ⋆}
          → {Δ : Ctx n}
          → {C : Ty (len a)}
          → Typing-Sub (tgtCtx a) Δ σ
          → Typing-Tm Δ (lhs a [ σ ]tm) (C [ σ ]ty)
          → lhs a [ σ ]tm ≈[ Δ ]tm rhs a [ σ ]tm

  SupportRule : Set
  SupportRule = {A : Ty (len a)}
              → (tty : Typing-Tm (tgtCtx a) (lhs a) A)
              → SuppTm (tgtCtx a) (lhs a) ≡ SuppTm (tgtCtx a) (rhs a)

  ConvRule : Set
  ConvRule = {A : Ty (len a)}
           → Typing-Tm (tgtCtx a) (lhs a) A
           → Typing-Tm (tgtCtx a) (rhs a) A
