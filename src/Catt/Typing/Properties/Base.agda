open import Catt.Prelude
open import Catt.Typing.Base

module Catt.Typing.Properties.Base {index : Set} (rule : index → Rule) where

open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing rule
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Globular
open import Catt.Support
open import Catt.Variables

refl≈ty : A ≈[ Γ ]ty A
refl≈tm : t ≈[ Γ ]tm t
refl≈s : σ ≈[ Γ ]s σ

refl≈ty {A = ⋆} = Star≈
refl≈ty {A = s ─⟨ A ⟩⟶ t} = Arr≈ refl≈tm refl≈ty refl≈tm

refl≈tm {t = Var i} = Var≈ refl
refl≈tm {t = Coh Δ A σ} = Coh≈ refl≈ty refl≈s

refl≈s {σ = ⟨⟩} = Null≈ refl≈ty
refl≈s {σ = ⟨ σ , t ⟩} = Ext≈ refl≈s refl≈tm

reflexive≈ty : A ≃ty B → A ≈[ Γ ]ty B
reflexive≈tm : s ≃tm t → s ≈[ Γ ]tm t
reflexive≈s : σ ≃s τ → σ ≈[ Γ ]s τ

reflexive≈ty (Star≃ x) = Star≈
reflexive≈ty (Arr≃ p q r) = Arr≈ (reflexive≈tm p) (reflexive≈ty q) (reflexive≈tm r)

reflexive≈tm (Var≃ x y) = Var≈ y
reflexive≈tm (Coh≃ p q r) with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = Coh≈ (reflexive≈ty q) (reflexive≈s r)

reflexive≈s (Null≃ x) = Null≈ (reflexive≈ty x)
reflexive≈s (Ext≃ eq x) = Ext≈ (reflexive≈s eq) (reflexive≈tm x)

sym≈ty : A ≈[ Γ ]ty B → B ≈[ Γ ]ty A
sym≈tm : s ≈[ Γ ]tm t → t ≈[ Γ ]tm s
sym≈s : σ ≈[ Γ ]s τ → τ ≈[ Γ ]s σ

sym≈ty Star≈ = Star≈
sym≈ty (Arr≈ p q r) = Arr≈ (sym≈tm p) (sym≈ty q) (sym≈tm r)

sym≈tm eq = Sym≈ eq

sym≈s (Null≈ x) = Null≈ (sym≈ty x)
sym≈s (Ext≈ eq x) = Ext≈ (sym≈s eq) (sym≈tm x)

trans≈ty : A ≈[ Γ ]ty B → B ≈[ Γ ]ty C → A ≈[ Γ ]ty C
trans≈tm : s ≈[ Γ ]tm t → t ≈[ Γ ]tm u → s ≈[ Γ ]tm u
trans≈s : σ ≈[ Γ ]s τ → τ ≈[ Γ ]s μ → σ ≈[ Γ ]s μ

trans≈ty Star≈ Star≈ = Star≈
trans≈ty (Arr≈ p q r) (Arr≈ p′ q′ r′) = Arr≈ (trans≈tm p p′) (trans≈ty q q′) (trans≈tm r r′)

trans≈tm eq eq′ = Trans≈ eq eq′

trans≈s (Null≈ x) (Null≈ y) = Null≈ (trans≈ty x y)
trans≈s (Ext≈ eq x) (Ext≈ eq′ y) = Ext≈ (trans≈s eq eq′) (trans≈tm x y)

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

sub-setoid-≈ : Ctx m → Setoid _ _
sub-setoid-≈ {m} Δ = record { Carrier = SUB′ m
                    ; _≈_ = λ x y → sub′ x ≈[ Δ ]s sub′ y
                    ; isEquivalence = record { refl = refl≈s
                                             ; sym = sym≈s
                                             ; trans = trans≈s
                                             }
                    }

≈ty-preserve-height : A ≈[ Γ ]ty B → ty-dim A ≡ ty-dim B
≈ty-preserve-height Star≈ = refl
≈ty-preserve-height (Arr≈ x p x₁) = cong suc (≈ty-preserve-height p)

src-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → s ≈[ Γ ]tm s′
src-eq (Arr≈ p q r) = p

tgt-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → t ≈[ Γ ]tm t′
tgt-eq (Arr≈ p q r) = r

base-eq : (s ─⟨ A ⟩⟶ t) ≈[ Γ ]ty (s′ ─⟨ A′ ⟩⟶ t′) → A ≈[ Γ ]ty A′
base-eq (Arr≈ p q r) = q

transport-typing : Typing-Tm Γ t A → t ≃tm s → Typing-Tm Γ s A
transport-typing tty p with ≃tm-to-≡ p
... | refl = tty

transport-typing-full : Typing-Tm Γ t A → t ≃tm s → A ≃ty B → Typing-Tm Γ s B
transport-typing-full tty p q with ≃tm-to-≡ p | ≃ty-to-≡ q
... | refl | refl = tty

transport-typing-ctx : Typing-Ctx Γ → Γ ≃c Δ → Typing-Ctx Δ
transport-typing-ctx Γty p with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = Γty

transport-typing-ty : Typing-Ty Γ A → Γ ≃c Δ → A ≃ty B → Typing-Ty Δ B
transport-typing-ty Γty p q with ≃c-preserve-length p
... | refl with ≃c-to-≡ p | ≃ty-to-≡ q
... | refl | refl = Γty

transport-typing-sub : Typing-Sub Γ Δ σ → Γ ≃c Γ′ → Δ ≃c Δ′ → σ ≃s τ → Typing-Sub Γ′ Δ′ τ
transport-typing-sub σty p q r with ≃c-preserve-length p | ≃c-preserve-length q
... | refl | refl with ≃c-to-≡ p | ≃c-to-≡ q | ≃ty-to-≡ (≃s-to-same-ty r)
... | refl | refl | refl with ≃s-to-≡ r
... | refl = σty

coh-sub-ty : Typing-Tm Γ (Coh Δ A τ) B → Typing-Sub Δ Γ τ
coh-sub-ty (TyConv tty p) = coh-sub-ty tty
coh-sub-ty (TyCoh x τty b x₂) = τty

coh-ty-ty : Typing-Tm Γ (Coh Δ A τ) B → Typing-Ty Δ A
coh-ty-ty (TyConv tty p) = coh-ty-ty tty
coh-ty-ty (TyCoh Aty τty b a) = Aty

isVar-Ty : (t : Tm n) → .⦃ _ : isVar t ⦄ → Typing-Tm Γ t (Γ ‼ getVarFin t)
isVar-Ty (Var i) = TyVar i

fromℕ-Ty : (Γ : Ctx (suc n)) → Typing-Tm Γ (Var (fromℕ _)) ⋆
fromℕ-Ty Γ = TyConv (TyVar (fromℕ _)) (reflexive≈ty (fromℕ-‼ Γ))

replaceSub-Ty : {Γ : Ctx (suc n)} → Typing-Sub Γ Δ σ → Typing-Tm Δ t (Γ ‼ zero [ σ ]ty) → Typing-Sub Γ Δ (replaceSub σ t)
replaceSub-Ty (TyExt {σ = σ} {A = A} σty sty) tty = TyExt σty (TyConv tty (reflexive≈ty (lift-sub-comp-lem-ty σ A)))

ty-dim-≈ : A ≈[ Γ ]ty B → ty-dim A ≡ ty-dim B
ty-dim-≈ Star≈ = refl
ty-dim-≈ (Arr≈ _ p _) = cong suc (ty-dim-≈ p)

unrestrictEq : σ ≈[ Δ ]s τ → unrestrict σ ≈[ Δ ]s unrestrict τ
unrestrictEq (Null≈ (Arr≈ p q r)) = Ext≈ (Ext≈ (Null≈ q) p) r
unrestrictEq (Ext≈ eq x) = Ext≈ (unrestrictEq eq) x

module _ (r : Rule) where
  open Rule r

  LiftRule : Set
  LiftRule = {A : Ty len}
           → {C : Ty len}
           → Typing-Tm (tgtCtx , A) (liftTerm lhs) (liftType C)
           → (liftTerm lhs) ≈[ tgtCtx , A ]tm (liftTerm rhs)

  SuspRule : Set
  SuspRule = {C : Ty len}
           → Typing-Tm (suspCtx tgtCtx) (suspTm lhs) (suspTy C)
           → suspTm lhs ≈[ suspCtx tgtCtx ]tm suspTm rhs

  SubRule : Set
  SubRule = ∀ {n}
          → {σ : Sub len n ⋆}
          → {Δ : Ctx n}
          → {C : Ty len}
          → Typing-Sub tgtCtx Δ σ
          → Typing-Tm Δ (lhs [ σ ]tm) (C [ σ ]ty)
          → lhs [ σ ]tm ≈[ Δ ]tm rhs [ σ ]tm

  SupportRule : Set
  SupportRule = {A : Ty len}
              → (tty : Typing-Tm tgtCtx lhs A)
              → SuppTm tgtCtx lhs ≡ SuppTm tgtCtx rhs

  ConvRule : Set
  ConvRule = {A : Ty len}
           → Typing-Tm tgtCtx lhs A
           → Typing-Tm tgtCtx rhs A
