module Catt.Support.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Suspension.Pasting
open import Catt.Wedge
open import Catt.Wedge.Pasting
open import Catt.Tree
open import Catt.Tree.Pasting

open import Catt.Support

open import Algebra.Bundles
open import Algebra.Definitions
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using (Pointwise)
open import Relation.Binary
open import Relation.Nullary
open import Tactic.MonoidSolver

FVTm-≃ : s ≃tm t → FVTm s ≡ FVTm t
FVTy-≃ : A ≃ty B → FVTy A ≡ FVTy B
FVSub-≃ : σ ≃s τ → FVSub σ ≡ FVSub τ

FVTm-≃ (Var≃ x y) with toℕ-injective y
... | refl = refl
FVTm-≃ (Coh≃ x y z) = FVSub-≃ z

FVTy-≃ (Star≃ x) = refl
FVTy-≃ (Arr≃ p q r) = cong₂ _∪_ (cong₂ _∪_ (FVTy-≃ q) (FVTm-≃ p)) (FVTm-≃ r)

FVSub-≃ (Null≃ x) = FVTy-≃ x
FVSub-≃ (Ext≃ p x) = cong₂ _∪_ (FVSub-≃ p) (FVTm-≃ x)

∪-assoc : Associative _≡_ (_∪_ {n})
∪-assoc emp emp emp = refl
∪-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (∨-assoc x y z) (∪-assoc xs ys zs)

∪-left-unit : LeftIdentity _≡_ empty (_∪_ {n})
∪-left-unit emp = refl
∪-left-unit (x ∷ xs) = cong₂ _∷_ refl (∪-left-unit xs)

∪-right-unit : RightIdentity _≡_ empty (_∪_ {n})
∪-right-unit emp = refl
∪-right-unit (x ∷ xs) = cong₂ _∷_ (∨-identityʳ x) (∪-right-unit xs)

∪-comm : Commutative _≡_ (_∪_ {n})
∪-comm emp emp = refl
∪-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (∨-comm x y) (∪-comm xs ys)

∪-idem : Idempotent _≡_ (_∪_ {n})
∪-idem emp = refl
∪-idem (x ∷ xs) = cong₂ _∷_ (∨-idem x) (∪-idem xs)

∪-left-zero : (xs : VarSet n) → full ∪ xs ≡ full
∪-left-zero emp = refl
∪-left-zero (x ∷ xs) = cong ewt (∪-left-zero xs)

∪-right-zero : (xs : VarSet n) → xs ∪ full ≡ full
∪-right-zero emp = refl
∪-right-zero (x ∷ xs) = cong₂ _∷_ (∨-zeroʳ x) (∪-right-zero xs)

FVTm-on-var : (t : Tm n) → .⦃ _ : isVar t ⦄ → FVTm t ≡ trueAt (getVarFin t)
FVTm-on-var (Var i) = refl

module _ {n : ℕ} where

  open import Algebra.Definitions {A = VarSet n} _≡_
  open import Algebra.Structures {A = VarSet n} _≡_

  ∪-isMagma : IsMagma (_∪_)
  ∪-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong = cong₂ _∪_
    }

  ∪-isSemigroup : IsSemigroup _∪_
  ∪-isSemigroup = record
    { isMagma = ∪-isMagma
    ; assoc = ∪-assoc
    }

  ∪-isMonoid : IsMonoid _∪_ empty
  ∪-isMonoid = record
    { isSemigroup = ∪-isSemigroup
    ; identity = ∪-left-unit ,, ∪-right-unit
    }

  ∪-isCommutativeMonoid : IsCommutativeMonoid _∪_ empty
  ∪-isCommutativeMonoid = record
    { isMonoid = ∪-isMonoid
    ; comm = ∪-comm
    }

  ∪-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _∪_ empty
  ∪-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ∪-isCommutativeMonoid
    ; idem = ∪-idem
    }

  ∪-monoid : Monoid _ _
  ∪-monoid = record
    { isMonoid = ∪-isMonoid }

  ∪-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  ∪-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = ∪-isIdempotentCommutativeMonoid
    }

vs-sub-empty : (σ : Sub n m ⋆) → empty [ σ ]vs ≡ empty
vs-sub-empty ⟨ _ ⟩′ = refl
vs-sub-empty ⟨ σ , t ⟩ = vs-sub-empty σ

vs-sub-full : (σ : Sub n m ⋆) → full [ σ ]vs ≡ FVSub σ
vs-sub-full ⟨ _ ⟩′ = refl
vs-sub-full ⟨ σ , t ⟩ = cong (_∪ FVTm t) (vs-sub-full σ)

vs-sub-∪ : (xs ys : VarSet n) → (σ : Sub n m ⋆) → (xs ∪ ys) [ σ ]vs ≡ xs [ σ ]vs ∪ ys [ σ ]vs
vs-sub-∪ xs ys ⟨ _ ⟩′ = sym (∪-left-unit empty)
vs-sub-∪ (ewf xs) (ewf ys) ⟨ σ , t ⟩ = vs-sub-∪ xs ys σ
vs-sub-∪ (ewf xs) (ewt ys) ⟨ σ , t ⟩ = trans (cong (_∪ FVTm t) (vs-sub-∪ xs ys σ))
                                             (∪-assoc (xs [ σ ]vs) (ys [ σ ]vs) (FVTm t))
vs-sub-∪ (ewt xs) (ewf ys) ⟨ σ , t ⟩ = begin
  (xs ∪ ys) [ σ ]vs ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (vs-sub-∪ xs ys σ) ⟩
  xs [ σ ]vs ∪ ys [ σ ]vs ∪ FVTm t
    ≡⟨ ∪-assoc (xs [ σ ]vs) (ys [ σ ]vs) (FVTm t) ⟩
  xs [ σ ]vs ∪ (ys [ σ ]vs ∪ FVTm t)
    ≡⟨ cong (xs [ σ ]vs ∪_) (∪-comm (ys [ σ ]vs) (FVTm t)) ⟩
  xs [ σ ]vs ∪ (FVTm t ∪ ys [ σ ]vs)
    ≡˘⟨ ∪-assoc (xs [ σ ]vs) (FVTm t) (ys [ σ ]vs) ⟩
  xs [ σ ]vs ∪ FVTm t ∪ ys [ σ ]vs ∎
  where
    open ≡-Reasoning
vs-sub-∪ {n} {m} (ewt xs) (ewt ys) ⟨ σ , t ⟩ = begin
  (xs ∪ ys) [ σ ]vs ∪ FVTm t
    ≡⟨ cong (_∪ FVTm t) (vs-sub-∪ xs ys σ) ⟩
  xs [ σ ]vs ∪ ys [ σ ]vs ∪ FVTm t
    ≡⟨ ∪-assoc (xs [ σ ]vs) (ys [ σ ]vs) (FVTm t) ⟩
  xs [ σ ]vs ∪ (ys [ σ ]vs ∪ FVTm t)
    ≡˘⟨ cong (λ - → xs [ σ ]vs ∪ (ys [ σ ]vs ∪ -)) (∪-idem (FVTm t)) ⟩
  xs [ σ ]vs ∪ (ys [ σ ]vs ∪ (FVTm t ∪ FVTm t))
    ≡˘⟨ cong (xs [ σ ]vs ∪_) (∪-assoc (ys [ σ ]vs) (FVTm t) (FVTm t)) ⟩
  xs [ σ ]vs ∪ (ys [ σ ]vs ∪ FVTm t ∪ FVTm t)
    ≡⟨ cong (λ - → xs [ σ ]vs ∪ (- ∪ FVTm t)) (∪-comm (ys [ σ ]vs) (FVTm t)) ⟩
  xs [ σ ]vs ∪ (FVTm t ∪ ys [ σ ]vs ∪ FVTm t)
    ≡⟨ solve (∪-monoid {m}) ⟩
  xs [ σ ]vs ∪ FVTm t ∪ (ys [ σ ]vs ∪ FVTm t) ∎
  where
    open ≡-Reasoning

vs-sub-ty : (A : Ty n) → (σ : Sub n m ⋆) → (FVTy A) [ σ ]vs ≡ FVTy (A [ σ ]ty)
vs-sub-tm : (t : Tm n) → (σ : Sub n m ⋆) → (FVTm t) [ σ ]vs ≡ FVTm (t [ σ ]tm)
vs-sub-sub : (τ : Sub l n A) → (σ : Sub n m ⋆) → (FVSub τ) [ σ ]vs ≡ FVSub (τ ● σ)

vs-sub-ty ⋆ σ = vs-sub-empty σ
vs-sub-ty (s ─⟨ A ⟩⟶ t) σ = begin
  (FVTy (s ─⟨ A ⟩⟶ t)) [ σ ]vs
    ≡⟨ vs-sub-∪ (FVTy A ∪ FVTm s) (FVTm t) σ ⟩
  (FVTy A ∪ FVTm s) [ σ ]vs ∪ (FVTm t) [ σ ]vs
    ≡⟨ cong (_∪ (FVTm t) [ σ ]vs) (vs-sub-∪ (FVTy A) (FVTm s) σ) ⟩
  (FVTy A) [ σ ]vs ∪ (FVTm s) [ σ ]vs ∪ (FVTm t) [ σ ]vs
    ≡⟨ cong₂ _∪_ (cong₂ _∪_ (vs-sub-ty A σ) (vs-sub-tm s σ)) (vs-sub-tm t σ) ⟩
  FVTy ((s ─⟨ A ⟩⟶ t) [ σ ]ty) ∎
  where
    open ≡-Reasoning

vs-sub-tm (Var zero) ⟨ σ , t ⟩ = trans (cong (_∪ FVTm t) (vs-sub-empty σ)) (∪-left-unit (FVTm t))
vs-sub-tm (Var (suc i)) ⟨ σ , t ⟩ = vs-sub-tm (Var i) σ
vs-sub-tm (Coh S A τ) σ = vs-sub-sub τ σ

vs-sub-sub ⟨ A ⟩′ σ = vs-sub-ty A σ
vs-sub-sub ⟨ τ , t ⟩ σ = trans (vs-sub-∪ (FVSub τ) (FVTm t) σ) (cong₂ _∪_ (vs-sub-sub τ σ) (vs-sub-tm t σ))

fv-wk-ty : (A : Ty n) → FVTy (wk-ty A) ≡ ewf (FVTy A)
fv-wk-tm : (t : Tm n) → FVTm (wk-tm t) ≡ ewf (FVTm t)
fv-wk-sub : (σ : Sub n m ⋆) → FVSub (wk-sub σ) ≡ ewf (FVSub σ)

fv-wk-ty ⋆ = refl
fv-wk-ty (s ─⟨ A ⟩⟶ t) = cong₂ _∪_ (cong₂ _∪_ (fv-wk-ty A) (fv-wk-tm s)) (fv-wk-tm t)

fv-wk-tm (Var i) = refl
fv-wk-tm (Coh S A σ) = fv-wk-sub σ

fv-wk-sub ⟨ _ ⟩′ = refl
fv-wk-sub ⟨ σ , t ⟩ = cong₂ _∪_ (fv-wk-sub σ) (fv-wk-tm t)

idSub-fv : FVSub (idSub {n}) ≡ full
idSub-fv {zero} = refl
idSub-fv {suc n} = trans (cong (_∪ ewt empty) (fv-wk-sub idSub)) (cong ewt (trans (∪-right-unit (FVSub idSub)) idSub-fv))

idSub≃-fv : (p : Γ ≃c Δ) → FVSub (idSub≃ p) ≡ full
idSub≃-fv Emp≃ = refl
idSub≃-fv (Add≃ p x) = trans (cong (_∪ ewt empty) (fv-wk-sub (idSub≃ p))) (cong ewt (trans (∪-right-unit (FVSub (idSub≃ p))) (idSub≃-fv p)))

vs-sub-wk : (xs : VarSet n) → (σ : Sub n m ⋆) → xs [ wk-sub σ ]vs ≡ ewf (xs [ σ ]vs)
vs-sub-wk emp ⟨ _ ⟩′ = refl
vs-sub-wk (ewf xs) ⟨ σ , t ⟩ = vs-sub-wk xs σ
vs-sub-wk (ewt xs) ⟨ σ , t ⟩ = cong₂ _∪_ (vs-sub-wk xs σ) (fv-wk-tm t)

vs-sub-id-lem : (b : Bool) → (xs : VarSet n) → (σ : Sub n m ⋆)
                       → (b ∷ xs) [ ⟨ wk-sub σ , 0V ⟩ ]vs ≡ b ∷ xs [ σ ]vs
vs-sub-id-lem false xs σ = vs-sub-wk xs σ
vs-sub-id-lem true xs σ = begin
  xs [ wk-sub σ ]vs ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) (vs-sub-wk xs σ) ⟩
  ewt (xs [ σ ]vs ∪ empty)
    ≡⟨ cong ewt (∪-right-unit (xs [ σ ]vs)) ⟩
  ewt (xs [ σ ]vs) ∎
  where
    open ≡-Reasoning

vs-sub-id : (xs : VarSet n) → xs [ idSub ]vs ≡ xs
vs-sub-id emp = refl
vs-sub-id (b ∷ xs) = begin
  (b ∷ xs) [ idSub ]vs
    ≡⟨ vs-sub-id-lem b xs idSub ⟩
  b ∷ xs [ idSub ]vs
    ≡⟨ cong (b ∷_) (vs-sub-id xs) ⟩
  b ∷ xs ∎
  where
    open ≡-Reasoning

⊆-refl : {xs : VarSet n} → xs ⊆ xs
⊆-refl = sym (∪-idem _)

⊆-reflexive : {xs ys : VarSet n} → xs ≡ ys → xs ⊆ ys
⊆-reflexive refl = ⊆-refl

⊆-trans : {xs ys zs : VarSet n} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans {xs = xs} {ys} {zs} p q = begin
  zs
    ≡⟨ q ⟩
  zs ∪ ys
    ≡⟨ cong (zs ∪_) p ⟩
  zs ∪ (ys ∪ xs)
    ≡˘⟨ ∪-assoc zs ys xs ⟩
  zs ∪ ys ∪ xs
    ≡˘⟨ cong (_∪ xs) q ⟩
  zs ∪ xs ∎
  where
    open ≡-Reasoning

⊆-antisym : {xs ys : VarSet n} → xs ⊆ ys → ys ⊆ xs → xs ≡ ys
⊆-antisym {xs = xs} {ys} p q = begin
  xs
    ≡⟨ q ⟩
  xs ∪ ys
    ≡⟨ ∪-comm xs ys ⟩
  ys ∪ xs
    ≡˘⟨ p ⟩
  ys ∎
  where
    open ≡-Reasoning

⊆-preorder : (n : ℕ) → IsPreorder _≡_ (_⊆_ {n})
IsPreorder.isEquivalence (⊆-preorder n) = isEquivalence
IsPreorder.reflexive (⊆-preorder n) = ⊆-reflexive
IsPreorder.trans (⊆-preorder n) = ⊆-trans

⊆-partial-order : (n : ℕ) → IsPartialOrder _≡_ (_⊆_ {n})
IsPartialOrder.isPreorder (⊆-partial-order n) = ⊆-preorder n
IsPartialOrder.antisym (⊆-partial-order n) = ⊆-antisym

⊆-poset : (n : ℕ) → Poset _ _ _
Poset.Carrier (⊆-poset n) = VarSet n
Poset._≈_ (⊆-poset n) = _≡_
Poset._≤_ (⊆-poset n) = _⊆_
Poset.isPartialOrder (⊆-poset n) = ⊆-partial-order n

⊆-top : (xs : VarSet n) → xs ⊆ full
⊆-top xs = sym (∪-left-zero xs)

⊆-bot : (xs : VarSet n) → empty ⊆ xs
⊆-bot xs = sym (∪-right-unit xs)

⊆-step : (xs : VarSet n) → ewf xs ⊆ ewt xs
⊆-step xs = cong ewt (sym (∪-idem xs))

⊆-cong : {xs ys : VarSet n} → (b : Bool) → xs ⊆ ys → (b ∷ xs) ⊆ (b ∷ ys)
⊆-cong b p = cong₂ _∷_ (sym (∨-idem b)) p

⊆-drop : (xs : VarSet n) → drop xs ⊆ xs
⊆-drop emp = ⊆-refl
⊆-drop (ewf xs) = ⊆-cong false (⊆-drop xs)
⊆-drop (ewt xs) = ⊆-step xs

⊆-vs-sub : (σ : Sub n m ⋆) → {xs ys : VarSet n} → xs ⊆ ys → xs [ σ ]vs ⊆ ys [ σ ]vs
⊆-vs-sub σ {xs} {ys} p = begin
  ys [ σ ]vs
    ≡⟨ cong (_[ σ ]vs) p ⟩
  (ys ∪ xs) [ σ ]vs
    ≡⟨ vs-sub-∪ ys xs σ ⟩
  ys [ σ ]vs ∪ xs [ σ ]vs ∎
  where
    open ≡-Reasoning

lookup-isVar-⊆ : (xs : VarSet n) → (s : Tm n) → .⦃ _ : isVar s ⦄ → Truth (lookup-isVar xs s) → FVTm s ⊆ xs
lookup-isVar-⊆ (ewt xs) (Var zero) p = cong ewt (sym (∪-right-unit xs))
lookup-isVar-⊆ (ewf xs) (Var (suc i)) p = cong ewf (lookup-isVar-⊆ xs (Var i) p)
lookup-isVar-⊆ (ewt xs) (Var (suc i)) p = cong ewt (lookup-isVar-⊆ xs (Var i) p)

vs-sub-comp : (xs : VarSet l) → (σ : Sub n m ⋆) → (τ : Sub l n ⋆) → xs [ τ ● σ ]vs ≡ xs [ τ ]vs [ σ ]vs
vs-sub-comp emp σ ⟨ _ ⟩′ = sym (vs-sub-empty σ)
vs-sub-comp (ewf xs) σ ⟨ τ , t ⟩ = vs-sub-comp xs σ τ
vs-sub-comp (ewt xs) σ ⟨ τ , t ⟩ = begin
  xs [ τ ● σ ]vs ∪ FVTm (t [ σ ]tm)
    ≡⟨ cong₂ _∪_ (vs-sub-comp xs σ τ) (sym (vs-sub-tm t σ)) ⟩
  xs [ τ ]vs [ σ ]vs ∪ (FVTm t) [ σ ]vs
    ≡˘⟨ vs-sub-∪ (xs [ τ ]vs) (FVTm t) σ ⟩
  (xs [ τ ]vs ∪ FVTm t) [ σ ]vs ∎
  where
    open ≡-Reasoning

isVar-fv : (t : Tm n) → .⦃ _ : isVar t ⦄ → FVTm t ≡ trueAt (getVarFin t)
isVar-fv (Var i) = refl

↓-fv : (σ : Sub n m (s ─⟨ A ⟩⟶ t)) → FVSub (↓ σ) ≡ FVSub σ
↓-fv ⟨ _ ⟩′ = refl
↓-fv ⟨ σ , t ⟩ = cong (_∪ FVTm t) (↓-fv σ)

coh-sub-fv : (Γ : Ctx (suc n)) → (A : Ty (suc n)) → (σ : Sub (suc n) m B) → FVTm (Coh Γ A idSub [ σ ]tm) ≡ FVSub σ
coh-sub-fv {B = ⋆} Γ A σ = FVSub-≃ (id-left-unit σ)
coh-sub-fv {B = s ─⟨ B ⟩⟶ t} Γ A σ = begin
  FVTm (Coh (susp-ctx Γ) (susp-ty A) (susp-sub idSub) [ ↓ σ ]tm)
    ≡⟨ FVTm-≃ (sub-action-≃-tm (Coh≃ (refl≃c {Γ = susp-ctx Γ}) refl≃ty susp-functorial-id) (refl≃s {σ = ↓ σ})) ⟩
  FVTm (Coh (susp-ctx Γ) (susp-ty A) idSub [ ↓ σ ]tm)
    ≡⟨ coh-sub-fv (susp-ctx Γ) (susp-ty A) (↓ σ) ⟩
  FVSub (↓ σ)
    ≡⟨ ↓-fv σ ⟩
  FVSub σ ∎
  where
    open ≡-Reasoning

∪-⊆-2 : (xs ys : VarSet n) → ys ⊆ xs ∪ ys
∪-⊆-2 xs ys = begin
  xs ∪ ys
    ≡˘⟨ cong (xs ∪_) (∪-idem ys) ⟩
  xs ∪ (ys ∪ ys)
    ≡˘⟨ ∪-assoc xs ys ys ⟩
  xs ∪ ys ∪ ys ∎
  where
    open ≡-Reasoning

∪-⊆-1 : (xs ys : VarSet n) → xs ⊆ xs ∪ ys
∪-⊆-1 xs ys = begin
  xs
    ≤⟨ ∪-⊆-2 ys xs ⟩
  ys ∪ xs
    ≡⟨ ∪-comm ys xs ⟩
  xs ∪ ys ∎
  where
    open PReasoning (⊆-poset _)

ty-tgt′-⊆ : (A : Ty (suc n)) → .⦃ NonZero (ty-dim A) ⦄ → FVTm (ty-tgt′ A) ⊆ FVTy A
ty-tgt′-⊆ (s ─⟨ A ⟩⟶ t) = ∪-⊆-2 (FVTy A ∪ FVTm s) (FVTm t)

vs-sub-idSub≃ : (xs : VarSet n) → (p : Γ ≃c Δ) → xs [ idSub≃ p ]vs ≡ᵖ xs
vs-sub-idSub≃ emp Emp≃ = P.refl refl
vs-sub-idSub≃ (ewf xs) (Add≃ p y) = P.trans trans (P.≡⇒Pointwise-≡ (vs-sub-wk xs (idSub≃ p))) (refl P.∷ vs-sub-idSub≃ xs p)
vs-sub-idSub≃ (ewt xs) (Add≃ p y) = P.trans trans (P.≡⇒Pointwise-≡ (trans (cong (_∪ ewt empty) (vs-sub-wk xs (idSub≃ p))) (cong ewt (∪-right-unit (xs [ idSub≃ p ]vs))))) (refl P.∷ vs-sub-idSub≃ xs p)

∪-Truth : (xs ys : VarSet n) → (i : Fin n) → Truth (lookup (xs ∪ ys) i) → Truth (lookup xs i) ⊎ Truth (lookup ys i)
∪-Truth (x ∷ xs) (y ∷ ys) (suc i) truth = ∪-Truth xs ys i truth
∪-Truth (ewf xs) (y ∷ ys) zero truth = inj₂ truth
∪-Truth (ewt xs) (y ∷ ys) zero truth = inj₁ tt

sub-type-⊆ : (σ : Sub n m A) → FVTy A ⊆ FVSub σ
sub-type-⊆ ⟨ _ ⟩′ = ⊆-refl
sub-type-⊆ ⟨ σ , t ⟩ = ⊆-trans (sub-type-⊆ σ) (∪-⊆-1 (FVSub σ) (FVTm t))

∪-⊆ : {xs ys zs : VarSet n} → xs ⊆ zs → ys ⊆ zs → xs ∪ ys ⊆ zs
∪-⊆ {xs = xs} {ys} {zs} p q = begin
  zs
    ≡⟨ q ⟩
  zs ∪ ys
    ≡⟨ cong (_∪ ys) p ⟩
  zs ∪ xs ∪ ys
    ≡⟨ ∪-assoc zs xs ys ⟩
  zs ∪ (xs ∪ ys) ∎
  where
    open ≡-Reasoning

DC-⊆ : (Γ : Ctx n) → (xs : VarSet n) → xs ⊆ DC Γ xs
DC-⊆ ∅ emp = ⊆-refl
DC-⊆ (Γ , A) (ewf xs) = cong ewf (DC-⊆ Γ xs)
DC-⊆ (Γ , A) (ewt xs) = cong ewt (begin
  xs
    ≤⟨ ∪-⊆-1 xs (FVTy A) ⟩
  xs ∪ FVTy A
    ≤⟨ DC-⊆ Γ (xs ∪ FVTy A) ⟩
  DC Γ (xs ∪ FVTy A) ∎)
  where
    open PReasoning (⊆-poset _)

module _ where
  open ≡-Reasoning

  DC-∪ : (Γ : Ctx n) → (xs ys : VarSet n) → DC Γ (xs ∪ ys) ≡ DC Γ xs ∪ DC Γ ys
  DC-∪ ∅ xs ys = refl
  DC-∪ (Γ , A) (ewf xs) (ewf ys) = cong ewf (DC-∪ Γ xs ys)
  DC-∪ (Γ , A) (ewf xs) (ewt ys) = cong ewt (begin
    DC Γ (xs ∪ ys ∪ FVTy A)
      ≡⟨ cong (DC Γ) (∪-assoc xs ys (FVTy A)) ⟩
    DC Γ (xs ∪ (ys ∪ FVTy A))
      ≡⟨ DC-∪ Γ xs (ys ∪ FVTy A) ⟩
    (DC Γ xs) ∪ (DC Γ (ys ∪ FVTy A)) ∎)
  DC-∪ (Γ , A) (ewt xs) (ewf ys) = cong ewt (begin
    DC Γ (xs ∪ ys ∪ FVTy A)
      ≡⟨ cong (DC Γ) (∪-assoc xs ys (FVTy A)) ⟩
    DC Γ (xs ∪ (ys ∪ FVTy A))
      ≡⟨ cong (λ - → DC Γ (xs ∪ -)) (∪-comm ys (FVTy A)) ⟩
    DC Γ (xs ∪ (FVTy A ∪ ys))
      ≡˘⟨ cong (DC Γ) (∪-assoc xs (FVTy A) ys) ⟩
    DC Γ (xs ∪ FVTy A ∪ ys)
      ≡⟨ DC-∪ Γ (xs ∪ FVTy A) ys ⟩
    (DC Γ (xs ∪ FVTy A)) ∪ (DC Γ ys) ∎)
  DC-∪ {suc n} (Γ , A) (ewt xs) (ewt ys) = cong ewt (begin
    DC Γ (xs ∪ ys ∪ FVTy A)
      ≡˘⟨ cong (λ - → DC Γ (xs ∪ ys ∪ -)) (∪-idem (FVTy A)) ⟩
    DC Γ (xs ∪ ys ∪ (FVTy A ∪ FVTy A))
      ≡⟨ cong (DC Γ) (solve (∪-monoid {n})) ⟩
    DC Γ (xs ∪ (ys ∪ FVTy A) ∪ FVTy A)
      ≡⟨ cong (λ - → DC Γ (xs ∪ - ∪ FVTy A)) (∪-comm ys (FVTy A)) ⟩
    DC Γ (xs ∪ (FVTy A ∪ ys) ∪ FVTy A)
      ≡⟨ cong (DC Γ) (solve (∪-monoid {n})) ⟩
    DC Γ ((xs ∪ FVTy A) ∪ (ys ∪ FVTy A))
      ≡⟨ DC-∪ Γ (xs ∪ FVTy A) (ys ∪ FVTy A) ⟩
    DC Γ (xs ∪ FVTy A) ∪ DC Γ (ys ∪ FVTy A) ∎)

  DC-idem : (Γ : Ctx n) → (xs : VarSet n) → DC Γ (DC Γ xs) ≡ DC Γ xs
  DC-idem ∅ xs = refl
  DC-idem (Γ , A) (ewf xs) = cong ewf (DC-idem Γ xs)
  DC-idem (Γ , A) (ewt xs) = cong ewt (begin
    DC Γ (DC Γ (xs ∪ FVTy A) ∪ FVTy A)
      ≡⟨ cong (λ - → DC Γ (- ∪ FVTy A)) (DC-∪ Γ xs (FVTy A)) ⟩
    DC Γ (DC Γ xs ∪ DC Γ (FVTy A) ∪ FVTy A)
      ≡⟨ cong (DC Γ) (∪-assoc (DC Γ xs) (DC Γ (FVTy A)) (FVTy A)) ⟩
    DC Γ (DC Γ xs ∪ (DC Γ (FVTy A) ∪ FVTy A))
      ≡˘⟨ cong (λ - → DC Γ (DC Γ xs ∪ -)) (DC-⊆ Γ (FVTy A)) ⟩
    DC Γ (DC Γ xs ∪ DC Γ (FVTy A))
      ≡˘⟨ cong (DC Γ) (DC-∪ Γ xs (FVTy A)) ⟩
    DC Γ (DC Γ (xs ∪ FVTy A))
      ≡⟨ DC-idem Γ (xs ∪ FVTy A) ⟩
    DC Γ (xs ∪ FVTy A) ∎)

  DC-empty : (Γ : Ctx n) → DC Γ empty ≡ empty
  DC-empty ∅ = refl
  DC-empty (Γ , A) = cong ewf (DC-empty Γ)

  DC-full : (Γ : Ctx n) → DC Γ full ≡ full
  DC-full ∅ = refl
  DC-full (Γ , A) = cong ewt (trans (cong (DC Γ) (∪-left-zero (FVTy A))) (DC-full Γ))

⊆-cong-∪-1 : {xs ys zs : VarSet n} → ys ⊆ zs → xs ∪ ys ⊆ xs ∪ zs
⊆-cong-∪-1 p = ∪-⊆ (∪-⊆-1 _ _) (⊆-trans p (∪-⊆-2 _ _))

build-⊆-1 : (x : Bool) → {xs ys : VarSet n} → xs ⊆ ys → ewf xs ⊆ (x ∷ ys)
build-⊆-1 x p = cong₂ _∷_ (sym (∨-identityʳ x)) p

build-⊆-2 : (x : Bool) → {xs ys : VarSet n} → xs ⊆ ys → (x ∷ xs) ⊆ ewt ys
build-⊆-2 x p = cong ewt p

debuild-⊆-2 : {x y : Bool} → {xs ys : VarSet n} → (x ∷ xs) ⊆ (y ∷ ys) → xs ⊆ ys
debuild-⊆-2 p = cong tail p

FVTy-comp-⊆ : (A : Ty n) → (σ : Sub n m B) → FVTy (A [ σ ]ty) ⊆ FVSub σ
FVTm-comp-⊆ : (t : Tm n) → (σ : Sub n m A) → FVTm (t [ σ ]tm) ⊆ FVSub σ
FVSub-comp-⊆ : (τ : Sub l n ⋆) → (σ : Sub n m A) → FVSub (τ ● σ) ⊆ FVSub σ

FVTy-comp-⊆ ⋆ σ = sub-type-⊆ σ
FVTy-comp-⊆ (s ─⟨ A ⟩⟶ t) σ = ∪-⊆ (∪-⊆ (FVTy-comp-⊆ A σ) (FVTm-comp-⊆ s σ)) (FVTm-comp-⊆ t σ)

FVTm-comp-⊆ (Var zero) ⟨ σ , t ⟩ = ∪-⊆-2 (FVSub σ) (FVTm t)
FVTm-comp-⊆ (Var (suc i)) ⟨ σ , t ⟩ = ⊆-trans (FVTm-comp-⊆ (Var i) σ) (∪-⊆-1 (FVSub σ) (FVTm t))
FVTm-comp-⊆ {A = ⋆} (Coh S B τ) σ = FVSub-comp-⊆ τ σ
FVTm-comp-⊆ {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) σ = begin
  FVTm
      (Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ ↓ σ ]tm)
    ≤⟨ FVTm-comp-⊆ (Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ)) (↓ σ) ⟩
  FVSub (↓ σ)
    ≡⟨ ↓-fv σ ⟩
  FVSub σ ∎
  where
    open PReasoning (⊆-poset _)

FVSub-comp-⊆ ⟨ _ ⟩′ σ = sub-type-⊆ σ
FVSub-comp-⊆ ⟨ τ , t ⟩ σ = begin
  FVSub (τ ● σ) ∪ FVTm (t [ σ ]tm)
    ≤⟨ ⊆-cong-∪-1 (FVTm-comp-⊆ t σ) ⟩
  FVSub (τ ● σ) ∪ FVSub σ
    ≤⟨ ∪-⊆ (FVSub-comp-⊆ τ σ) ⊆-refl ⟩
  FVSub σ ∎
  where
    open PReasoning (⊆-poset _)

SuppContainsType : (t : Tm n) → (Γ : Ctx n) → SuppTy Γ (tm-to-ty Γ t) ⊆ SuppTm Γ t
SuppContainsType (Var zero) (Γ , A) = begin
  SuppTy (Γ , A) (wk-ty A)
    ≡⟨ cong (DC (Γ , A)) (fv-wk-ty A) ⟩
  ewf (SuppTy Γ A)
    ≤⟨ cong ewt (sym (∪-idem (SuppTy Γ A))) ⟩
  ewt (SuppTy Γ A)
    ≡˘⟨ cong (λ - → ewt (DC Γ -)) (∪-left-unit (FVTy A)) ⟩
  ewt (DC Γ (empty ∪ FVTy A))
    ≡⟨⟩
  SuppTm (Γ , A) 0V ∎
  where
    open PReasoning (⊆-poset _)

SuppContainsType (Var (suc i)) (Γ , A) = begin
  SuppTy (Γ , A) (wk-ty (Γ ‼ i))
    ≡⟨ cong (DC (Γ , A)) (fv-wk-ty (Γ ‼ i)) ⟩
  ewf (SuppTy Γ (Γ ‼ i))
    ≤⟨ cong ewf (SuppContainsType (Var i) Γ) ⟩
  ewf (SuppTm Γ (Var i))
    ≡⟨⟩
  SuppTm (Γ , A) (Var (suc i)) ∎
  where
    open PReasoning (⊆-poset _)

SuppContainsType (Coh S A σ) Γ = trans (cong (DC Γ) (FVTy-comp-⊆ A σ)) (DC-∪ Γ (FVTm (Coh S A σ)) (FVTy (A [ σ ]ty)))

full-⊆ : {xs : VarSet n} → full ⊆ xs → xs ≡ full
full-⊆ p = trans p (∪-right-zero _)

DC-is-DC : (Γ : Ctx n) → (xs : VarSet n) → is-DC Γ (DC Γ xs)
DC-is-DC ∅ emp = tt
DC-is-DC (Γ , A) (ewf xs) = DC-is-DC Γ xs
DC-is-DC (Γ , A) (ewt xs) = (DC-is-DC Γ (xs ∪ FVTy A)) ,, ⊆-trans (∪-⊆-2 xs (FVTy A)) (DC-⊆ Γ (xs ∪ FVTy A))

drop-var : (t : Tm n) → .⦃ isVar t ⦄ → drop (FVTm t) ≡ empty
drop-var (Var 0F) = refl
drop-var (Var (suc i)) = cong ewf (drop-var (Var i))

DC-fromℕ : (Γ : Ctx (suc n)) → SuppTm Γ (Var (fromℕ n)) ≡ trueAt (fromℕ n)
DC-fromℕ {n = zero} (∅ , A) = refl
DC-fromℕ {n = suc n} (Γ , A) = cong ewf (DC-fromℕ Γ)

DC-cong-⊆ : (Γ : Ctx n) → {xs ys : VarSet n} → xs ⊆ ys → DC Γ xs ⊆ DC Γ ys
DC-cong-⊆ Γ {xs} {ys} p = begin
  DC Γ ys
    ≡⟨ cong (DC Γ) p ⟩
  DC Γ (ys ∪ xs)
    ≡⟨ DC-∪ Γ ys xs ⟩
  DC Γ ys ∪ DC Γ xs ∎
  where
    open ≡-Reasoning

lookup-empty : (i : Fin n) → lookup empty i ≡ false
lookup-empty 0F = refl
lookup-empty (suc i) = lookup-empty i

lookup-trueAt : (i : Fin n) → lookup (trueAt i) i ≡ true
lookup-trueAt 0F = refl
lookup-trueAt (suc i) = lookup-trueAt i

lookup-∪ : (xs ys : VarSet n) → (i : Fin n) → lookup (xs ∪ ys) i ≡ lookup xs i ∨ lookup ys i
lookup-∪ (x ∷ xs) (y ∷ ys) 0F = refl
lookup-∪ (x ∷ xs) (y ∷ ys) (suc i) = lookup-∪ xs ys i

trueAt-non-empty : (i : Fin n) → Truth (varset-non-empty (trueAt i))
trueAt-non-empty 0F = tt
trueAt-non-empty (suc i) = trueAt-non-empty i

∪-non-empty-right : (xs ys : VarSet n) → Truth (varset-non-empty ys) → Truth (varset-non-empty (xs ∪ ys))
∪-non-empty-right (ewf xs) (ewf ys) t = ∪-non-empty-right xs ys t
∪-non-empty-right (ewf xs) (ewt ys) t = tt
∪-non-empty-right (ewt xs) (x ∷ ys) t = tt

empty-is-empty : {n : ℕ} → varset-non-empty (empty {n = n}) ≡ false
empty-is-empty {n = zero} = refl
empty-is-empty {n = suc n} = empty-is-empty {n = n}

pdb-bd-vs-full : (n : ℕ)
                 → (Γ : Ctx m)
                 → .⦃ _ : Γ ⊢pdb ⦄
                 → (b : Bool)
                 → n ≥ ctx-dim Γ
                 → pdb-bd-vs n Γ b ≡ full
pdb-bd-vs-full n ∅ ⦃ pdb ⦄ b p = ⊥-elim (pdb-odd-length pdb)
pdb-bd-vs-full n (∅ , A) b p = refl
pdb-bd-vs-full n (Γ , B , A) b p = begin
  pdb-bd-vs n (Γ , B , A) b
    ≡⟨ tri-case> lem (<-cmp n (ty-dim B)) _ _ _ ⟩
  ewt (ewt (pdb-bd-vs n Γ ⦃ pdb-prefix it ⦄ b))
    ≡⟨ cong (ewt ∘ ewt) (pdb-bd-vs-full n Γ ⦃ pdb-prefix it ⦄ b lem2) ⟩
  ewt (ewt full) ∎
  where
    lem : ty-dim B < n
    lem = begin
      suc (ty-dim B)
        ≡˘⟨ pdb-dim-proj (recompute (pdb-dec (Γ , B , A)) it) ⟩
      ty-dim A
        ≤⟨ m≤n⊔m (ctx-dim Γ ⊔ ty-dim B) (ty-dim A) ⟩
      ctx-dim (Γ , B) ⊔ ty-dim A
        ≤⟨ p ⟩
      n ∎
      where
        open ≤-Reasoning

    lem2 : ctx-dim Γ ≤ n
    lem2 = begin
      ctx-dim Γ
        ≤⟨ m≤m⊔n (ctx-dim Γ) (ty-dim B) ⟩
      ctx-dim Γ ⊔ ty-dim B
        ≤⟨ m≤m⊔n (ctx-dim Γ ⊔ ty-dim B) (ty-dim A) ⟩
      ctx-dim Γ ⊔ ty-dim B ⊔ ty-dim A
        ≤⟨ p ⟩
      n ∎
      where
        open ≤-Reasoning
    open ≡-Reasoning

pd-bd-vs-full : (n : ℕ)
                → (Γ : Ctx m)
                → .⦃ _ : Γ ⊢pd ⦄
                → (b : Bool)
                → n ≥ ctx-dim Γ
                → pd-bd-vs n Γ b ≡ full
pd-bd-vs-full n Γ b p = pdb-bd-vs-full n Γ ⦃ pd-to-pdb it ⦄ b p
