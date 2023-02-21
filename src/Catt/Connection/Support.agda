module Catt.Connection.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Connection
open import Catt.Connection.Pasting
open import Catt.Connection.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Catt.Suspension.Support
open import Catt.Tree
open import Catt.Variables
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using (Pointwise; Pointwise-≡⇒≡)
open import Relation.Binary.Definitions
open import Tactic.MonoidSolver

connect-supp : VarSet (suc n) → (t : Tm (suc n)) → VarSet (suc m) → VarSet (suc (m + n))
connect-supp {m = zero} xs t (ewf ys) = xs
connect-supp {m = zero} xs t (ewt ys) = xs ∪ FVTm t
connect-supp {m = suc m} xs t (x ∷ ys) = x ∷ connect-supp xs t ys

connect-susp-supp : VarSet (3 + n) → VarSet (suc m) → VarSet (suc (m + (2 + n)))
connect-susp-supp xs ys = connect-supp xs get-snd ys

connect-supp-empty : (n : ℕ) → (t : Tm (suc n)) → (m : ℕ) → connect-supp {n = n} {m = m} empty t empty ≡ empty
connect-supp-empty n t zero = refl
connect-supp-empty n t (suc m) = cong ewf (connect-supp-empty n t m)

connect-susp-supp-base : (xs : VarSet (suc n)) → (b : Bool) → connect-susp-supp (suspSupp xs) (b ∷ emp) ≡ suspSupp xs
connect-susp-supp-base xs true = sym (lookup-isVar-⊆ (suspSupp xs) get-snd (suspSuppSndTruth xs))
connect-susp-supp-base xs false = refl

VarSet-NonEmpty-Special : (xs : VarSet n) → Set
VarSet-NonEmpty-Special {zero} xs = ⊥
VarSet-NonEmpty-Special {suc zero} xs = ⊥
VarSet-NonEmpty-Special {suc (suc n)} (ewf xs) = VarSet-NonEmpty-Special xs
VarSet-NonEmpty-Special {suc (suc n)} (ewt xs) = ⊤

connect-drop : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → .⦃ VarSet-NonEmpty-Special ys ⦄ → connect-susp-supp xs (drop ys) ≡ drop (connect-susp-supp (xs) ys)
connect-drop xs (ewf (y ∷ ys)) = cong ewf (connect-drop xs (y ∷ ys))
connect-drop xs (ewt (y ∷ ys)) = refl

pdb-bd-supp-non-empty-special : (n : ℕ) → (Γ : Ctx (suc m)) → .⦃ pdb : Γ ⊢pdb ⦄ → (b : Bool) → .⦃ NonZero m ⦄ → VarSet-NonEmpty-Special (pdb-bd-supp (suc n) Γ b)
pdb-bd-supp-non-empty-special n (∅ , B , A) ⦃ pdb ⦄ b = ⊥-elim (pdb-odd-length pdb)
pdb-bd-supp-non-empty-special n (Γ , C , B , A) b with <-cmp (suc n) (ty-dim B) | b
... | tri< a ¬b ¬c | b = pdb-bd-supp-non-empty-special n (Γ , C) ⦃ pdb-prefix it ⦄ b ⦃ focus-ty-dim-to-non-empty (pdb-prefix it) (≤-trans (≤-trans (s≤s z≤n) a) (≤-reflexive (ty-dim-≃ (pdb-proj₁ it)))) ⦄
... | tri≈ ¬a b₁ ¬c | false = pdb-bd-supp-non-empty-special n (Γ , C) ⦃ pdb-prefix it ⦄ false ⦃ focus-ty-dim-to-non-empty (pdb-prefix it) (≤-trans (≤-trans (s≤s z≤n) (≤-reflexive b₁)) (≤-reflexive (ty-dim-≃ (pdb-proj₁ it )))) ⦄
... | tri≈ ¬a b₁ ¬c | true = tt
... | tri> ¬a ¬b c | b = tt

connect-susp-pdb-bd-compat : (n : ℕ)
                      → (Γ : Ctx (suc m))
                      → .⦃ pd : Γ ⊢pd ⦄
                      → (Δ : Ctx (suc l))
                      → .⦃ pdb : Δ ⊢pdb ⦄
                      → (b : Bool)
                      → connect-susp-supp (suspSupp (pd-bd-supp n Γ b)) (pdb-bd-supp (suc n) Δ b) ≡ pdb-bd-supp (suc n) (connect-susp Γ Δ) ⦃ connect-susp-pdb pd pdb ⦄ b
connect-susp-pdb-bd-compat n Γ ⦃ pd ⦄ (∅ , A) b = begin
  connect-susp-supp (suspSupp (pd-bd-supp n Γ b)) (ewt emp)
    ≡⟨ connect-susp-supp-base (pd-bd-supp n Γ b) true ⟩
  suspSupp (pd-bd-supp n Γ b)
    ≡⟨ susp-pd-bd-compat n Γ b ⟩
  pd-bd-supp (suc n) (susp-ctx Γ) ⦃ susp-pd it ⦄ b ∎
  where
    open ≡-Reasoning
-- susp-pdb-bd-compat n Γ ⦃ pd-to-pdb pd ⦄ b
connect-susp-pdb-bd-compat n Γ (∅ , B , A) b = ⊥-elim (pdb-odd-length it)
connect-susp-pdb-bd-compat {m = m} n Γ (Δ , C , B , A) b with ty-dim B | ty-dim (B [ connect-susp-inc-right m _ ]ty) | .(ty-dim-≃ (pdb-proj₁ {Γ = Δ , C} it)) | sub-dim (connect-susp-inc-right m _) B
... | x | .x | p | refl with <-cmp (suc n) x | b
... | tri< a ¬b ¬c | b = cong ewf (cong ewf (connect-susp-pdb-bd-compat n Γ (Δ , C) ⦃ pdb-prefix it ⦄ b))
... | tri≈ ¬a b₁ ¬c | false = cong ewf (cong ewf (connect-susp-pdb-bd-compat n Γ (Δ , C) ⦃ pdb-prefix it ⦄ false))
... | tri≈ ¬a b₁ ¬c | true = cong ewf (cong ewt (trans (connect-drop (suspSupp (pd-bd-supp n Γ true)) (pdb-bd-supp (suc n) (Δ , C) ⦃ pdb-prefix it ⦄ true) ⦃ pdb-bd-supp-non-empty-special n (Δ , C) ⦃ pdb-prefix it ⦄ true ⦃ focus-ty-dim-to-non-empty (pdb-prefix it) (≤-trans (≤-trans (s≤s z≤n) (≤-reflexive b₁)) (≤-reflexive p)) ⦄ ⦄) (cong drop (connect-susp-pdb-bd-compat n Γ (Δ , C) ⦃ pdb-prefix it ⦄ true))))
... | tri> ¬a ¬b c | b = cong ewt (cong ewt (connect-susp-pdb-bd-compat n Γ (Δ , C) ⦃ pdb-prefix it ⦄ b))

connect-susp-pd-bd-compat : (n : ℕ)
                      → (Γ : Ctx (suc m))
                      → .⦃ pd : Γ ⊢pd ⦄
                      → (Δ : Ctx (suc l))
                      → .⦃ pd2 : Δ ⊢pd ⦄
                      → (b : Bool)
                      → connect-susp-supp (suspSupp (pd-bd-supp n Γ b)) (pd-bd-supp (suc n) Δ b) ≡ pd-bd-supp (suc n) (connect-susp Γ Δ) ⦃ connect-susp-pd pd pd2 ⦄ b
connect-susp-pd-bd-compat n Γ ⦃ pd ⦄ Δ ⦃ pd2 ⦄ b = connect-susp-pdb-bd-compat n Γ Δ ⦃ pd-to-pdb pd2 ⦄ b

connect-supp-full : ∀ n (t : Tm (suc n)) m → connect-supp {n} {m} full t full ≡ full
connect-supp-full n t zero = ∪-left-zero (FVTm t)
connect-supp-full n t (suc m) = cong ewt (connect-supp-full n t m)

connect-supp-inc-left : (xs : VarSet (suc n)) → (t : Tm (suc n)) → (m : ℕ) → TransportVarSet xs (connect-inc-left t m) ≡ connect-supp xs t empty
connect-supp-inc-left xs t zero = TransportVarSet-id xs
connect-supp-inc-left xs t (suc m) = begin
  TransportVarSet xs (lift-sub (connect-inc-left t m))
    ≡⟨ TransportVarSet-lift xs (connect-inc-left t m) ⟩
  ewf (TransportVarSet xs (connect-inc-left t m))
    ≡⟨ cong ewf (connect-supp-inc-left xs t m) ⟩
  ewf (connect-supp xs t empty) ∎
  where
    open ≡-Reasoning

connect-supp-inc-right : (t : Tm (suc n)) → (ys : VarSet (suc m)) → TransportVarSet ys (connect-inc-right t m) ≡ connect-supp empty t ys
connect-supp-inc-right {m = zero} t (ewf ys) = refl
connect-supp-inc-right {m = zero} t (ewt ys) = refl
connect-supp-inc-right {m = suc m} t (ewf ys) = begin
  TransportVarSet ys (lift-sub (connect-inc-right t m))
    ≡⟨ TransportVarSet-lift ys (connect-inc-right t m) ⟩
  ewf (TransportVarSet ys (connect-inc-right t m))
    ≡⟨ cong ewf (connect-supp-inc-right t ys) ⟩
  ewf (connect-supp empty t ys) ∎
  where
    open ≡-Reasoning
connect-supp-inc-right {m = suc m} t (ewt ys) = begin
  TransportVarSet ys (lift-sub (connect-inc-right t m)) ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) (TransportVarSet-lift ys (connect-inc-right t m)) ⟩
  ewt (TransportVarSet ys (connect-inc-right t m) ∪ empty)
    ≡⟨ cong ewt (∪-right-unit (TransportVarSet ys (connect-inc-right t m))) ⟩
  ewt (TransportVarSet ys (connect-inc-right t m))
    ≡⟨ cong ewt (connect-supp-inc-right t ys) ⟩
  ewt (connect-supp empty t ys) ∎
  where
    open ≡-Reasoning

connect-supp-fst : (t : Tm (suc n)) → (m : ℕ) → connect-supp (trueAt (fromℕ n)) t (empty {n = suc m}) ≡ trueAt (fromℕ (m + n))
connect-supp-fst t zero = refl
connect-supp-fst t (suc m) = cong ewf (connect-supp-fst t m)

connect-supp-∪ : (xs xs′ : VarSet (suc n)) → (ys ys′ : VarSet (suc m)) → (t : Tm (suc n)) → connect-supp (xs ∪ xs′) t (ys ∪ ys′) ≡ connect-supp xs t ys ∪ connect-supp xs′ t ys′
connect-supp-∪ {m = zero} xs xs′ (ewf ys) (ewf ys′) t = refl
connect-supp-∪ {n = n} {m = zero} xs xs′ (ewf ys) (ewt ys′) t = solve (∪-monoid {n = suc n})
connect-supp-∪ {n = n} {m = zero} xs xs′ (ewt ys) (ewf ys′) t
  = prove 3 ((var 0F ⊕ var 1F) ⊕ var 2F) ((var 0F ⊕ var 2F) ⊕ var 1F) (_ ∷ _ ∷ _ ∷ emp)
  where
    open Solver ∪-idempotentCommutativeMonoid
connect-supp-∪ {n = n} {m = zero} xs xs′ (ewt ys) (ewt ys′) t
  = prove 3 ((var 0F ⊕ var 1F) ⊕ var 2F) ((var 0F ⊕ var 2F) ⊕ (var 1F ⊕ var 2F)) (_ ∷ _ ∷ _ ∷ emp)
  where
    open Solver ∪-idempotentCommutativeMonoid
connect-supp-∪ {m = suc m} xs xs′ (y ∷ ys) (y′ ∷ ys′) t = cong ((y ∨ y′) ∷_) (connect-supp-∪ xs xs′ ys ys′ t)

connect-susp-supp-lem : (xs : VarSet (suc n)) → (ys : VarSet (suc m)) → connect-susp-supp (suspSupp xs) ys ≡ connect-susp-supp (suspSupp xs) (trueAt (fromℕ _) ∪ ys)
connect-susp-supp-lem {m = zero} xs (ewf emp) = lookup-isVar-⊆ (suspSupp xs) get-snd (suspSuppSndTruth xs)
connect-susp-supp-lem {m = zero} xs (ewt emp) = refl
connect-susp-supp-lem {m = suc m} xs (y ∷ ys) = cong (y ∷_) (connect-susp-supp-lem xs ys)

connect-supp-DC : (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m)) → (xs : VarSet (suc n)) → (ys : VarSet (suc m))
                → DC Γ (FVTm t) ≡ FVTm t
                → DC (connect Γ t Δ) (connect-supp xs t ys) ≡ connect-supp (DC Γ xs) t (DC Δ ys)
connect-supp-DC {m = zero} Γ t (Δ , A) xs (ewf ys) p = refl
connect-supp-DC {m = zero} Γ t (Δ , A) xs (ewt ys) p = trans (DC-∪ Γ xs (FVTm t)) (cong (DC Γ xs ∪_) p)
connect-supp-DC {m = suc m} Γ t (Δ , A) xs (ewf ys) p = cong ewf (connect-supp-DC Γ t Δ xs ys p)
connect-supp-DC {m = suc m} Γ t (Δ , A) xs (ewt ys) p = cong ewt (begin
  DC (connect Γ t Δ) (connect-supp xs t ys ∪ FVTy (A [ connect-inc-right t m ]ty))
    ≡˘⟨ cong (λ - → DC (connect Γ t Δ) (connect-supp xs t ys ∪ -)) (TransportVarSet-ty A (connect-inc-right t m)) ⟩
  DC (connect Γ t Δ) (connect-supp xs t ys ∪ TransportVarSet (FVTy A) (connect-inc-right t m))
    ≡⟨ cong (λ - → DC (connect Γ t Δ) (connect-supp xs t ys ∪ -)) (connect-supp-inc-right t (FVTy A)) ⟩
  DC (connect Γ t Δ) (connect-supp xs t ys ∪ connect-supp empty t (FVTy A))
    ≡˘⟨ cong (DC (connect Γ t Δ)) (connect-supp-∪ xs empty ys (FVTy A) t) ⟩
  DC (connect Γ t Δ) (connect-supp (xs ∪ empty) t (ys ∪ FVTy A))
    ≡⟨ cong (λ - → DC (connect Γ t Δ) (connect-supp - t (ys ∪ FVTy A))) (∪-right-unit xs) ⟩
  DC (connect Γ t Δ) (connect-supp xs t (ys ∪ FVTy A))
    ≡⟨ connect-supp-DC Γ t Δ xs (ys ∪ FVTy A) p ⟩
  connect-supp (DC Γ xs) t (DC Δ (ys ∪ FVTy A)) ∎)
  where
    open ≡-Reasoning

connect-susp-supp-DC : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → DC (connect-susp Γ Δ) (connect-susp-supp xs ys) ≡ connect-susp-supp (DC (susp-ctx Γ) xs) (DC Δ ys)
connect-susp-supp-DC Γ Δ xs ys = connect-supp-DC (susp-ctx Γ) get-snd Δ xs ys (lem Γ)
  where
    lem : (Γ : Ctx n) → DC (susp-ctx Γ) (FVTm get-snd) ≡ FVTm get-snd
    lem ∅ = refl
    lem (Γ , A) = cong ewf (lem Γ)

connect-susp-supp-ext : (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m))
                      → connect-susp-supp (suspSupp (SuppTm Γ t)) empty ≡ SuppTm (connect-susp Γ Δ) (susp-tm t [ connect-susp-inc-left n m ]tm)
connect-susp-supp-ext {m = m} Γ t Δ = begin
  connect-susp-supp (suspSupp (SuppTm Γ t)) empty
    ≡˘⟨ cong₂ connect-susp-supp (suspSuppTm′ Γ t) (DC-empty Δ) ⟩
  connect-susp-supp (SuppTm (susp-ctx Γ) (susp-tm t))
    (DC Δ empty)
    ≡˘⟨ connect-susp-supp-DC Γ Δ ((FVTm (susp-tm t))) empty ⟩
  DC (connect-susp Γ Δ) (connect-susp-supp (FVTm (susp-tm t)) empty)
    ≡˘⟨ cong (DC (connect-susp Γ Δ)) (connect-supp-inc-left (FVTm (susp-tm t)) get-snd m) ⟩
  DC (connect-susp Γ Δ) (TransportVarSet (FVTm (susp-tm t)) (connect-susp-inc-left _ m))
    ≡⟨ cong (DC (connect-susp Γ Δ)) (TransportVarSet-tm (susp-tm t) (connect-susp-inc-left _ m)) ⟩
  SuppTm (connect-susp Γ Δ) (susp-tm t [ connect-susp-inc-left _ m ]tm) ∎
     where
       open ≡-Reasoning

connect-susp-supp-shift : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → (t : Tm (suc m))
                        → connect-susp-supp empty (SuppTm Δ t) ≡ SuppTm (connect-susp Γ Δ) (t [ connect-susp-inc-right n m ]tm)
connect-susp-supp-shift Γ Δ t = begin
  connect-susp-supp empty (SuppTm Δ t)
    ≡˘⟨ cong (λ - → connect-susp-supp - (SuppTm Δ t)) (DC-empty (susp-ctx Γ)) ⟩
  connect-susp-supp (DC (susp-ctx Γ) empty) (SuppTm Δ t)
    ≡˘⟨ connect-susp-supp-DC Γ Δ empty (FVTm t) ⟩
  DC (connect-susp Γ Δ) (connect-susp-supp empty (FVTm t))
    ≡˘⟨ cong (DC (connect-susp Γ Δ)) (connect-supp-inc-right get-snd (FVTm t)) ⟩
  DC (connect-susp Γ Δ) (TransportVarSet (FVTm t) (connect-susp-inc-right _ _))
    ≡⟨ cong (DC (connect-susp Γ Δ)) (TransportVarSet-tm t (connect-susp-inc-right _ _)) ⟩
  SuppTm (connect-susp Γ Δ) (t [ connect-susp-inc-right _ _ ]tm) ∎
  where
    open ≡-Reasoning


sub-from-connect-supp : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A)
                      → FVTm (Var (fromℕ _) [ τ ]tm) ⊆ FVSub σ
                      → FVSub (sub-from-connect σ τ) ≡ FVSub σ ∪ FVSub τ
sub-from-connect-supp {l = l} {A = A} σ ⟨ ⟨⟩ , x ⟩ p = begin
  FVSub σ
    ≡⟨ p ⟩
  FVSub σ ∪ FVTm x
    ≡⟨ cong (_∪ FVTm x) (sub-type-⊆ σ) ⟩
  FVSub σ ∪ FVTy A ∪ FVTm x
    ≡⟨ ∪-assoc (FVSub σ) (FVTy A) (FVTm x) ⟩
  FVSub σ ∪ (FVTy A ∪ FVTm x) ∎
  where
    open ≡-Reasoning
sub-from-connect-supp {l = l} σ ⟨ ⟨ τ , y ⟩ , x ⟩ p = trans (cong (_∪ FVTm x) (sub-from-connect-supp σ ⟨ τ , y ⟩ p)) (solve (∪-monoid {l}))

sub-from-connect-supp′ : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A)
                       → SuppTm Γ (Var (fromℕ _) [ τ ]tm) ⊆ SuppSub Γ σ
                       → SuppSub Γ (sub-from-connect σ τ) ≡ SuppSub Γ σ ∪ SuppSub Γ τ
sub-from-connect-supp′ {A = A} {Γ = Γ} σ ⟨ ⟨⟩ , x ⟩ p = begin
  SuppSub Γ σ
    ≡⟨ p ⟩
  SuppSub Γ σ ∪ SuppTm Γ x
    ≡⟨ cong (_∪ SuppTm Γ x) (cong (DC Γ) (sub-type-⊆ σ)) ⟩
  DC Γ (FVSub σ ∪ FVTy A) ∪ SuppTm Γ x
    ≡⟨ cong (_∪ SuppTm Γ x) (DC-∪ Γ (FVSub σ) (FVTy A)) ⟩
  SuppSub Γ σ ∪ SuppTy Γ A ∪ SuppTm Γ x
    ≡⟨ ∪-assoc (DC Γ (FVSub σ)) (SuppTy Γ A) (SuppTm Γ x) ⟩
  SuppSub Γ σ ∪ (SuppTy Γ A ∪ SuppTm Γ x)
    ≡˘⟨ cong (SuppSub Γ σ ∪_) (DC-∪ Γ (FVTy A) (FVTm x)) ⟩
  SuppSub Γ σ ∪ (DC Γ (FVTy A ∪ FVTm x)) ∎
  where
    open ≡-Reasoning
sub-from-connect-supp′ {Γ = Γ} σ ⟨ ⟨ τ , y ⟩ , x ⟩ p = begin
  DC Γ (FVSub (sub-from-connect σ ⟨ τ , y ⟩) ∪ FVTm x)
    ≡⟨ DC-∪ Γ (FVSub (sub-from-connect σ ⟨ τ , y ⟩)) (FVTm x) ⟩
  SuppSub Γ (sub-from-connect σ ⟨ τ , y ⟩) ∪ SuppTm Γ x
    ≡⟨ cong (_∪ SuppTm Γ x) (sub-from-connect-supp′ σ ⟨ τ , y ⟩ p) ⟩
  SuppSub Γ σ ∪ SuppSub Γ ⟨ τ , y ⟩ ∪ SuppTm Γ x
    ≡⟨ ∪-assoc (SuppSub Γ σ) (SuppSub Γ ⟨ τ , y ⟩) (SuppTm Γ x) ⟩
  SuppSub Γ σ ∪ (SuppSub Γ ⟨ τ , y ⟩ ∪ SuppTm Γ x)
    ≡˘⟨ cong (SuppSub Γ σ ∪_) (DC-∪ Γ (FVSub ⟨ τ , y ⟩) (FVTm x)) ⟩
  SuppSub Γ σ ∪ SuppSub Γ ⟨ ⟨ τ , y ⟩ , x ⟩ ∎
  where
    open ≡-Reasoning

{-
sub-from-connect-Transport : (σ : Sub (suc n) l ⋆)
                           → (τ : Sub (suc m) l ⋆)
                           → (xs : VarSet (suc n))
                           → (ys : VarSet (suc m))
                           → (t : Tm (suc n))
                           → .⦃ _ : isVar t ⦄
                           → (Var (fromℕ _) [ τ ]tm ≃tm t [ σ ]tm)
                           → Truth (lookup-isVar xs t)
                           → TransportVarSet (connect-supp xs ys) (sub-from-connect σ τ) ≡ (TransportVarSet xs σ) ∪ (TransportVarSet ys τ)
sub-from-connect-Transport σ ⟨ ⟨⟩ , t ⟩ xs (ewf emp) s p q = sym (∪-right-unit (TransportVarSet xs σ))
sub-from-connect-Transport σ ⟨ ⟨⟩ , t ⟩ xs (ewt emp) s p q = begin
  empty ∪ FVTm t ≡⟨ ∪-left-unit (FVTm t) ⟩
  FVTm t ≡⟨ cong FVTm (≃tm-to-≡ p) ⟩
  FVTm (s [ σ ]tm) ≡˘⟨ TransportVarSet-tm s σ ⟩
  TransportVarSet (FVTm s) σ ≤⟨ ⊆-TransportVarSet σ (lookup-isVar-⊆ xs s q) ⟩
  TransportVarSet xs σ ∎
  where
    open PReasoning (⊆-poset _)
sub-from-connect-Transport σ ⟨ ⟨ τ , s ⟩ , t ⟩ xs (ewf (y ∷ ys)) u p q = sub-from-connect-Transport σ ⟨ τ , s ⟩ xs (y ∷ ys) u p q
sub-from-connect-Transport σ ⟨ ⟨ τ , s ⟩ , t ⟩ xs (ewt (y ∷ ys)) u p q = trans (cong (_∪ FVTm t) (sub-from-connect-Transport σ ⟨ τ , s ⟩ xs (y ∷ ys) u p q)) (∪-assoc (TransportVarSet xs σ) (TransportVarSet (y ∷ ys) ⟨ τ , s ⟩) (FVTm t))

sub-between-connect-supp : (σ : Sub (suc n) (suc l) ⋆)
                         → (τ : Sub (suc m) (suc l′) ⋆)
                         → (s : Tm (suc l))
                         → FVSub (connect-inc-left s l′ ● σ) ≡ FVSub (connect-inc-left s l′ ● σ) ∪ FVTm (Var (fromℕ m) [ connect-inc-right s l′ ● τ ]tm)
                         → FVTm s ⊆ FVSub σ
                         → FVSub (sub-between-connects σ τ s) ≡ connect-supp (FVSub σ) (FVSub τ)
sub-between-connect-supp σ τ s p q = begin
  FVSub (sub-from-connect (connect-inc-left s _ ● σ) (connect-inc-right s _ ● τ))
    ≡⟨ sub-from-connect-supp (connect-inc-left s _ ● σ) (connect-inc-right s _ ● τ) p ⟩
  FVSub (connect-inc-left s _ ● σ) ∪
    FVSub (connect-inc-right s _ ● τ)
    ≡˘⟨ cong₂ _∪_ (TransportVarSet-sub σ (connect-inc-left s _)) (TransportVarSet-sub τ (connect-inc-right s _)) ⟩
  TransportVarSet (FVSub σ) (connect-inc-left s _) ∪
    TransportVarSet (FVSub τ) (connect-inc-right s _)
    ≡⟨ connect-supp-incs (FVSub σ) s (FVSub τ) q ⟩
  connect-supp (FVSub σ) (FVSub τ) ∎
  where
    open ≡-Reasoning

sub-between-connect-Transport : (σ : Sub (suc n) (suc l) ⋆)
                              → (τ : Sub (suc m) (suc l′) ⋆)
                              → (s : Tm (suc l))
                              → (xs : VarSet (suc n))
                              → (ys : VarSet (suc m))
                              → (t : Tm (suc n))
                              → .⦃ _ : isVar t ⦄
                              → Var (fromℕ _) [ connect-inc-right s l′ ● τ ]tm ≃tm t [ connect-inc-left s l′ ● σ ]tm
                              → Truth (lookup-isVar xs t)
                              → FVTm s ⊆ TransportVarSet xs σ
                              → TransportVarSet (connect-supp xs ys) (sub-between-connects σ τ s)
                              ≡ connect-supp (TransportVarSet xs σ) (TransportVarSet ys τ)
sub-between-connect-Transport {l = l} {l′ = l′} σ τ s xs ys t p q r = begin
  TransportVarSet (connect-supp xs ys) (sub-between-connects σ τ s)
    ≡⟨ sub-from-connect-Transport (connect-inc-left s l′ ● σ) (connect-inc-right s l′ ● τ) xs ys t p q ⟩
  TransportVarSet xs (connect-inc-left s l′ ● σ)
  ∪ TransportVarSet ys (connect-inc-right s l′ ● τ)
    ≡⟨ cong₂ _∪_ (TransportVarSet-comp xs (connect-inc-left s l′) σ) (TransportVarSet-comp ys (connect-inc-right s l′) τ) ⟩
  TransportVarSet (TransportVarSet xs σ) (connect-inc-left s l′)
  ∪ TransportVarSet (TransportVarSet ys τ) (connect-inc-right s l′)
    ≡⟨ connect-supp-incs (TransportVarSet xs σ) s (TransportVarSet ys τ) r ⟩
  connect-supp (TransportVarSet xs σ) (TransportVarSet ys τ) ∎
  where
    open ≡-Reasoning

sub-between-connect-susps-supp : (σ : Sub (suc n) (suc l) ⋆)
                               → (τ : Sub (suc m) (suc l′) ⋆)
                               → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                               → FVSub (sub-between-connect-susps σ τ) ≡ connect-supp (suspSupp (FVSub σ)) (FVSub τ)
sub-between-connect-susps-supp {n = n} {l = l} {m = m} {l′ = l′} σ τ p = trans (sub-between-connect-supp (susp-sub σ) τ get-snd lem2 l1) (cong (λ - → connect-supp - (FVSub τ)) (suspSuppSub σ))
  where
    l1 : FVTm get-snd ⊆ FVSub (susp-sub σ)
    l1 = begin
      FVTm get-snd
        ≤⟨ suspSuppSnd (FVSub σ) ⟩
      suspSupp (FVSub σ)
        ≡˘⟨ suspSuppSub σ ⟩
      FVSub (susp-sub σ) ∎
      where
        open PReasoning (⊆-poset _)

    lem : Var (fromℕ m) [ connect-susp-inc-right l l′ ● τ ]tm ≃tm get-snd [ connect-susp-inc-left l l′ ]tm
    lem = begin
      < Var (fromℕ m) [ connect-susp-inc-right l l′ ● τ ]tm >tm
        ≈⟨ assoc-tm (connect-susp-inc-right l l′) τ (Var (fromℕ m)) ⟩
      < (Var (fromℕ m) [ τ ]tm) [ connect-susp-inc-right l l′ ]tm >tm
        ≈⟨ sub-action-≃-tm p refl≃s ⟩
      < Var (fromℕ l′) [ connect-susp-inc-right l l′ ]tm >tm
        ≈˘⟨ connect-inc-fst-var get-snd l′ ⟩
      < get-snd [ connect-susp-inc-left l l′ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    open ≡-Reasoning
    lem2 : FVSub (connect-susp-inc-left l l′ ● susp-sub σ) ≡
             FVSub (connect-susp-inc-left l l′ ● susp-sub σ) ∪
             FVTm (Var (fromℕ m) [ connect-inc-right get-snd l′ ● τ ]tm)
    lem2 = begin
      FVSub (connect-susp-inc-left l l′ ● susp-sub σ)
        ≡˘⟨ TransportVarSet-sub (susp-sub σ) (connect-susp-inc-left l l′) ⟩
      TransportVarSet (FVSub (susp-sub σ)) (connect-susp-inc-left l l′)
        ≡⟨ cong (λ - → TransportVarSet - (connect-susp-inc-left l l′)) (trans (suspSuppSub σ) (sym (trans (cong (_∪ trueAt (inject₁ (fromℕ (suc l)))) (suspSuppSub σ)) (sym (suspSuppSnd (FVSub σ)))))) ⟩
      TransportVarSet (FVSub (susp-sub σ) ∪ FVTm get-snd)
        (connect-susp-inc-left l l′)
        ≡⟨ TransportVarSet-∪ (FVSub (susp-sub σ)) (FVTm get-snd) (connect-susp-inc-left l l′) ⟩
      TransportVarSet (FVSub (susp-sub σ)) (connect-susp-inc-left l l′) ∪
        TransportVarSet (FVTm get-snd) (connect-susp-inc-left l l′)
        ≡⟨ cong₂ _∪_ (TransportVarSet-sub (susp-sub σ) (connect-susp-inc-left l l′)) (TransportVarSet-tm get-snd (connect-susp-inc-left l l′)) ⟩
      FVSub (connect-susp-inc-left l l′ ● susp-sub σ) ∪
        FVTm (get-snd [ connect-susp-inc-left l l′ ]tm)
        ≡˘⟨ cong (FVSub (connect-susp-inc-left l l′ ● susp-sub σ) ∪_) (cong FVTm (≃tm-to-≡ lem)) ⟩
      FVSub (connect-susp-inc-left l l′ ● susp-sub σ) ∪
        FVTm (Var (fromℕ m) [ connect-inc-right get-snd l′ ● τ ]tm) ∎

sub-between-connect-susps-Transport : (σ : Sub (suc n) (suc l) ⋆)
                                    → (τ : Sub (suc m) (suc l′) ⋆)
                                    → (xs : VarSet (suc n))
                                    → (ys : VarSet (suc m))
                                    → Var (fromℕ _) [ τ ]tm ≃tm Var (fromℕ l′)
                                    -- → Var (fromℕ _) [ connect-inc-right s l′ ● τ ]tm ≃tm get-snd [ connect-susp-inc-left s l′ ● σ ]tm
                                    -- → Truth (lookup-isVar xs t)
                                    -- → FVTm s ⊆ TransportVarSet xs σ
                                    → TransportVarSet (connect-supp (suspSupp xs) ys) (sub-between-connect-susps σ τ)
                                    ≡ connect-supp (suspSupp (TransportVarSet xs σ)) (TransportVarSet ys τ)
sub-between-connect-susps-Transport σ τ xs ys p = begin
  TransportVarSet (connect-supp (suspSupp xs) ys)
    (sub-between-connect-susps σ τ)
    ≡⟨ sub-between-connect-Transport (susp-sub σ) τ get-snd (suspSupp xs) ys get-snd l1 (suspSuppSndTruth xs) l2 ⟩
  connect-supp (TransportVarSet (suspSupp xs) (susp-sub σ))
    (TransportVarSet ys τ)
    ≡⟨ cong (λ - → connect-supp - (TransportVarSet ys τ)) (TransportVarSet-susp xs σ) ⟩
  connect-supp (suspSupp (TransportVarSet xs σ))
    (TransportVarSet ys τ) ∎
  where
    l1 : Var (fromℕ _) [ connect-inc-right get-snd _ ● τ ]tm
     ≃tm get-snd [ connect-inc-left get-snd _ ● susp-sub σ ]tm
    l1 = begin
      < Var (fromℕ _) [ connect-inc-right get-snd _ ● τ ]tm >tm
        ≈⟨ assoc-tm (connect-inc-right get-snd _) τ (Var (fromℕ _)) ⟩
      < (Var (fromℕ _) [ τ ]tm) [ connect-inc-right get-snd _ ]tm >tm
        ≈⟨ sub-action-≃-tm p refl≃s ⟩
      < Var (fromℕ _) [ connect-inc-right get-snd _ ]tm >tm
        ≈˘⟨ connect-inc-fst-var get-snd _ ⟩
      < get-snd [ connect-inc-left get-snd _ ]tm >tm
        ≈⟨ sub-action-≃-tm (susp-sub-preserve-get-snd σ) refl≃s ⟩
      < get-snd [ susp-sub σ ]tm [ connect-inc-left get-snd _ ]tm >tm
        ≈˘⟨ assoc-tm (connect-inc-left get-snd _) (susp-sub σ) get-snd ⟩
      < get-snd [ connect-inc-left get-snd _ ● susp-sub σ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : FVTm get-snd ⊆ TransportVarSet (suspSupp xs) (susp-sub σ)
    l2 = begin
      FVTm get-snd
        ≤⟨ suspSuppSnd (TransportVarSet xs σ) ⟩
      suspSupp (TransportVarSet xs σ)
        ≡˘⟨ TransportVarSet-susp xs σ ⟩
      TransportVarSet (suspSupp xs) (susp-sub σ) ∎
      where
        open PReasoning (⊆-poset _)

    open ≡-Reasoning

connect-supp-unit-left : (xs : VarSet (suc n))
                       → Truth (lookup-isVar xs (Var (fromℕ _)))
                       → connect-supp (full {1}) xs ≡ᵖ xs
connect-supp-unit-left (ewt emp) p = P.refl refl
connect-supp-unit-left (ewf (y ∷ xs)) p = refl P.∷ connect-supp-unit-left (y ∷ xs) p
connect-supp-unit-left (ewt (y ∷ xs)) p = refl P.∷ connect-supp-unit-left (y ∷ xs) p

connect-supp-fst : (xs : VarSet (suc n)) → (ys : VarSet (suc m)) → Truth (lookup-isVar xs (Var (fromℕ _))) → Truth (lookup-isVar (connect-supp xs ys) (Var (fromℕ _)))
connect-supp-fst xs (x ∷ emp) p = p
connect-supp-fst xs (x ∷ y ∷ ys) p = connect-supp-fst xs (y ∷ ys) p

connect-supp-assoc : (xs : VarSet (suc n)) → (ys : VarSet (suc m)) → (zs : VarSet (suc l))
                   → connect-supp (connect-supp xs ys) zs ≡ᵖ connect-supp xs (connect-supp ys zs)
connect-supp-assoc xs ys (x ∷ emp) = P.refl refl
connect-supp-assoc xs (x′ ∷ ys) (x ∷ y ∷ emp) = P.refl refl
connect-supp-assoc xs (x′ ∷ ys) (x ∷ y ∷ z ∷ zs) = refl P.∷ connect-supp-assoc xs (x′ ∷ ys) (y ∷ z ∷ zs)

connect-supp-≡ᵖ : {xs : VarSet (suc n)} → {xs′ : VarSet (suc n′)} → {ys : VarSet (suc m)} → {ys′ : VarSet (suc m′)} → xs ≡ᵖ xs′ → ys ≡ᵖ ys′ → connect-supp xs ys ≡ᵖ connect-supp xs′ ys′
connect-supp-≡ᵖ p (x∼y P.∷ P.[]) = p
connect-supp-≡ᵖ p (x∼y P.∷ z P.∷ q) = x∼y Pointwise.∷ (connect-supp-≡ᵖ p (z P.∷ q))
-}

connect-susp-supp-fst-var : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → lookup (connect-susp-supp xs ys) (fromℕ _) ≡ lookup xs (fromℕ _)
connect-susp-supp-fst-var {m = zero} xs (ewf ys) = refl
connect-susp-supp-fst-var {n} {m = zero} xs (ewt ys) = begin
  lookup (xs ∪ FVTm get-snd) (fromℕ _)
    ≡⟨ lookup-∪ xs (FVTm (get-snd {n = (suc n)})) (fromℕ _) ⟩
  lookup xs (fromℕ _) ∨ lookup (FVTm (get-snd {n = (suc n)})) (fromℕ _)
    ≡⟨ cong (lookup xs (fromℕ _) ∨_) (lookup-fst-var-snd (suc n)) ⟩
  lookup xs (fromℕ _) ∨ false
    ≡⟨ ∨-identityʳ (lookup xs (fromℕ _)) ⟩
  lookup xs (fromℕ _) ∎
  where
    open ≡-Reasoning
connect-susp-supp-fst-var {m = suc m} xs (y ∷ ys) = connect-susp-supp-fst-var xs ys

connect-susp-supp-snd-var : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → lookup (connect-susp-supp xs ys) (raise (suc m) (inject₁ (fromℕ _))) ≡ lookup xs (inject₁ (fromℕ _)) ∨ lookup ys (fromℕ _)
connect-susp-supp-snd-var {m = zero} xs (ewf ys) = sym (∨-identityʳ (lookup xs (inject₁ (fromℕ (suc _)))))
connect-susp-supp-snd-var {n} {m = zero} xs (ewt ys) = begin
  lookup (xs ∪ trueAt (inject₁ (fromℕ (suc n))))
      (inject₁ (fromℕ (suc n)))
    ≡⟨ lookup-∪ xs (trueAt (inject₁ (fromℕ (suc n)))) (inject₁ (fromℕ (suc n))) ⟩
  lookup xs (inject₁ (fromℕ (suc n))) ∨
    lookup (trueAt (inject₁ (fromℕ (suc n)))) (inject₁ (fromℕ (suc n)))
    ≡⟨ cong (lookup xs (inject₁ (fromℕ (suc n))) ∨_) (lookup-trueAt (inject₁ (fromℕ (suc n)))) ⟩
  lookup xs (inject₁ (fromℕ (suc n))) ∨ true ∎
  where
    open ≡-Reasoning
connect-susp-supp-snd-var {m = suc m} xs (x ∷ ys) = connect-susp-supp-snd-var xs ys

connect-susp-supp-non-empty-left : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → Truth (varset-non-empty xs) → Truth (varset-non-empty (connect-susp-supp xs ys))
connect-susp-supp-non-empty-left {m = zero} xs (ewf ys) t = t
connect-susp-supp-non-empty-left {n} {m = zero} xs (ewt ys) t = ∪-non-empty-right xs (FVTm get-snd) (trueAt-non-empty (inject₁ (fromℕ n)))
connect-susp-supp-non-empty-left {m = suc m} xs (ewf ys) t = connect-susp-supp-non-empty-left xs ys t
connect-susp-supp-non-empty-left {m = suc m} xs (ewt ys) t = tt

connect-susp-supp-non-empty-right : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → Truth (varset-non-empty ys) → Truth (varset-non-empty (connect-susp-supp xs ys))
connect-susp-supp-non-empty-right {m = zero} xs (ewf emp) ()
connect-susp-supp-non-empty-right {n} {m = zero} xs (ewt ys) t = ∪-non-empty-right xs (FVTm get-snd) (trueAt-non-empty (inject₁ (fromℕ n)))
connect-susp-supp-non-empty-right {m = suc m} xs (ewf ys) t = connect-susp-supp-non-empty-right xs ys t
connect-susp-supp-non-empty-right {m = suc m} xs (ewt ys) t = tt

connect-susp-supp-proj-right : (xs xs′ : VarSet (3 + n)) → (ys ys′ : VarSet (suc m)) → connect-susp-supp xs ys ≡ connect-susp-supp xs′ ys′ → trueAt (fromℕ _) ∪ ys ≡ trueAt (fromℕ _) ∪ ys′
connect-susp-supp-proj-right {m = zero} xs xs′ (y ∷ emp) (y′ ∷ emp) p = refl
connect-susp-supp-proj-right {m = suc m} xs xs′ (y ∷ ys) (y′ ∷ ys′) p = cong₂ _∷_ (cong head p) (connect-susp-supp-proj-right xs xs′ ys ys′ (cong tail p))

connect-susp-supp-proj-left : (xs xs′ : VarSet (suc n)) → (ys ys′ : VarSet (suc m)) → connect-susp-supp (suspSupp xs) ys ≡ connect-susp-supp (suspSupp xs′) ys′ → xs ≡ xs′
connect-susp-supp-proj-left {m = zero} xs xs′ (y ∷ emp) (y′ ∷ emp) p = suspSupp-reflect (begin
  suspSupp xs
    ≡˘⟨ connect-susp-supp-base xs y ⟩
  connect-susp-supp (suspSupp xs) (y ∷ emp)
    ≡⟨ p ⟩
  connect-susp-supp (suspSupp xs′) (y′ ∷ emp)
    ≡⟨ connect-susp-supp-base xs′ y′ ⟩
  suspSupp xs′ ∎)
  where
    open ≡-Reasoning
connect-susp-supp-proj-left {m = suc m} xs xs′ (y ∷ ys) (y′ ∷ ys′) p = connect-susp-supp-proj-left xs xs′ ys ys′ (cong tail p)

connect-susp-supp-⊥ : (n : ℕ) → (xs ys : VarSet (3 + n)) → Truth (not (lookup-isVar xs get-snd)) → Truth (not (lookup-isVar ys get-snd)) → connect-susp-supp xs (ewf emp) ≡ connect-susp-supp ys (ewt emp) → ⊥
connect-susp-supp-⊥ n xs ys a b p = absurd (begin
  true
    ≡˘⟨ ∨-zeroʳ (lookup-isVar ys get-snd) ⟩
  lookup-isVar ys get-snd ∨ true
    ≡˘⟨ cong (lookup-isVar ys get-snd ∨_) (lookup-trueAt (inject₁ (fromℕ (suc n)))) ⟩
  lookup-isVar ys get-snd ∨ lookup (trueAt (inject₁ (fromℕ (suc n)))) (inject₁ (fromℕ (suc n)))
    ≡˘⟨ lookup-∪ ys (FVTm get-snd) (inject₁ (fromℕ (suc n))) ⟩
  lookup (connect-susp-supp ys (ewt emp)) (inject₁ (fromℕ (suc n)))
    ≡˘⟨ cong (λ - → lookup - (inject₁ (fromℕ _))) p ⟩
  lookup (connect-susp-supp xs (ewf emp)) (inject₁ (fromℕ (suc n)))
    ≡⟨ Truth-not-prop a ⟩
  false ∎)
  where
    open ≡-Reasoning

connect-supp-proj-right-emp : (n : ℕ) → (xs xs′ : VarSet (3 + n)) → Truth (not (lookup-isVar xs get-snd)) → Truth (not (lookup-isVar xs′ get-snd)) → (ys ys′ : VarSet (suc m)) → connect-susp-supp xs ys ≡ connect-susp-supp xs′ ys′ → ys ≡ ys′
connect-supp-proj-right-emp {m = zero} n xs xs′ a b (ewf emp) (ewf emp) p = refl
connect-supp-proj-right-emp {m = zero} n xs xs′ a b (ewf emp) (ewt emp) p = ⊥-elim (connect-susp-supp-⊥ n xs xs′ a b p)
connect-supp-proj-right-emp {m = zero} n xs xs′ a b (ewt emp) (ewf emp) p = ⊥-elim (connect-susp-supp-⊥ n xs′ xs b a (sym p))
connect-supp-proj-right-emp {m = zero} n xs xs′ a b (ewt emp) (ewt emp) p = refl
connect-supp-proj-right-emp {m = suc m} n xs xs′ a b (y ∷ ys) (y′ ∷ ys′) p = cong₂ _∷_ (cong head p) (connect-supp-proj-right-emp n xs xs′ a b ys ys′ (cong tail p))

connect-susp-supp-trueAt-lem : (xs : VarSet (suc n)) → (ys : VarSet (suc m)) → trueAt (fromℕ _) ∪ (connect-susp-supp (suspSupp xs) ys) ≡ connect-susp-supp (suspSupp xs) ys
connect-susp-supp-trueAt-lem {m = m} xs ys = begin
  trueAt (fromℕ _) ∪ connect-susp-supp (suspSupp xs) ys
    ≡⟨ ∪-comm (trueAt (fromℕ _)) (connect-susp-supp (suspSupp xs) ys) ⟩
  connect-susp-supp (suspSupp xs) ys ∪ trueAt (fromℕ (m + (2 + _)))
    ≡˘⟨ lookup-isVar-⊆ (connect-susp-supp (suspSupp xs) ys) (Var (fromℕ _)) (subst Truth (sym (connect-susp-supp-fst-var (suspSupp xs) ys)) (suspSuppFstTruth xs)) ⟩
  connect-susp-supp (suspSupp xs) ys ∎
  where
    open ≡-Reasoning

connect-susp-supp-trueAt-lem′ : (n : ℕ) → (ys : VarSet (suc m)) → trueAt (fromℕ _) ∪ (connect-susp-supp (empty {n = 3 + n}) ys) ≡ connect-susp-supp (trueAt (fromℕ _)) ys
connect-susp-supp-trueAt-lem′ {m = m} n ys = begin
  trueAt (fromℕ _) ∪ connect-susp-supp empty ys
    ≡˘⟨ cong (_∪ connect-susp-supp empty ys) (connect-supp-fst get-snd m) ⟩
  connect-susp-supp (trueAt (fromℕ _)) empty ∪
    connect-susp-supp empty ys
    ≡˘⟨ connect-supp-∪ (trueAt (fromℕ _)) empty empty ys get-snd ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc n))) ∪ empty) (empty ∪ ys)
    ≡⟨ cong₂ connect-susp-supp (∪-right-unit (trueAt (fromℕ _))) (∪-left-unit ys) ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc n)))) ys ∎
  where
    open ≡-Reasoning

connect-susp-supp-susp-lem : (ys : VarSet (suc m)) → (xs : VarSet (3 + n)) → trueAt (raise (suc m) (inject₁ (fromℕ _))) ∪ (trueAt (fromℕ _) ∪ (connect-susp-supp xs ys)) ≡ connect-susp-supp (xs ∪ suspSupp empty) ys
connect-susp-supp-susp-lem {m = zero} {n = zero} (ewf emp) (x ∷ y ∷ z ∷ emp) = sym (cong₃ (λ a b c → a ∷ b ∷ c ∷ emp) (∨-identityʳ x) (∨-zeroʳ y) (∨-zeroʳ z))
connect-susp-supp-susp-lem {m = zero} {n = suc n} (ewf emp) (x ∷ xs) = cong₂ _∷_ (sym (∨-identityʳ x)) (connect-susp-supp-susp-lem (ewf emp) xs)
connect-susp-supp-susp-lem {m = zero} {n = zero} (ewt emp) (x ∷ y ∷ z ∷ emp) = sym (cong₃ (λ a b c → a ∷ b ∷ c ∷ emp) (∨-identityʳ (x ∨ false)) (∨-zeroʳ (y ∨ true)) (cong (_∨ false) (∨-zeroʳ z)))
connect-susp-supp-susp-lem {m = zero} {n = suc n} (ewt emp) (x ∷ xs) = cong₂ _∷_ (sym (∨-identityʳ (x ∨ false))) (connect-susp-supp-susp-lem (ewt emp) xs)
connect-susp-supp-susp-lem {m = suc m} {n = n} (y ∷ ys) xs = cong (y ∷_) (connect-susp-supp-susp-lem ys xs)
