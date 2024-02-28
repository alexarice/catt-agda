module Catt.Wedge.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Catt.Wedge
open import Catt.Wedge.Pasting
open import Catt.Wedge.Properties
open import Catt.Tree

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support

open import Tactic.MonoidSolver

wedge-supp : VarSet (suc n) → (t : Tm (suc n)) → VarSet (suc m) → VarSet (suc (m + n))
wedge-supp {m = zero} xs t (ewf ys) = xs
wedge-supp {m = zero} xs t (ewt ys) = xs ∪ FVTm t
wedge-supp {m = suc m} xs t (x ∷ ys) = x ∷ wedge-supp xs t ys

wedge-susp-supp : VarSet (3 + n) → VarSet (suc m) → VarSet (suc (m + (2 + n)))
wedge-susp-supp xs ys = wedge-supp xs get-snd ys

wedge-supp-empty : (n : ℕ) → (t : Tm (suc n)) → (m : ℕ) → wedge-supp {n = n} {m = m} empty t empty ≡ empty
wedge-supp-empty n t zero = refl
wedge-supp-empty n t (suc m) = cong ewf (wedge-supp-empty n t m)

wedge-susp-supp-base : (xs : VarSet (suc n)) → wedge-susp-supp (suspSupp xs) (ewt emp) ≡ suspSupp xs
wedge-susp-supp-base xs = sym (lookup-isVar-⊆ (suspSupp xs) get-snd (suspSuppSndTruth xs))

VarSet-NonEmpty-Special : (xs : VarSet n) → Set
VarSet-NonEmpty-Special {zero} xs = ⊥
VarSet-NonEmpty-Special {suc zero} xs = ⊥
VarSet-NonEmpty-Special {suc (suc n)} (ewf xs) = VarSet-NonEmpty-Special xs
VarSet-NonEmpty-Special {suc (suc n)} (ewt xs) = ⊤

wedge-drop : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → .⦃ VarSet-NonEmpty-Special ys ⦄ → wedge-susp-supp xs (drop ys) ≡ drop (wedge-susp-supp (xs) ys)
wedge-drop xs (ewf (y ∷ ys)) = cong ewf (wedge-drop xs (y ∷ ys))
wedge-drop xs (ewt (y ∷ ys)) = refl

pdb-bd-supp-non-empty-special : (n : ℕ) → (Γ : Ctx (suc m)) → .⦃ pdb : Γ ⊢pdb ⦄ → (b : Bool) → .⦃ NonZero m ⦄ → VarSet-NonEmpty-Special (pdb-bd-supp (suc n) Γ b)
pdb-bd-supp-non-empty-special n (∅ , B , A) ⦃ pdb ⦄ b = ⊥-elim (pdb-odd-length pdb)
pdb-bd-supp-non-empty-special n (Γ , C , B , A) b with <-cmp (suc n) (ty-dim B) | b
... | tri< a ¬b ¬c | b = pdb-bd-supp-non-empty-special n (Γ , C) ⦃ pdb-prefix it ⦄ b ⦃ focus-ty-dim-to-non-empty (pdb-prefix it) (≤-trans (≤-trans (s≤s z≤n) a) (≤-reflexive (ty-dim-≃ (pdb-proj₁ it)))) ⦄
... | tri≈ ¬a b₁ ¬c | false = pdb-bd-supp-non-empty-special n (Γ , C) ⦃ pdb-prefix it ⦄ false ⦃ focus-ty-dim-to-non-empty (pdb-prefix it) (≤-trans (≤-trans (s≤s z≤n) (≤-reflexive b₁)) (≤-reflexive (ty-dim-≃ (pdb-proj₁ it )))) ⦄
... | tri≈ ¬a b₁ ¬c | true = tt
... | tri> ¬a ¬b c | b = tt

wedge-susp-pdb-bd-compat : (n : ℕ)
                      → (Γ : Ctx (suc m))
                      → .⦃ pd : Γ ⊢pd ⦄
                      → (Δ : Ctx (suc l))
                      → .⦃ pdb : Δ ⊢pdb ⦄
                      → (b : Bool)
                      → wedge-susp-supp (suspSupp (pd-bd-supp n Γ b)) (pdb-bd-supp (suc n) Δ b) ≡ pdb-bd-supp (suc n) (wedge-susp Γ Δ) ⦃ wedge-susp-pdb pd pdb ⦄ b
wedge-susp-pdb-bd-compat n Γ ⦃ pd ⦄ (∅ , A) b = begin
  wedge-susp-supp (suspSupp (pd-bd-supp n Γ b)) (ewt emp)
    ≡⟨ wedge-susp-supp-base (pd-bd-supp n Γ b) ⟩
  suspSupp (pd-bd-supp n Γ b)
    ≡⟨ susp-pd-bd-compat n Γ b ⟩
  pd-bd-supp (suc n) (susp-ctx Γ) ⦃ susp-pd it ⦄ b ∎
  where
    open ≡-Reasoning

wedge-susp-pdb-bd-compat n Γ (∅ , B , A) b = ⊥-elim (pdb-odd-length it)
wedge-susp-pdb-bd-compat {m = m} n Γ (Δ , C , B , A) b rewrite sym (sub-dim (wedge-susp-inc-right m _) B) with <-cmp (suc n) (ty-dim B) | b
... | tri< a ¬b ¬c | b = cong ewf (cong ewf (wedge-susp-pdb-bd-compat n Γ (Δ , C) ⦃ pdb-prefix it ⦄ b))
... | tri≈ ¬a b₁ ¬c | false = cong ewf (cong ewf (wedge-susp-pdb-bd-compat n Γ (Δ , C) ⦃ pdb-prefix it ⦄ false))
... | tri≈ ¬a b₁ ¬c | true
  = cong ewf (cong ewt (trans (wedge-drop (suspSupp (pd-bd-supp n Γ true))
                                          (pdb-bd-supp (suc n) (Δ , C) ⦃ pdb-prefix it ⦄ true)
                                          ⦃ pdb-bd-supp-non-empty-special n (Δ , C) ⦃ pdb-prefix it ⦄ true
                                                                          ⦃ focus-ty-dim-to-non-empty (pdb-prefix it) (≤-trans (≤-trans (s≤s z≤n) (≤-reflexive b₁)) (≤-reflexive (ty-dim-≃ (pdb-proj₁ {Γ = Δ , C} it)))) ⦄ ⦄)
                              (cong drop (wedge-susp-pdb-bd-compat n Γ (Δ , C) ⦃ pdb-prefix it ⦄ true))))
... | tri> ¬a ¬b c | b = cong ewt (cong ewt (wedge-susp-pdb-bd-compat n Γ (Δ , C) ⦃ pdb-prefix it ⦄ b))

wedge-susp-pd-bd-compat : (n : ℕ)
                      → (Γ : Ctx (suc m))
                      → .⦃ pd : Γ ⊢pd ⦄
                      → (Δ : Ctx (suc l))
                      → .⦃ pd2 : Δ ⊢pd ⦄
                      → (b : Bool)
                      → wedge-susp-supp (suspSupp (pd-bd-supp n Γ b)) (pd-bd-supp (suc n) Δ b) ≡ pd-bd-supp (suc n) (wedge-susp Γ Δ) ⦃ wedge-susp-pd pd pd2 ⦄ b
wedge-susp-pd-bd-compat n Γ ⦃ pd ⦄ Δ ⦃ pd2 ⦄ b = wedge-susp-pdb-bd-compat n Γ Δ ⦃ pd-to-pdb pd2 ⦄ b

wedge-supp-full : ∀ n (t : Tm (suc n)) m → wedge-supp {n} {m} full t full ≡ full
wedge-supp-full n t zero = ∪-left-zero (FVTm t)
wedge-supp-full n t (suc m) = cong ewt (wedge-supp-full n t m)

wedge-supp-inc-left : (xs : VarSet (suc n)) → (t : Tm (suc n)) → (m : ℕ) → TransportVarSet xs (wedge-inc-left t m) ≡ wedge-supp xs t empty
wedge-supp-inc-left xs t zero = TransportVarSet-id xs
wedge-supp-inc-left xs t (suc m) = begin
  TransportVarSet xs (lift-sub (wedge-inc-left t m))
    ≡⟨ TransportVarSet-lift xs (wedge-inc-left t m) ⟩
  ewf (TransportVarSet xs (wedge-inc-left t m))
    ≡⟨ cong ewf (wedge-supp-inc-left xs t m) ⟩
  ewf (wedge-supp xs t empty) ∎
  where
    open ≡-Reasoning

wedge-supp-inc-right : (t : Tm (suc n)) → (ys : VarSet (suc m)) → TransportVarSet ys (wedge-inc-right t m) ≡ wedge-supp empty t ys
wedge-supp-inc-right {m = zero} t (ewf ys) = refl
wedge-supp-inc-right {m = zero} t (ewt ys) = refl
wedge-supp-inc-right {m = suc m} t (ewf ys) = begin
  TransportVarSet ys (lift-sub (wedge-inc-right t m))
    ≡⟨ TransportVarSet-lift ys (wedge-inc-right t m) ⟩
  ewf (TransportVarSet ys (wedge-inc-right t m))
    ≡⟨ cong ewf (wedge-supp-inc-right t ys) ⟩
  ewf (wedge-supp empty t ys) ∎
  where
    open ≡-Reasoning
wedge-supp-inc-right {m = suc m} t (ewt ys) = begin
  TransportVarSet ys (lift-sub (wedge-inc-right t m)) ∪ ewt empty
    ≡⟨ cong (_∪ ewt empty) (TransportVarSet-lift ys (wedge-inc-right t m)) ⟩
  ewt (TransportVarSet ys (wedge-inc-right t m) ∪ empty)
    ≡⟨ cong ewt (∪-right-unit (TransportVarSet ys (wedge-inc-right t m))) ⟩
  ewt (TransportVarSet ys (wedge-inc-right t m))
    ≡⟨ cong ewt (wedge-supp-inc-right t ys) ⟩
  ewt (wedge-supp empty t ys) ∎
  where
    open ≡-Reasoning

wedge-supp-fst : (t : Tm (suc n)) → (m : ℕ) → wedge-supp (trueAt (fromℕ n)) t (empty {n = suc m}) ≡ trueAt (fromℕ (m + n))
wedge-supp-fst t zero = refl
wedge-supp-fst t (suc m) = cong ewf (wedge-supp-fst t m)

wedge-supp-∪ : (xs xs′ : VarSet (suc n)) → (ys ys′ : VarSet (suc m)) → (t : Tm (suc n)) → wedge-supp xs t ys ∪ wedge-supp xs′ t ys′ ≡ wedge-supp (xs ∪ xs′) t (ys ∪ ys′)
wedge-supp-∪ {m = zero} xs xs′ (ewf ys) (ewf ys′) t = refl
wedge-supp-∪ {n = n} {m = zero} xs xs′ (ewf ys) (ewt ys′) t = solve (∪-monoid {n = suc n})
wedge-supp-∪ {n = n} {m = zero} xs xs′ (ewt ys) (ewf ys′) t = begin
  xs ∪ FVTm t ∪ xs′
    ≡⟨ solve (∪-monoid {n = suc n}) ⟩
  xs ∪ (FVTm t ∪ xs′)
    ≡⟨ cong (xs ∪_) (∪-comm (FVTm t) xs′) ⟩
  xs ∪ (xs′ ∪ FVTm t)
    ≡⟨ solve (∪-monoid {n = suc n}) ⟩
  xs ∪ xs′ ∪ FVTm t ∎
  where
    open ≡-Reasoning
wedge-supp-∪ {n = n} {m = zero} xs xs′ (ewt ys) (ewt ys′) t = begin
  xs ∪ FVTm t ∪ (xs′ ∪ FVTm t)
    ≡⟨ solve (∪-monoid {n = suc n}) ⟩
  xs ∪ (FVTm t ∪ xs′) ∪ FVTm t
    ≡⟨ cong (λ - → xs ∪ - ∪ FVTm t) (∪-comm (FVTm t) xs′) ⟩
  xs ∪ (xs′ ∪ FVTm t) ∪ FVTm t
    ≡⟨ solve (∪-monoid {n = suc n}) ⟩
  xs ∪ xs′ ∪ (FVTm t ∪ FVTm t)
    ≡⟨ cong (xs ∪ xs′ ∪_) (∪-idem (FVTm t)) ⟩
  xs ∪ xs′ ∪ FVTm t ∎
  where
    open ≡-Reasoning
wedge-supp-∪ {m = suc m} xs xs′ (y ∷ ys) (y′ ∷ ys′) t = cong ((y ∨ y′) ∷_) (wedge-supp-∪ xs xs′ ys ys′ t)

wedge-susp-supp-lem : (xs : VarSet (suc n)) → (ys : VarSet (suc m)) → wedge-susp-supp (suspSupp xs) ys ≡ wedge-susp-supp (suspSupp xs) (trueAt (fromℕ _) ∪ ys)
wedge-susp-supp-lem {m = zero} xs (ewf emp) = lookup-isVar-⊆ (suspSupp xs) get-snd (suspSuppSndTruth xs)
wedge-susp-supp-lem {m = zero} xs (ewt emp) = refl
wedge-susp-supp-lem {m = suc m} xs (y ∷ ys) = cong (y ∷_) (wedge-susp-supp-lem xs ys)

wedge-supp-DC : (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m)) → (xs : VarSet (suc n)) → (ys : VarSet (suc m))
                → DC Γ (FVTm t) ≡ FVTm t
                → DC (wedge Γ t Δ) (wedge-supp xs t ys) ≡ wedge-supp (DC Γ xs) t (DC Δ ys)
wedge-supp-DC {m = zero} Γ t (Δ , A) xs (ewf ys) p = refl
wedge-supp-DC {m = zero} Γ t (Δ , A) xs (ewt ys) p = trans (DC-∪ Γ xs (FVTm t)) (cong (DC Γ xs ∪_) p)
wedge-supp-DC {m = suc m} Γ t (Δ , A) xs (ewf ys) p = cong ewf (wedge-supp-DC Γ t Δ xs ys p)
wedge-supp-DC {m = suc m} Γ t (Δ , A) xs (ewt ys) p = cong ewt (begin
  DC (wedge Γ t Δ) (wedge-supp xs t ys ∪ FVTy (A [ wedge-inc-right t m ]ty))
    ≡˘⟨ cong (λ - → DC (wedge Γ t Δ) (wedge-supp xs t ys ∪ -)) (TransportVarSet-ty A (wedge-inc-right t m)) ⟩
  DC (wedge Γ t Δ) (wedge-supp xs t ys ∪ TransportVarSet (FVTy A) (wedge-inc-right t m))
    ≡⟨ cong (λ - → DC (wedge Γ t Δ) (wedge-supp xs t ys ∪ -)) (wedge-supp-inc-right t (FVTy A)) ⟩
  DC (wedge Γ t Δ) (wedge-supp xs t ys ∪ wedge-supp empty t (FVTy A))
    ≡⟨ cong (DC (wedge Γ t Δ)) (wedge-supp-∪ xs empty ys (FVTy A) t) ⟩
  DC (wedge Γ t Δ) (wedge-supp (xs ∪ empty) t (ys ∪ FVTy A))
    ≡⟨ cong (λ - → DC (wedge Γ t Δ) (wedge-supp - t (ys ∪ FVTy A))) (∪-right-unit xs) ⟩
  DC (wedge Γ t Δ) (wedge-supp xs t (ys ∪ FVTy A))
    ≡⟨ wedge-supp-DC Γ t Δ xs (ys ∪ FVTy A) p ⟩
  wedge-supp (DC Γ xs) t (DC Δ (ys ∪ FVTy A)) ∎)
  where
    open ≡-Reasoning

wedge-susp-supp-DC : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → DC (wedge-susp Γ Δ) (wedge-susp-supp xs ys) ≡ wedge-susp-supp (DC (susp-ctx Γ) xs) (DC Δ ys)
wedge-susp-supp-DC Γ Δ xs ys = wedge-supp-DC (susp-ctx Γ) get-snd Δ xs ys (lem Γ)
  where
    lem : (Γ : Ctx n) → DC (susp-ctx Γ) (FVTm get-snd) ≡ FVTm get-snd
    lem ∅ = refl
    lem (Γ , A) = cong ewf (lem Γ)

wedge-susp-supp-ext : (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m))
                      → wedge-susp-supp (suspSupp (SuppTm Γ t)) empty ≡ SuppTm (wedge-susp Γ Δ) (susp-tm t [ wedge-susp-inc-left n m ]tm)
wedge-susp-supp-ext {m = m} Γ t Δ = begin
  wedge-susp-supp (suspSupp (SuppTm Γ t)) empty
    ≡˘⟨ cong₂ wedge-susp-supp (suspSuppTm′ Γ t) (DC-empty Δ) ⟩
  wedge-susp-supp (SuppTm (susp-ctx Γ) (susp-tm t))
    (DC Δ empty)
    ≡˘⟨ wedge-susp-supp-DC Γ Δ ((FVTm (susp-tm t))) empty ⟩
  DC (wedge-susp Γ Δ) (wedge-susp-supp (FVTm (susp-tm t)) empty)
    ≡˘⟨ cong (DC (wedge-susp Γ Δ)) (wedge-supp-inc-left (FVTm (susp-tm t)) get-snd m) ⟩
  DC (wedge-susp Γ Δ) (TransportVarSet (FVTm (susp-tm t)) (wedge-susp-inc-left _ m))
    ≡⟨ cong (DC (wedge-susp Γ Δ)) (TransportVarSet-tm (susp-tm t) (wedge-susp-inc-left _ m)) ⟩
  SuppTm (wedge-susp Γ Δ) (susp-tm t [ wedge-susp-inc-left _ m ]tm) ∎
     where
       open ≡-Reasoning

wedge-susp-supp-shift : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → (t : Tm (suc m))
                        → wedge-susp-supp empty (SuppTm Δ t) ≡ SuppTm (wedge-susp Γ Δ) (t [ wedge-susp-inc-right n m ]tm)
wedge-susp-supp-shift Γ Δ t = begin
  wedge-susp-supp empty (SuppTm Δ t)
    ≡˘⟨ cong (λ - → wedge-susp-supp - (SuppTm Δ t)) (DC-empty (susp-ctx Γ)) ⟩
  wedge-susp-supp (DC (susp-ctx Γ) empty) (SuppTm Δ t)
    ≡˘⟨ wedge-susp-supp-DC Γ Δ empty (FVTm t) ⟩
  DC (wedge-susp Γ Δ) (wedge-susp-supp empty (FVTm t))
    ≡˘⟨ cong (DC (wedge-susp Γ Δ)) (wedge-supp-inc-right get-snd (FVTm t)) ⟩
  DC (wedge-susp Γ Δ) (TransportVarSet (FVTm t) (wedge-susp-inc-right _ _))
    ≡⟨ cong (DC (wedge-susp Γ Δ)) (TransportVarSet-tm t (wedge-susp-inc-right _ _)) ⟩
  SuppTm (wedge-susp Γ Δ) (t [ wedge-susp-inc-right _ _ ]tm) ∎
  where
    open ≡-Reasoning


sub-from-wedge-supp : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A)
                      → FVTm (Var (fromℕ _) [ τ ]tm) ⊆ FVSub σ
                      → FVSub (sub-from-wedge σ τ) ≡ FVSub σ ∪ FVSub τ
sub-from-wedge-supp {l = l} σ ⟨ ⟨ A ⟩′ , x ⟩ p = begin
  FVSub σ
    ≡⟨ p ⟩
  FVSub σ ∪ FVTm x
    ≡⟨ cong (_∪ FVTm x) (sub-type-⊆ σ) ⟩
  FVSub σ ∪ FVTy A ∪ FVTm x
    ≡⟨ ∪-assoc (FVSub σ) (FVTy A) (FVTm x) ⟩
  FVSub σ ∪ (FVTy A ∪ FVTm x) ∎
  where
    open ≡-Reasoning
sub-from-wedge-supp {l = l} σ ⟨ ⟨ τ , y ⟩ , x ⟩ p = trans (cong (_∪ FVTm x) (sub-from-wedge-supp σ ⟨ τ , y ⟩ p)) (solve (∪-monoid {l}))

sub-from-wedge-supp′ : (σ : Sub (suc n) l A) → (τ : Sub (suc m) l A)
                       → SuppTm Γ (Var (fromℕ _) [ τ ]tm) ⊆ SuppSub Γ σ
                       → SuppSub Γ (sub-from-wedge σ τ) ≡ SuppSub Γ σ ∪ SuppSub Γ τ
sub-from-wedge-supp′ {Γ = Γ} σ ⟨ ⟨ A ⟩′ , x ⟩ p = begin
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
sub-from-wedge-supp′ {Γ = Γ} σ ⟨ ⟨ τ , y ⟩ , x ⟩ p = begin
  DC Γ (FVSub (sub-from-wedge σ ⟨ τ , y ⟩) ∪ FVTm x)
    ≡⟨ DC-∪ Γ (FVSub (sub-from-wedge σ ⟨ τ , y ⟩)) (FVTm x) ⟩
  SuppSub Γ (sub-from-wedge σ ⟨ τ , y ⟩) ∪ SuppTm Γ x
    ≡⟨ cong (_∪ SuppTm Γ x) (sub-from-wedge-supp′ σ ⟨ τ , y ⟩ p) ⟩
  SuppSub Γ σ ∪ SuppSub Γ ⟨ τ , y ⟩ ∪ SuppTm Γ x
    ≡⟨ ∪-assoc (SuppSub Γ σ) (SuppSub Γ ⟨ τ , y ⟩) (SuppTm Γ x) ⟩
  SuppSub Γ σ ∪ (SuppSub Γ ⟨ τ , y ⟩ ∪ SuppTm Γ x)
    ≡˘⟨ cong (SuppSub Γ σ ∪_) (DC-∪ Γ (FVSub ⟨ τ , y ⟩) (FVTm x)) ⟩
  SuppSub Γ σ ∪ SuppSub Γ ⟨ ⟨ τ , y ⟩ , x ⟩ ∎
  where
    open ≡-Reasoning

wedge-susp-supp-fst-var : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → lookup (wedge-susp-supp xs ys) (fromℕ _) ≡ lookup xs (fromℕ _)
wedge-susp-supp-fst-var {m = zero} xs (ewf ys) = refl
wedge-susp-supp-fst-var {n} {m = zero} xs (ewt ys) = begin
  lookup (xs ∪ FVTm get-snd) (fromℕ _)
    ≡⟨ lookup-∪ xs (FVTm (get-snd {n = (suc n)})) (fromℕ _) ⟩
  lookup xs (fromℕ _) ∨ lookup (FVTm (get-snd {n = (suc n)})) (fromℕ _)
    ≡⟨ cong (lookup xs (fromℕ _) ∨_) (lookup-fst-var-snd (suc n)) ⟩
  lookup xs (fromℕ _) ∨ false
    ≡⟨ ∨-identityʳ (lookup xs (fromℕ _)) ⟩
  lookup xs (fromℕ _) ∎
  where
    open ≡-Reasoning
wedge-susp-supp-fst-var {m = suc m} xs (y ∷ ys) = wedge-susp-supp-fst-var xs ys

wedge-susp-supp-snd-var : (xs : VarSet (3 + n))
                          → (ys : VarSet (suc m))
                          → lookup (wedge-susp-supp xs ys) (suc m ↑ʳ inject₁ (fromℕ _)) ≡ lookup xs (inject₁ (fromℕ _)) ∨ lookup ys (fromℕ _)
wedge-susp-supp-snd-var {m = zero} xs (ewf ys) = sym (∨-identityʳ (lookup xs (inject₁ (fromℕ (suc _)))))
wedge-susp-supp-snd-var {n} {m = zero} xs (ewt ys) = begin
  lookup (xs ∪ trueAt (inject₁ (fromℕ (suc n))))
      (inject₁ (fromℕ (suc n)))
    ≡⟨ lookup-∪ xs (trueAt (inject₁ (fromℕ (suc n)))) (inject₁ (fromℕ (suc n))) ⟩
  lookup xs (inject₁ (fromℕ (suc n))) ∨
    lookup (trueAt (inject₁ (fromℕ (suc n)))) (inject₁ (fromℕ (suc n)))
    ≡⟨ cong (lookup xs (inject₁ (fromℕ (suc n))) ∨_) (lookup-trueAt (inject₁ (fromℕ (suc n)))) ⟩
  lookup xs (inject₁ (fromℕ (suc n))) ∨ true ∎
  where
    open ≡-Reasoning
wedge-susp-supp-snd-var {m = suc m} xs (x ∷ ys) = wedge-susp-supp-snd-var xs ys

wedge-susp-supp-non-empty-left : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → Truth (varset-non-empty xs) → Truth (varset-non-empty (wedge-susp-supp xs ys))
wedge-susp-supp-non-empty-left {m = zero} xs (ewf ys) t = t
wedge-susp-supp-non-empty-left {n} {m = zero} xs (ewt ys) t = ∪-non-empty-right xs (FVTm get-snd) (trueAt-non-empty (inject₁ (fromℕ n)))
wedge-susp-supp-non-empty-left {m = suc m} xs (ewf ys) t = wedge-susp-supp-non-empty-left xs ys t
wedge-susp-supp-non-empty-left {m = suc m} xs (ewt ys) t = tt

wedge-susp-supp-non-empty-right : (xs : VarSet (3 + n)) → (ys : VarSet (suc m)) → Truth (varset-non-empty ys) → Truth (varset-non-empty (wedge-susp-supp xs ys))
wedge-susp-supp-non-empty-right {m = zero} xs (ewf emp) ()
wedge-susp-supp-non-empty-right {n} {m = zero} xs (ewt ys) t = ∪-non-empty-right xs (FVTm get-snd) (trueAt-non-empty (inject₁ (fromℕ n)))
wedge-susp-supp-non-empty-right {m = suc m} xs (ewf ys) t = wedge-susp-supp-non-empty-right xs ys t
wedge-susp-supp-non-empty-right {m = suc m} xs (ewt ys) t = tt

wedge-susp-supp-proj-right : (xs xs′ : VarSet (3 + n)) → (ys ys′ : VarSet (suc m)) → wedge-susp-supp xs ys ≡ wedge-susp-supp xs′ ys′ → trueAt (fromℕ _) ∪ ys ≡ trueAt (fromℕ _) ∪ ys′
wedge-susp-supp-proj-right {m = zero} xs xs′ (y ∷ emp) (y′ ∷ emp) p = refl
wedge-susp-supp-proj-right {m = suc m} xs xs′ (y ∷ ys) (y′ ∷ ys′) p = cong₂ _∷_ (cong head p) (wedge-susp-supp-proj-right xs xs′ ys ys′ (cong tail p))
