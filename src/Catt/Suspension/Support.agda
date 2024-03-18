module Catt.Suspension.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Syntax.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension.Pasting

open import Catt.Support
open import Catt.Support.Properties

susp-vs : VarSet n → VarSet (2 + n)
susp-vs [] = full
susp-vs (x ∷ vs) = x ∷ susp-vs vs

VarSet-NonEmpty : (xs : VarSet n) → Set
VarSet-NonEmpty emp = ⊥
VarSet-NonEmpty (ewf xs) = VarSet-NonEmpty xs
VarSet-NonEmpty (ewt xs) = ⊤

susp-vs-drop : (xs : VarSet n) → .⦃ VarSet-NonEmpty xs ⦄ → susp-vs (drop xs) ≡ drop (susp-vs xs)
susp-vs-drop (ewf xs) = cong ewf (susp-vs-drop xs)
susp-vs-drop (ewt xs) = refl

pdb-bd-vs-non-empty : (n : ℕ) → (Γ : Ctx m) → .⦃ pdb : Γ ⊢pdb ⦄ → (b : Bool) → VarSet-NonEmpty (pdb-bd-vs n Γ b)
pdb-bd-vs-non-empty n ∅ ⦃ pdb ⦄ b = ⊥-elim (pdb-odd-length pdb)
pdb-bd-vs-non-empty n (∅ , A) b = tt
pdb-bd-vs-non-empty n (Γ , B , A) b with <-cmp n (ty-dim B) | b
... | tri< a ¬b ¬c | b = pdb-bd-vs-non-empty n Γ ⦃ pdb-prefix it ⦄ b
... | tri≈ ¬a b₁ ¬c | false = pdb-bd-vs-non-empty n Γ ⦃ pdb-prefix it ⦄ false
... | tri≈ ¬a b₁ ¬c | true = tt
... | tri> ¬a ¬b c | b = tt

susp-pdb-bd-compat : (n : ℕ)
                   → (Γ : Ctx m)
                   → .⦃ pdb : Γ ⊢pdb ⦄
                   → (b : Bool)
                   → susp-vs (pdb-bd-vs n Γ b) ≡ pdb-bd-vs (suc n) (susp-ctx Γ) ⦃ susp-pdb pdb ⦄ b
susp-pdb-bd-compat n ∅ b = ⊥-elim (pdb-odd-length it)
susp-pdb-bd-compat n (∅ , A) b = refl
susp-pdb-bd-compat n (Γ , B , A) b with  <-cmp n (ty-dim B) | <-cmp (suc n) (ty-dim (susp-ty B)) | b
... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ | b = cong ewf (cong ewf (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ b))
... | tri< a ¬b ¬c | tri≈ ¬a b₁ ¬c₁ | b = ⊥-elim (¬a (≤-<-trans a (<-≤-trans (n<1+n (ty-dim B)) (≤-reflexive (sym (susp-dim B))))))
... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c | b = ⊥-elim (¬a (≤-<-trans a (<-≤-trans (n<1+n (ty-dim B)) (≤-reflexive (sym (susp-dim B))))))
... | tri≈ ¬a b₁ ¬c | tri< a ¬b ¬c₁ | b = ⊥-elim (¬b (trans (cong suc b₁) (sym (susp-dim B))))
... | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ | false = cong ewf (cong ewf (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ false))
... | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ | true = cong ewf (cong ewt (trans (susp-vs-drop (pdb-bd-vs n Γ ⦃ pdb-prefix it ⦄ true) ⦃ pdb-bd-vs-non-empty n Γ ⦃ pdb-prefix it ⦄ true ⦄) (cong drop (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ true))))
... | tri≈ ¬a b₁ ¬c | tri> ¬a₁ ¬b c | b = ⊥-elim (¬b (trans (cong suc b₁) (sym (susp-dim B))))
... | tri> ¬a ¬b c | tri< a ¬b₁ ¬c | b = ⊥-elim (¬c (s≤s (≤-trans (≤-reflexive (susp-dim B)) c)))
... | tri> ¬a ¬b c | tri≈ ¬a₁ b₁ ¬c | b = ⊥-elim (¬c (s≤s (≤-trans (≤-reflexive (susp-dim B)) c)))
... | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ | b = cong ewt (cong ewt (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ b))

susp-pd-bd-compat : (n : ℕ)
                  → (Γ : Ctx m)
                  → .⦃ pd : Γ ⊢pd ⦄
                  → (b : Bool)
                  → susp-vs (pd-bd-vs n Γ b) ≡ pd-bd-vs (suc n) (susp-ctx Γ) ⦃ susp-pd pd ⦄ b
susp-pd-bd-compat n Γ b = susp-pdb-bd-compat n Γ ⦃ pd-to-pdb it ⦄ b

susp-vs-∪ : (vs vs′ : VarSet n) → susp-vs vs ∪ susp-vs vs′ ≡ susp-vs (vs ∪ vs′)
susp-vs-∪ emp emp = refl
susp-vs-∪ (x ∷ xs) (y ∷ ys) = cong₂ _∷_ refl (susp-vs-∪ xs ys)

susp-vs-lem : (n : ℕ) → empty ∪ ewf (trueAt (fromℕ n)) ∪ trueAt (inject₁ (fromℕ n)) ≡ susp-vs empty
susp-vs-lem zero = refl
susp-vs-lem (suc n) = cong (ewf) (susp-vs-lem n)

susp-vs-fst-Truth : (xs : VarSet n) → Truth (lookup-isVar (susp-vs xs) get-fst)
susp-vs-fst-Truth emp = tt
susp-vs-fst-Truth (x ∷ xs) = susp-vs-fst-Truth xs

susp-vs-snd-Truth : (xs : VarSet n) → Truth (lookup-isVar (susp-vs xs) get-snd)
susp-vs-snd-Truth emp = tt
susp-vs-snd-Truth (x ∷ xs) = susp-vs-snd-Truth xs

susp-vs-snd : (xs : VarSet n) → FVTm get-snd ⊆ susp-vs xs
susp-vs-snd emp = refl
susp-vs-snd (x ∷ xs) = cong₂ _∷_ (sym (∨-identityʳ x)) (susp-vs-snd xs)

susp-vs-emp-right : (xs : VarSet n) → susp-vs xs ≡ susp-vs xs ∪ susp-vs empty
susp-vs-emp-right xs = sym (trans (susp-vs-∪ xs empty) (cong susp-vs (∪-right-unit xs)))

susp-FVTy : (A : Ty n) → FVTy (susp-ty A) ≡ susp-vs (FVTy A)
susp-FVTm : (t : Tm n) → (susp-vs empty) ∪ FVTm (susp-tm t) ≡ susp-vs (FVTm t)
susp-FVSub : (σ : Sub n m ⋆) → FVSub (susp-sub σ) ≡ susp-vs (FVSub σ)
susp-FVTyTm : (A : Ty n) → (t : Tm n) → FVTy (susp-ty A) ∪ FVTm (susp-tm t) ≡ susp-vs (FVTy A ∪ FVTm t)

susp-FVTy ⋆ = susp-vs-lem _
susp-FVTy (s ─⟨ A ⟩⟶ t) = begin
  FVTy (susp-ty (s ─⟨ A ⟩⟶ t)) ≡⟨⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-FVTyTm A s) ⟩
  susp-vs (FVTy A ∪ FVTm s) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-vs-emp-right (FVTy A ∪ FVTm s)) ⟩
  susp-vs (FVTy A ∪ FVTm s) ∪ susp-vs empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (susp-vs (FVTy A ∪ FVTm s)) (susp-vs empty) (FVTm (susp-tm t)) ⟩
  susp-vs (FVTy A ∪ FVTm s) ∪
    (susp-vs empty ∪ FVTm (susp-tm t)) ≡⟨ cong (susp-vs (FVTy A ∪ FVTm s) ∪_) (susp-FVTm t) ⟩
  susp-vs (FVTy A ∪ FVTm s) ∪ susp-vs (FVTm t) ≡⟨ susp-vs-∪ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  susp-vs (FVTy (s ─⟨ A ⟩⟶ t)) ∎
  where
    open ≡-Reasoning

susp-FVTyTm A t = begin
  FVTy (susp-ty A) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-FVTy A) ⟩
  susp-vs (FVTy A) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-vs-emp-right (FVTy A)) ⟩
  susp-vs (FVTy A) ∪ susp-vs empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (susp-vs (FVTy A)) (susp-vs empty) (FVTm (susp-tm t)) ⟩
  susp-vs (FVTy A) ∪ (susp-vs empty ∪ FVTm (susp-tm t)) ≡⟨ cong (susp-vs (FVTy A) ∪_) (susp-FVTm t) ⟩
  susp-vs (FVTy A) ∪ susp-vs (FVTm t) ≡⟨ susp-vs-∪ (FVTy A) (FVTm t) ⟩
  susp-vs (FVTy A ∪ FVTm t) ∎
  where
    open ≡-Reasoning


susp-FVTm (Var i) = lem _ i
  where
    lem : (n : ℕ) → (i : Fin n) → susp-vs empty ∪ trueAt (inject₁ (inject₁ i)) ≡ susp-vs (trueAt i)
    lem (suc n) zero = cong ewt (∪-right-unit (susp-vs empty))
    lem (suc n) (suc i) = cong ewf (lem n i)
susp-FVTm (Coh Δ A σ) = trans (∪-comm (susp-vs empty) (FVTm (susp-tm (Coh Δ A σ)))) (trans (cong (_∪ susp-vs empty) (susp-FVSub σ)) (sym (susp-vs-emp-right (FVSub σ))))

susp-FVSub ⟨ A ⟩′ = susp-vs-lem _
susp-FVSub ⟨ σ , t ⟩ = begin
  FVSub (susp-sub ⟨ σ , t ⟩) ≡⟨⟩
  FVSub (susp-sub σ) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-FVSub σ) ⟩
  susp-vs (FVSub σ) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-vs-emp-right (FVSub σ)) ⟩
  susp-vs (FVSub σ) ∪ susp-vs empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (susp-vs (FVSub σ)) (susp-vs empty) (FVTm (susp-tm t)) ⟩
  susp-vs (FVSub σ) ∪ (susp-vs empty ∪ FVTm (susp-tm t)) ≡⟨ cong (susp-vs (FVSub σ) ∪_) (susp-FVTm t) ⟩
  susp-vs (FVSub σ) ∪ susp-vs (FVTm t) ≡⟨ susp-vs-∪ (FVSub σ) (FVTm t) ⟩
  susp-vs (FVSub ⟨ σ , t ⟩) ∎
  where
    open ≡-Reasoning

susp-vs-full : susp-vs (full {n}) ≡ full
susp-vs-full {zero} = refl
susp-vs-full {suc n} = cong ewt susp-vs-full

vs-sub-susp : (xs : VarSet n) → (σ : Sub n m ⋆) → susp-vs xs [ susp-sub σ ]vs ≡ susp-vs (xs [ σ ]vs)
vs-sub-susp emp ⟨ A ⟩′ = susp-vs-lem _
vs-sub-susp (ewf xs) ⟨ σ , t ⟩ = vs-sub-susp xs σ
vs-sub-susp (ewt xs) ⟨ σ , t ⟩ = begin
  susp-vs xs [ susp-sub σ ]vs ∪ FVTm (susp-tm t)
    ≡⟨ cong (_∪ FVTm (susp-tm t)) (trans (vs-sub-susp xs σ) (susp-vs-emp-right (xs [ σ ]vs))) ⟩
  susp-vs (xs [ σ ]vs) ∪ susp-vs empty ∪ FVTm (susp-tm t)
    ≡⟨ ∪-assoc (susp-vs (xs [ σ ]vs)) (susp-vs empty) (FVTm (susp-tm t)) ⟩
  susp-vs (xs [ σ ]vs) ∪ (susp-vs empty ∪ FVTm (susp-tm t))
    ≡⟨ cong (susp-vs (xs [ σ ]vs) ∪_) (susp-FVTm t) ⟩
  susp-vs (xs [ σ ]vs) ∪ susp-vs (FVTm t)
    ≡⟨ susp-vs-∪ (xs [ σ ]vs) (FVTm t) ⟩
  susp-vs (xs [ σ ]vs ∪ FVTm t) ∎
  where
    open ≡-Reasoning

susp-FVTyContainsEmpty : (A : Ty n) → susp-vs empty ⊆ FVTy (susp-ty A)
susp-FVTyContainsEmpty ⋆ = ⊆-reflexive (sym (susp-vs-lem _))
susp-FVTyContainsEmpty (s ─⟨ A ⟩⟶ t) = begin
  susp-vs empty
    ≤⟨ susp-FVTyContainsEmpty A ⟩
  FVTy (susp-ty A)
    ≤⟨ ∪-⊆-1 (FVTy (susp-ty A)) (FVTm (susp-tm s)) ⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s)
    ≤⟨ ∪-⊆-1 (FVTy (susp-ty A) ∪ FVTm (susp-tm s)) (FVTm (susp-tm t)) ⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s) ∪ FVTm (susp-tm t) ∎
  where
    open PReasoning (⊆-poset _)

susp-SuppTmContainsEmpty : (Γ : Ctx n) → (t : Tm n) → susp-vs empty ⊆ SuppTm (susp-ctx Γ) (susp-tm t)
susp-SuppTmContainsEmpty Γ t = begin
  susp-vs empty
    ≤⟨ susp-FVTyContainsEmpty (tm-to-ty Γ t) ⟩
  FVTy (susp-ty (tm-to-ty Γ t))
    ≤⟨ DC-⊆ (susp-ctx Γ) (FVTy (susp-ty (tm-to-ty Γ t))) ⟩
  SuppTy (susp-ctx Γ) (susp-ty (tm-to-ty Γ t))
    ≡⟨ cong (SuppTy (susp-ctx Γ)) (≃ty-to-≡ (tm-to-ty-susp t Γ)) ⟩
  SuppTy (susp-ctx Γ) (tm-to-ty (susp-ctx Γ) (susp-tm t))
    ≤⟨ SuppContainsType (susp-tm t) (susp-ctx Γ) ⟩
  SuppTm (susp-ctx Γ) (susp-tm t) ∎
  where
    open PReasoning (⊆-poset _)

DC-susp-vs : (Γ : Ctx n) → (xs : VarSet n) → DC (susp-ctx Γ) (susp-vs xs) ≡ susp-vs (DC Γ xs)
DC-susp-vs ∅ emp = refl
DC-susp-vs (Γ , A) (ewf xs) = cong ewf (DC-susp-vs Γ xs)
DC-susp-vs (Γ , A) (ewt xs) = cong ewt (begin
  DC (susp-ctx Γ) (susp-vs xs ∪ FVTy (susp-ty A))
    ≡⟨ cong (DC (susp-ctx Γ)) lem ⟩
  DC (susp-ctx Γ) (susp-vs (xs ∪ FVTy A))
    ≡⟨ DC-susp-vs Γ (xs ∪ FVTy A) ⟩
  susp-vs (DC Γ (xs ∪ FVTy A)) ∎)
  where
    open ≡-Reasoning
    lem : susp-vs xs ∪ FVTy (susp-ty A) ≡ susp-vs (xs ∪ FVTy A)
    lem = begin
      susp-vs xs ∪ FVTy (susp-ty A)
        ≡⟨ cong (susp-vs xs ∪_) (susp-FVTy A) ⟩
      susp-vs xs ∪ susp-vs (FVTy A)
        ≡⟨ susp-vs-∪ xs (FVTy A) ⟩
      susp-vs (xs ∪ FVTy A) ∎

susp-SuppTm : (Γ : Ctx n) → (t : Tm n) → SuppTm (susp-ctx Γ) (susp-tm t) ≡ susp-vs (SuppTm Γ t)
susp-SuppTy : (Γ : Ctx n) → (A : Ty n) → SuppTy (susp-ctx Γ) (susp-ty A) ≡ susp-vs (SuppTy Γ A)
susp-SuppSub : (Γ : Ctx n) → (σ : Sub m n ⋆) → SuppSub (susp-ctx Γ) (susp-sub σ) ≡ susp-vs (SuppSub Γ σ)

susp-SuppTm Γ (Coh Δ A σ) = susp-SuppSub Γ σ
susp-SuppTm (Γ , A) (Var 0F) = cong ewt (begin
  DC (susp-ctx Γ) (empty ∪ FVTy (susp-ty A))
    ≡⟨ cong (DC (susp-ctx Γ)) (∪-left-unit (FVTy (susp-ty A))) ⟩
  SuppTy (susp-ctx Γ) (susp-ty A)
    ≡⟨ susp-SuppTy Γ A ⟩
  susp-vs (SuppTy Γ A)
    ≡˘⟨ cong (susp-vs ∘ DC Γ) (∪-left-unit (FVTy A)) ⟩
  susp-vs (DC Γ (empty ∪ FVTy A)) ∎)
  where
    open ≡-Reasoning
susp-SuppTm (Γ , A) (Var (suc i)) = cong ewf (susp-SuppTm Γ (Var i))

susp-SuppTy Γ (s ─⟨ A ⟩⟶ t) = begin
  SuppTy (susp-ctx Γ) (susp-ty (s ─⟨ A ⟩⟶ t))
    ≡⟨ DC-∪ (susp-ctx Γ) (FVTy (susp-ty A) ∪ FVTm (susp-tm s)) (FVTm (susp-tm t)) ⟩
  DC (susp-ctx Γ) (FVTy (susp-ty A) ∪ FVTm (susp-tm s)) ∪ SuppTm (susp-ctx Γ) (susp-tm t)
    ≡⟨ cong (_∪ SuppTm (susp-ctx Γ) (susp-tm t)) (DC-∪ (susp-ctx Γ) (FVTy (susp-ty A)) (FVTm (susp-tm s))) ⟩
  SuppTy (susp-ctx Γ) (susp-ty A) ∪ SuppTm (susp-ctx Γ) (susp-tm s) ∪ SuppTm (susp-ctx Γ) (susp-tm t)
    ≡⟨ cong₃ (λ a b c → a ∪ b ∪ c) (susp-SuppTy Γ A) (susp-SuppTm Γ s) (susp-SuppTm Γ t) ⟩
  susp-vs (SuppTy Γ A) ∪ susp-vs (SuppTm Γ s) ∪ susp-vs (SuppTm Γ t)
    ≡⟨ cong (_∪ susp-vs (SuppTm Γ t)) (susp-vs-∪ (SuppTy Γ A) (SuppTm Γ s)) ⟩
  susp-vs (SuppTy Γ A ∪ SuppTm Γ s) ∪ susp-vs (SuppTm Γ t)
    ≡⟨ susp-vs-∪ (SuppTy Γ A ∪ SuppTm Γ s) (SuppTm Γ t) ⟩
  susp-vs (SuppTy Γ A ∪ SuppTm Γ s ∪ SuppTm Γ t)
    ≡˘⟨ cong (λ - → susp-vs (- ∪ SuppTm Γ t)) (DC-∪ Γ (FVTy A) (FVTm s)) ⟩
  susp-vs (DC Γ (FVTy A ∪ FVTm s) ∪ SuppTm Γ t)
    ≡˘⟨ cong susp-vs (DC-∪ Γ (FVTy A ∪ FVTm s) (FVTm t)) ⟩
  susp-vs (SuppTy Γ (s ─⟨ A ⟩⟶ t)) ∎
  where
    open ≡-Reasoning
susp-SuppTy ∅ ⋆ = refl
susp-SuppTy (Γ , A) ⋆ = cong ewf (susp-SuppTy Γ ⋆)

susp-SuppSub Γ ⟨ .⋆ ⟩′ = susp-SuppTy Γ ⋆
susp-SuppSub Γ ⟨ σ , t ⟩ = begin
  SuppSub (susp-ctx Γ) (susp-sub ⟨ σ , t ⟩)
    ≡⟨ DC-∪ (susp-ctx Γ) (FVSub (susp-sub σ)) (FVTm (susp-tm t)) ⟩
  SuppSub (susp-ctx Γ) (susp-sub σ) ∪ SuppTm (susp-ctx Γ) (susp-tm t)
    ≡⟨ cong₂ _∪_ (susp-SuppSub Γ σ) (susp-SuppTm Γ t) ⟩
  susp-vs (SuppSub Γ σ) ∪ susp-vs (SuppTm Γ t)
    ≡⟨ susp-vs-∪ (SuppSub Γ σ) (SuppTm Γ t) ⟩
  susp-vs (SuppSub Γ σ ∪ SuppTm Γ t)
    ≡˘⟨ cong susp-vs (DC-∪ Γ (FVSub σ) (FVTm t)) ⟩
  susp-vs (SuppSub Γ ⟨ σ , t ⟩) ∎
  where
    open ≡-Reasoning

susp-SuppTm-prop : (s t : Tm n) → SuppTm Γ s ≡ SuppTm Γ t → SuppTm (susp-ctx Γ) (susp-tm s) ≡ SuppTm (susp-ctx Γ) (susp-tm t)
susp-SuppTm-prop {Γ = Γ} s t p = begin
  SuppTm (susp-ctx Γ) (susp-tm s)
    ≡⟨ susp-SuppTm Γ s ⟩
  susp-vs (SuppTm Γ s)
    ≡⟨ cong susp-vs p ⟩
  susp-vs (SuppTm Γ t)
    ≡˘⟨ susp-SuppTm Γ t ⟩
  SuppTm (susp-ctx Γ) (susp-tm t) ∎
  where
    open ≡-Reasoning

susp-supp-cond : {b : Bool} → {A : Ty (suc n)} → {Γ : Ctx (suc n)} → supp-condition b A Γ → supp-condition b (susp-ty A) (susp-ctx Γ)
susp-supp-cond {b = false} {A} {Γ} sc = begin
  SuppTy (susp-ctx Γ) (susp-ty A)
    ≡⟨ susp-SuppTy Γ A ⟩
  susp-vs (SuppTy Γ A)
    ≡⟨ cong susp-vs sc ⟩
  susp-vs full
    ≡⟨ susp-vs-full ⟩
  full ∎
  where
    open ≡-Reasoning
susp-supp-cond {b = true} {s ─⟨ A ⟩⟶ t} {Γ} (pd ,, nz ,, sc1 ,, sc2) = it ,, NonZero-subst (sym (susp-ctx-dim Γ)) it ,, l1 ,, l2
  where
    instance _ = nz
    instance _ = pd
    instance _ = susp-pd {Γ = Γ} pd
    open ≡-Reasoning

    l3 : suc (pred (ctx-dim Γ)) ≡ pred (ctx-dim (susp-ctx Γ))
    l3 = begin
      suc (pred (ctx-dim Γ))
        ≡⟨ suc-pred (ctx-dim Γ) ⟩
      ctx-dim Γ
        ≡˘⟨ cong pred (susp-ctx-dim Γ) ⟩
      pred (ctx-dim (susp-ctx Γ)) ∎

    l1 : SuppTm (susp-ctx Γ) (susp-tm s) ≡ pd-bd-vs (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) false
    l1 = begin
      SuppTm (susp-ctx Γ) (susp-tm s)
        ≡⟨ susp-SuppTm Γ s ⟩
      susp-vs (SuppTm Γ s)
        ≡⟨ cong susp-vs sc1 ⟩
      susp-vs (pd-bd-vs (pred (ctx-dim Γ)) Γ false)
        ≡⟨ susp-pd-bd-compat (pred (ctx-dim Γ)) Γ false ⟩
      pd-bd-vs (suc (pred (ctx-dim Γ))) (susp-ctx Γ) false
        ≡⟨ cong (λ x → pd-bd-vs x (susp-ctx Γ) false) l3 ⟩
      pd-bd-vs (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) false ∎

    l2 : SuppTm (susp-ctx Γ) (susp-tm t) ≡ pd-bd-vs (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) true
    l2 = begin
      SuppTm (susp-ctx Γ) (susp-tm t)
        ≡⟨ susp-SuppTm Γ t ⟩
      susp-vs (SuppTm Γ t)
        ≡⟨ cong susp-vs sc2 ⟩
      susp-vs (pd-bd-vs (pred (ctx-dim Γ)) Γ true)
        ≡⟨ susp-pd-bd-compat (pred (ctx-dim Γ)) Γ true ⟩
      pd-bd-vs (suc (pred (ctx-dim Γ))) (susp-ctx Γ) true
        ≡⟨ cong (λ x → pd-bd-vs x (susp-ctx Γ) true) l3 ⟩
      pd-bd-vs (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) true ∎

lookup-fst-var-snd : (n : ℕ) → lookup (trueAt (inject₁ (fromℕ n))) (fromℕ (suc n)) ≡ false
lookup-fst-var-snd zero = refl
lookup-fst-var-snd (suc n) = lookup-fst-var-snd n

susp-vs-non-empty : (xs : VarSet n) → Truth (varset-non-empty (susp-vs xs))
susp-vs-non-empty emp = tt
susp-vs-non-empty (ewf xs) = susp-vs-non-empty xs
susp-vs-non-empty (ewt xs) = tt

susp-vs-fst-var : (xs : VarSet n) → lookup (susp-vs xs) (fromℕ _) ≡ true
susp-vs-fst-var emp = refl
susp-vs-fst-var (x ∷ xs) = susp-vs-fst-var xs
