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

susp-supp : VarSet n → VarSet (2 + n)
susp-supp [] = full
susp-supp (x ∷ vs) = x ∷ susp-supp vs

VarSet-NonEmpty : (xs : VarSet n) → Set
VarSet-NonEmpty emp = ⊥
VarSet-NonEmpty (ewf xs) = VarSet-NonEmpty xs
VarSet-NonEmpty (ewt xs) = ⊤

susp-supp-drop : (xs : VarSet n) → .⦃ VarSet-NonEmpty xs ⦄ → susp-supp (drop xs) ≡ drop (susp-supp xs)
susp-supp-drop (ewf xs) = cong ewf (susp-supp-drop xs)
susp-supp-drop (ewt xs) = refl

pdb-bd-supp-non-empty : (n : ℕ) → (Γ : Ctx m) → .⦃ pdb : Γ ⊢pdb ⦄ → (b : Bool) → VarSet-NonEmpty (pdb-bd-supp n Γ b)
pdb-bd-supp-non-empty n ∅ ⦃ pdb ⦄ b = ⊥-elim (pdb-odd-length pdb)
pdb-bd-supp-non-empty n (∅ , A) b = tt
pdb-bd-supp-non-empty n (Γ , B , A) b with <-cmp n (ty-dim B) | b
... | tri< a ¬b ¬c | b = pdb-bd-supp-non-empty n Γ ⦃ pdb-prefix it ⦄ b
... | tri≈ ¬a b₁ ¬c | false = pdb-bd-supp-non-empty n Γ ⦃ pdb-prefix it ⦄ false
... | tri≈ ¬a b₁ ¬c | true = tt
... | tri> ¬a ¬b c | b = tt

susp-pdb-bd-compat : (n : ℕ)
                   → (Γ : Ctx m)
                   → .⦃ pdb : Γ ⊢pdb ⦄
                   → (b : Bool)
                   → susp-supp (pdb-bd-supp n Γ b) ≡ pdb-bd-supp (suc n) (susp-ctx Γ) ⦃ susp-pdb pdb ⦄ b
susp-pdb-bd-compat n ∅ b = ⊥-elim (pdb-odd-length it)
susp-pdb-bd-compat n (∅ , A) b = refl
susp-pdb-bd-compat n (Γ , B , A) b with  <-cmp n (ty-dim B) | <-cmp (suc n) (ty-dim (susp-ty B)) | b
... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ | b = cong ewf (cong ewf (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ b))
... | tri< a ¬b ¬c | tri≈ ¬a b₁ ¬c₁ | b = ⊥-elim (¬a (≤-<-trans a (<-≤-trans (n<1+n (ty-dim B)) (≤-reflexive (sym (susp-dim B))))))
... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c | b = ⊥-elim (¬a (≤-<-trans a (<-≤-trans (n<1+n (ty-dim B)) (≤-reflexive (sym (susp-dim B))))))
... | tri≈ ¬a b₁ ¬c | tri< a ¬b ¬c₁ | b = ⊥-elim (¬b (trans (cong suc b₁) (sym (susp-dim B))))
... | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ | false = cong ewf (cong ewf (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ false))
... | tri≈ ¬a b₁ ¬c | tri≈ ¬a₁ b₂ ¬c₁ | true = cong ewf (cong ewt (trans (susp-supp-drop (pdb-bd-supp n Γ ⦃ pdb-prefix it ⦄ true) ⦃ pdb-bd-supp-non-empty n Γ ⦃ pdb-prefix it ⦄ true ⦄) (cong drop (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ true))))
... | tri≈ ¬a b₁ ¬c | tri> ¬a₁ ¬b c | b = ⊥-elim (¬b (trans (cong suc b₁) (sym (susp-dim B))))
... | tri> ¬a ¬b c | tri< a ¬b₁ ¬c | b = ⊥-elim (¬c (s≤s (≤-trans (≤-reflexive (susp-dim B)) c)))
... | tri> ¬a ¬b c | tri≈ ¬a₁ b₁ ¬c | b = ⊥-elim (¬c (s≤s (≤-trans (≤-reflexive (susp-dim B)) c)))
... | tri> ¬a ¬b c | tri> ¬a₁ ¬b₁ c₁ | b = cong ewt (cong ewt (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ b))

susp-pd-bd-compat : (n : ℕ)
                  → (Γ : Ctx m)
                  → .⦃ pd : Γ ⊢pd ⦄
                  → (b : Bool)
                  → susp-supp (pd-bd-supp n Γ b) ≡ pd-bd-supp (suc n) (susp-ctx Γ) ⦃ susp-pd pd ⦄ b
susp-pd-bd-compat n Γ b = susp-pdb-bd-compat n Γ ⦃ pd-to-pdb it ⦄ b

susp-supp∪ : (vs vs′ : VarSet n) → susp-supp vs ∪ susp-supp vs′ ≡ susp-supp (vs ∪ vs′)
susp-supp∪ emp emp = refl
susp-supp∪ (x ∷ xs) (y ∷ ys) = cong₂ _∷_ refl (susp-supp∪ xs ys)

susp-suppLem : (n : ℕ) → empty ∪ ewf (trueAt (fromℕ n)) ∪ trueAt (inject₁ (fromℕ n)) ≡ susp-supp empty
susp-suppLem zero = refl
susp-suppLem (suc n) = cong (ewf) (susp-suppLem n)

susp-suppFstTruth : (xs : VarSet n) → Truth (lookup-isVar (susp-supp xs) get-fst)
susp-suppFstTruth emp = tt
susp-suppFstTruth (x ∷ xs) = susp-suppFstTruth xs

susp-suppSndTruth : (xs : VarSet n) → Truth (lookup-isVar (susp-supp xs) get-snd)
susp-suppSndTruth emp = tt
susp-suppSndTruth (x ∷ xs) = susp-suppSndTruth xs

susp-suppSnd : (xs : VarSet n) → FVTm get-snd ⊆ susp-supp xs
susp-suppSnd emp = refl
susp-suppSnd (x ∷ xs) = cong₂ _∷_ (sym (∨-identityʳ x)) (susp-suppSnd xs)

susp-suppEmpRight : (xs : VarSet n) → susp-supp xs ≡ susp-supp xs ∪ susp-supp empty
susp-suppEmpRight xs = sym (trans (susp-supp∪ xs empty) (cong susp-supp (∪-right-unit xs)))

susp-suppTy : (A : Ty n) → FVTy (susp-ty A) ≡ susp-supp (FVTy A)
susp-suppTm : (t : Tm n) → (susp-supp empty) ∪ FVTm (susp-tm t) ≡ susp-supp (FVTm t)
susp-suppSub : (σ : Sub n m ⋆) → FVSub (susp-sub σ) ≡ susp-supp (FVSub σ)
susp-suppTyTm : (A : Ty n) → (t : Tm n) → FVTy (susp-ty A) ∪ FVTm (susp-tm t) ≡ susp-supp (FVTy A ∪ FVTm t)

susp-suppTy ⋆ = susp-suppLem _
susp-suppTy (s ─⟨ A ⟩⟶ t) = begin
  FVTy (susp-ty (s ─⟨ A ⟩⟶ t)) ≡⟨⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-suppTyTm A s) ⟩
  susp-supp (FVTy A ∪ FVTm s) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-suppEmpRight (FVTy A ∪ FVTm s)) ⟩
  susp-supp (FVTy A ∪ FVTm s) ∪ susp-supp empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (susp-supp (FVTy A ∪ FVTm s)) (susp-supp empty) (FVTm (susp-tm t)) ⟩
  susp-supp (FVTy A ∪ FVTm s) ∪
    (susp-supp empty ∪ FVTm (susp-tm t)) ≡⟨ cong (susp-supp (FVTy A ∪ FVTm s) ∪_) (susp-suppTm t) ⟩
  susp-supp (FVTy A ∪ FVTm s) ∪ susp-supp (FVTm t) ≡⟨ susp-supp∪ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  susp-supp (FVTy (s ─⟨ A ⟩⟶ t)) ∎
  where
    open ≡-Reasoning

susp-suppTyTm A t = begin
  FVTy (susp-ty A) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-suppTy A) ⟩
  susp-supp (FVTy A) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-suppEmpRight (FVTy A)) ⟩
  susp-supp (FVTy A) ∪ susp-supp empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (susp-supp (FVTy A)) (susp-supp empty) (FVTm (susp-tm t)) ⟩
  susp-supp (FVTy A) ∪ (susp-supp empty ∪ FVTm (susp-tm t)) ≡⟨ cong (susp-supp (FVTy A) ∪_) (susp-suppTm t) ⟩
  susp-supp (FVTy A) ∪ susp-supp (FVTm t) ≡⟨ susp-supp∪ (FVTy A) (FVTm t) ⟩
  susp-supp (FVTy A ∪ FVTm t) ∎
  where
    open ≡-Reasoning


susp-suppTm (Var i) = lem _ i
  where
    lem : (n : ℕ) → (i : Fin n) → susp-supp empty ∪ trueAt (inject₁ (inject₁ i)) ≡ susp-supp (trueAt i)
    lem (suc n) zero = cong ewt (∪-right-unit (susp-supp empty))
    lem (suc n) (suc i) = cong ewf (lem n i)
susp-suppTm (Coh Δ A σ) = trans (∪-comm (susp-supp empty) (FVTm (susp-tm (Coh Δ A σ)))) (trans (cong (_∪ susp-supp empty) (susp-suppSub σ)) (sym (susp-suppEmpRight (FVSub σ))))

susp-suppSub ⟨ A ⟩′ = susp-suppLem _
susp-suppSub ⟨ σ , t ⟩ = begin
  FVSub (susp-sub ⟨ σ , t ⟩) ≡⟨⟩
  FVSub (susp-sub σ) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-suppSub σ) ⟩
  susp-supp (FVSub σ) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (susp-suppEmpRight (FVSub σ)) ⟩
  susp-supp (FVSub σ) ∪ susp-supp empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (susp-supp (FVSub σ)) (susp-supp empty) (FVTm (susp-tm t)) ⟩
  susp-supp (FVSub σ) ∪ (susp-supp empty ∪ FVTm (susp-tm t)) ≡⟨ cong (susp-supp (FVSub σ) ∪_) (susp-suppTm t) ⟩
  susp-supp (FVSub σ) ∪ susp-supp (FVTm t) ≡⟨ susp-supp∪ (FVSub σ) (FVTm t) ⟩
  susp-supp (FVSub ⟨ σ , t ⟩) ∎
  where
    open ≡-Reasoning

susp-supp-full : susp-supp (full {n}) ≡ full
susp-supp-full {zero} = refl
susp-supp-full {suc n} = cong ewt susp-supp-full

vs-sub-susp : (xs : VarSet n) → (σ : Sub n m ⋆) → susp-supp xs [ susp-sub σ ]vs ≡ susp-supp (xs [ σ ]vs)
vs-sub-susp emp ⟨ A ⟩′ = susp-suppLem _
vs-sub-susp (ewf xs) ⟨ σ , t ⟩ = vs-sub-susp xs σ
vs-sub-susp (ewt xs) ⟨ σ , t ⟩ = begin
  susp-supp xs [ susp-sub σ ]vs ∪ FVTm (susp-tm t)
    ≡⟨ cong (_∪ FVTm (susp-tm t)) (trans (vs-sub-susp xs σ) (susp-suppEmpRight (xs [ σ ]vs))) ⟩
  susp-supp (xs [ σ ]vs) ∪ susp-supp empty ∪ FVTm (susp-tm t)
    ≡⟨ ∪-assoc (susp-supp (xs [ σ ]vs)) (susp-supp empty) (FVTm (susp-tm t)) ⟩
  susp-supp (xs [ σ ]vs) ∪ (susp-supp empty ∪ FVTm (susp-tm t))
    ≡⟨ cong (susp-supp (xs [ σ ]vs) ∪_) (susp-suppTm t) ⟩
  susp-supp (xs [ σ ]vs) ∪ susp-supp (FVTm t)
    ≡⟨ susp-supp∪ (xs [ σ ]vs) (FVTm t) ⟩
  susp-supp (xs [ σ ]vs ∪ FVTm t) ∎
  where
    open ≡-Reasoning

susp-suppTyContainsEmpty : (A : Ty n) → susp-supp empty ⊆ FVTy (susp-ty A)
susp-suppTyContainsEmpty ⋆ = ⊆-reflexive (sym (susp-suppLem _))
susp-suppTyContainsEmpty (s ─⟨ A ⟩⟶ t) = begin
  susp-supp empty
    ≤⟨ susp-suppTyContainsEmpty A ⟩
  FVTy (susp-ty A)
    ≤⟨ ∪-⊆-1 (FVTy (susp-ty A)) (FVTm (susp-tm s)) ⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s)
    ≤⟨ ∪-⊆-1 (FVTy (susp-ty A) ∪ FVTm (susp-tm s)) (FVTm (susp-tm t)) ⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s) ∪ FVTm (susp-tm t) ∎
  where
    open PReasoning (⊆-poset _)

susp-suppTmContainsEmpty : (Γ : Ctx n) → (t : Tm n) → susp-supp empty ⊆ SuppTm (susp-ctx Γ) (susp-tm t)
susp-suppTmContainsEmpty Γ t = begin
  susp-supp empty
    ≤⟨ susp-suppTyContainsEmpty (tm-to-ty Γ t) ⟩
  FVTy (susp-ty (tm-to-ty Γ t))
    ≤⟨ DC-⊆ (susp-ctx Γ) (FVTy (susp-ty (tm-to-ty Γ t))) ⟩
  SuppTy (susp-ctx Γ) (susp-ty (tm-to-ty Γ t))
    ≡⟨ cong (SuppTy (susp-ctx Γ)) (≃ty-to-≡ (tm-to-ty-susp t Γ)) ⟩
  SuppTy (susp-ctx Γ) (tm-to-ty (susp-ctx Γ) (susp-tm t))
    ≤⟨ SuppContainsType (susp-tm t) (susp-ctx Γ) ⟩
  SuppTm (susp-ctx Γ) (susp-tm t) ∎
  where
    open PReasoning (⊆-poset _)

DC-susp-supp : (Γ : Ctx n) → (xs : VarSet n) → DC (susp-ctx Γ) (susp-supp xs) ≡ susp-supp (DC Γ xs)
DC-susp-supp ∅ emp = refl
DC-susp-supp (Γ , A) (ewf xs) = cong ewf (DC-susp-supp Γ xs)
DC-susp-supp (Γ , A) (ewt xs) = cong ewt (begin
  DC (susp-ctx Γ) (susp-supp xs ∪ FVTy (susp-ty A))
    ≡⟨ cong (DC (susp-ctx Γ)) lem ⟩
  DC (susp-ctx Γ) (susp-supp (xs ∪ FVTy A))
    ≡⟨ DC-susp-supp Γ (xs ∪ FVTy A) ⟩
  susp-supp (DC Γ (xs ∪ FVTy A)) ∎)
  where
    open ≡-Reasoning
    lem : susp-supp xs ∪ FVTy (susp-ty A) ≡ susp-supp (xs ∪ FVTy A)
    lem = begin
      susp-supp xs ∪ FVTy (susp-ty A)
        ≡⟨ cong (susp-supp xs ∪_) (susp-suppTy A) ⟩
      susp-supp xs ∪ susp-supp (FVTy A)
        ≡⟨ susp-supp∪ xs (FVTy A) ⟩
      susp-supp (xs ∪ FVTy A) ∎

susp-SuppTm′ : (Γ : Ctx n) → (t : Tm n) → SuppTm (susp-ctx Γ) (susp-tm t) ≡ susp-supp (SuppTm Γ t)
susp-SuppTm′ Γ t = begin
  SuppTm (susp-ctx Γ) (susp-tm t)
    ≡⟨ susp-suppTmContainsEmpty Γ t ⟩
  SuppTm (susp-ctx Γ) (susp-tm t) ∪ susp-supp empty
    ≡⟨ ∪-comm (DC (susp-ctx Γ) (FVTm (susp-tm t))) (susp-supp empty) ⟩
  susp-supp empty ∪ SuppTm (susp-ctx Γ) (susp-tm t)
    ≡˘⟨ cong (_∪ SuppTm (susp-ctx Γ) (susp-tm t)) (trans (DC-susp-supp Γ empty) (cong susp-supp (DC-empty Γ))) ⟩
  DC (susp-ctx Γ) (susp-supp empty) ∪ DC (susp-ctx Γ) (FVTm (susp-tm t))
    ≡˘⟨ DC-∪ (susp-ctx Γ) (susp-supp empty) (FVTm (susp-tm t)) ⟩
  DC (susp-ctx Γ) (susp-supp empty ∪ FVTm (susp-tm t))
    ≡⟨ cong (DC (susp-ctx Γ)) (susp-suppTm t) ⟩
  DC (susp-ctx Γ) (susp-supp (FVTm t))
    ≡⟨ DC-susp-supp Γ (FVTm t) ⟩
  susp-supp (SuppTm Γ t) ∎
  where
    open ≡-Reasoning

susp-SuppTy′ : (Γ : Ctx n) → (A : Ty n) → SuppTy (susp-ctx Γ) (susp-ty A) ≡ susp-supp (SuppTy Γ A)
susp-SuppTy′ Γ A = begin
  SuppTy (susp-ctx Γ) (susp-ty A)
    ≡⟨ cong (DC (susp-ctx Γ)) (susp-suppTy A) ⟩
  DC (susp-ctx Γ) (susp-supp (FVTy A))
    ≡⟨ DC-susp-supp Γ (FVTy A) ⟩
  susp-supp (SuppTy Γ A) ∎
  where
    open ≡-Reasoning

susp-SuppTm-prop : (s t : Tm n) → SuppTm Γ s ≡ SuppTm Γ t → SuppTm (susp-ctx Γ) (susp-tm s) ≡ SuppTm (susp-ctx Γ) (susp-tm t)
susp-SuppTm-prop {Γ = Γ} s t p = begin
  SuppTm (susp-ctx Γ) (susp-tm s)
    ≡⟨ susp-SuppTm′ Γ s ⟩
  susp-supp (SuppTm Γ s)
    ≡⟨ cong susp-supp p ⟩
  susp-supp (SuppTm Γ t)
    ≡˘⟨ susp-SuppTm′ Γ t ⟩
  SuppTm (susp-ctx Γ) (susp-tm t) ∎
  where
    open ≡-Reasoning

susp-supp-cond : {b : Bool} → {A : Ty (suc n)} → {Γ : Ctx (suc n)} → supp-condition b A Γ → supp-condition b (susp-ty A) (susp-ctx Γ)
susp-supp-cond {b = false} {A} {Γ} sc = begin
  SuppTy (susp-ctx Γ) (susp-ty A)
    ≡⟨ susp-SuppTy′ Γ A ⟩
  susp-supp (SuppTy Γ A)
    ≡⟨ cong susp-supp sc ⟩
  susp-supp full
    ≡⟨ susp-supp-full ⟩
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

    l1 : SuppTm (susp-ctx Γ) (susp-tm s) ≡ pd-bd-supp (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) false
    l1 = begin
      SuppTm (susp-ctx Γ) (susp-tm s)
        ≡⟨ susp-SuppTm′ Γ s ⟩
      susp-supp (SuppTm Γ s)
        ≡⟨ cong susp-supp sc1 ⟩
      susp-supp (pd-bd-supp (pred (ctx-dim Γ)) Γ false)
        ≡⟨ susp-pd-bd-compat (pred (ctx-dim Γ)) Γ false ⟩
      pd-bd-supp (suc (pred (ctx-dim Γ))) (susp-ctx Γ) false
        ≡⟨ cong (λ x → pd-bd-supp x (susp-ctx Γ) false) l3 ⟩
      pd-bd-supp (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) false ∎

    l2 : SuppTm (susp-ctx Γ) (susp-tm t) ≡ pd-bd-supp (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) true
    l2 = begin
      SuppTm (susp-ctx Γ) (susp-tm t)
        ≡⟨ susp-SuppTm′ Γ t ⟩
      susp-supp (SuppTm Γ t)
        ≡⟨ cong susp-supp sc2 ⟩
      susp-supp (pd-bd-supp (pred (ctx-dim Γ)) Γ true)
        ≡⟨ susp-pd-bd-compat (pred (ctx-dim Γ)) Γ true ⟩
      pd-bd-supp (suc (pred (ctx-dim Γ))) (susp-ctx Γ) true
        ≡⟨ cong (λ x → pd-bd-supp x (susp-ctx Γ) true) l3 ⟩
      pd-bd-supp (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) true ∎

lookup-fst-var-snd : (n : ℕ) → lookup (trueAt (inject₁ (fromℕ n))) (fromℕ (suc n)) ≡ false
lookup-fst-var-snd zero = refl
lookup-fst-var-snd (suc n) = lookup-fst-var-snd n

susp-supp-non-empty : (xs : VarSet n) → Truth (varset-non-empty (susp-supp xs))
susp-supp-non-empty emp = tt
susp-supp-non-empty (ewf xs) = susp-supp-non-empty xs
susp-supp-non-empty (ewt xs) = tt

susp-supp-fst-var : (xs : VarSet n) → lookup (susp-supp xs) (fromℕ _) ≡ true
susp-supp-fst-var emp = refl
susp-supp-fst-var (x ∷ xs) = susp-supp-fst-var xs
