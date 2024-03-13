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

suspSupp : VarSet n → VarSet (2 + n)
suspSupp [] = full
suspSupp (x ∷ vs) = x ∷ suspSupp vs

VarSet-NonEmpty : (xs : VarSet n) → Set
VarSet-NonEmpty emp = ⊥
VarSet-NonEmpty (ewf xs) = VarSet-NonEmpty xs
VarSet-NonEmpty (ewt xs) = ⊤

susp-supp-drop : (xs : VarSet n) → .⦃ VarSet-NonEmpty xs ⦄ → suspSupp (drop xs) ≡ drop (suspSupp xs)
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
                   → suspSupp (pdb-bd-supp n Γ b) ≡ pdb-bd-supp (suc n) (susp-ctx Γ) ⦃ susp-pdb pdb ⦄ b
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
                  → suspSupp (pd-bd-supp n Γ b) ≡ pd-bd-supp (suc n) (susp-ctx Γ) ⦃ susp-pd pd ⦄ b
susp-pd-bd-compat n Γ b = susp-pdb-bd-compat n Γ ⦃ pd-to-pdb it ⦄ b

suspSupp∪ : (vs vs′ : VarSet n) → suspSupp vs ∪ suspSupp vs′ ≡ suspSupp (vs ∪ vs′)
suspSupp∪ emp emp = refl
suspSupp∪ (x ∷ xs) (y ∷ ys) = cong₂ _∷_ refl (suspSupp∪ xs ys)

suspSuppLem : (n : ℕ) → empty ∪ ewf (trueAt (fromℕ n)) ∪ trueAt (inject₁ (fromℕ n)) ≡ suspSupp empty
suspSuppLem zero = refl
suspSuppLem (suc n) = cong (ewf) (suspSuppLem n)

suspSuppFstTruth : (xs : VarSet n) → Truth (lookup-isVar (suspSupp xs) get-fst)
suspSuppFstTruth emp = tt
suspSuppFstTruth (x ∷ xs) = suspSuppFstTruth xs

suspSuppSndTruth : (xs : VarSet n) → Truth (lookup-isVar (suspSupp xs) get-snd)
suspSuppSndTruth emp = tt
suspSuppSndTruth (x ∷ xs) = suspSuppSndTruth xs

suspSuppSnd : (xs : VarSet n) → FVTm get-snd ⊆ suspSupp xs
suspSuppSnd emp = refl
suspSuppSnd (x ∷ xs) = cong₂ _∷_ (sym (∨-identityʳ x)) (suspSuppSnd xs)

suspSuppEmpRight : (xs : VarSet n) → suspSupp xs ≡ suspSupp xs ∪ suspSupp empty
suspSuppEmpRight xs = sym (trans (suspSupp∪ xs empty) (cong suspSupp (∪-right-unit xs)))

suspSuppTy : (A : Ty n) → FVTy (susp-ty A) ≡ suspSupp (FVTy A)
suspSuppTm : (t : Tm n) → (suspSupp empty) ∪ FVTm (susp-tm t) ≡ suspSupp (FVTm t)
suspSuppSub : (σ : Sub n m ⋆) → FVSub (susp-sub σ) ≡ suspSupp (FVSub σ)
suspSuppTyTm : (A : Ty n) → (t : Tm n) → FVTy (susp-ty A) ∪ FVTm (susp-tm t) ≡ suspSupp (FVTy A ∪ FVTm t)

suspSuppTy ⋆ = suspSuppLem _
suspSuppTy (s ─⟨ A ⟩⟶ t) = begin
  FVTy (susp-ty (s ─⟨ A ⟩⟶ t)) ≡⟨⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (suspSuppTyTm A s) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (suspSuppEmpRight (FVTy A ∪ FVTm s)) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ suspSupp empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (suspSupp (FVTy A ∪ FVTm s)) (suspSupp empty) (FVTm (susp-tm t)) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪
    (suspSupp empty ∪ FVTm (susp-tm t)) ≡⟨ cong (suspSupp (FVTy A ∪ FVTm s) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  suspSupp (FVTy (s ─⟨ A ⟩⟶ t)) ∎
  where
    open ≡-Reasoning

suspSuppTyTm A t = begin
  FVTy (susp-ty A) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (suspSuppTy A) ⟩
  suspSupp (FVTy A) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (suspSuppEmpRight (FVTy A)) ⟩
  suspSupp (FVTy A) ∪ suspSupp empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (suspSupp (FVTy A)) (suspSupp empty) (FVTm (susp-tm t)) ⟩
  suspSupp (FVTy A) ∪ (suspSupp empty ∪ FVTm (susp-tm t)) ≡⟨ cong (suspSupp (FVTy A) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVTy A) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVTy A) (FVTm t) ⟩
  suspSupp (FVTy A ∪ FVTm t) ∎
  where
    open ≡-Reasoning


suspSuppTm (Var i) = lem _ i
  where
    lem : (n : ℕ) → (i : Fin n) → suspSupp empty ∪ trueAt (inject₁ (inject₁ i)) ≡ suspSupp (trueAt i)
    lem (suc n) zero = cong ewt (∪-right-unit (suspSupp empty))
    lem (suc n) (suc i) = cong ewf (lem n i)
suspSuppTm (Coh Δ A σ) = trans (∪-comm (suspSupp empty) (FVTm (susp-tm (Coh Δ A σ)))) (trans (cong (_∪ suspSupp empty) (suspSuppSub σ)) (sym (suspSuppEmpRight (FVSub σ))))

suspSuppSub ⟨ A ⟩′ = suspSuppLem _
suspSuppSub ⟨ σ , t ⟩ = begin
  FVSub (susp-sub ⟨ σ , t ⟩) ≡⟨⟩
  FVSub (susp-sub σ) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (suspSuppSub σ) ⟩
  suspSupp (FVSub σ) ∪ FVTm (susp-tm t) ≡⟨ cong (_∪ FVTm (susp-tm t)) (suspSuppEmpRight (FVSub σ)) ⟩
  suspSupp (FVSub σ) ∪ suspSupp empty ∪ FVTm (susp-tm t) ≡⟨ ∪-assoc (suspSupp (FVSub σ)) (suspSupp empty) (FVTm (susp-tm t)) ⟩
  suspSupp (FVSub σ) ∪ (suspSupp empty ∪ FVTm (susp-tm t)) ≡⟨ cong (suspSupp (FVSub σ) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVSub σ) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVSub σ) (FVTm t) ⟩
  suspSupp (FVSub ⟨ σ , t ⟩) ∎
  where
    open ≡-Reasoning

suspSuppFull : suspSupp (full {n}) ≡ full
suspSuppFull {zero} = refl
suspSuppFull {suc n} = cong ewt suspSuppFull

vs-sub-susp : (xs : VarSet n) → (σ : Sub n m ⋆) → suspSupp xs [ susp-sub σ ]vs ≡ suspSupp (xs [ σ ]vs)
vs-sub-susp emp ⟨ A ⟩′ = suspSuppLem _
vs-sub-susp (ewf xs) ⟨ σ , t ⟩ = vs-sub-susp xs σ
vs-sub-susp (ewt xs) ⟨ σ , t ⟩ = begin
  suspSupp xs [ susp-sub σ ]vs ∪ FVTm (susp-tm t)
    ≡⟨ cong (_∪ FVTm (susp-tm t)) (trans (vs-sub-susp xs σ) (suspSuppEmpRight (xs [ σ ]vs))) ⟩
  suspSupp (xs [ σ ]vs) ∪ suspSupp empty ∪ FVTm (susp-tm t)
    ≡⟨ ∪-assoc (suspSupp (xs [ σ ]vs)) (suspSupp empty) (FVTm (susp-tm t)) ⟩
  suspSupp (xs [ σ ]vs) ∪ (suspSupp empty ∪ FVTm (susp-tm t))
    ≡⟨ cong (suspSupp (xs [ σ ]vs) ∪_) (suspSuppTm t) ⟩
  suspSupp (xs [ σ ]vs) ∪ suspSupp (FVTm t)
    ≡⟨ suspSupp∪ (xs [ σ ]vs) (FVTm t) ⟩
  suspSupp (xs [ σ ]vs ∪ FVTm t) ∎
  where
    open ≡-Reasoning

suspSuppTyContainsEmpty : (A : Ty n) → suspSupp empty ⊆ FVTy (susp-ty A)
suspSuppTyContainsEmpty ⋆ = ⊆-reflexive (sym (suspSuppLem _))
suspSuppTyContainsEmpty (s ─⟨ A ⟩⟶ t) = begin
  suspSupp empty
    ≤⟨ suspSuppTyContainsEmpty A ⟩
  FVTy (susp-ty A)
    ≤⟨ ∪-⊆-1 (FVTy (susp-ty A)) (FVTm (susp-tm s)) ⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s)
    ≤⟨ ∪-⊆-1 (FVTy (susp-ty A) ∪ FVTm (susp-tm s)) (FVTm (susp-tm t)) ⟩
  FVTy (susp-ty A) ∪ FVTm (susp-tm s) ∪ FVTm (susp-tm t) ∎
  where
    open PReasoning (⊆-poset _)

suspSuppTmContainsEmpty : (Γ : Ctx n) → (t : Tm n) → suspSupp empty ⊆ SuppTm (susp-ctx Γ) (susp-tm t)
suspSuppTmContainsEmpty Γ t = begin
  suspSupp empty
    ≤⟨ suspSuppTyContainsEmpty (tm-to-ty Γ t) ⟩
  FVTy (susp-ty (tm-to-ty Γ t))
    ≤⟨ DC-⊆ (susp-ctx Γ) (FVTy (susp-ty (tm-to-ty Γ t))) ⟩
  SuppTy (susp-ctx Γ) (susp-ty (tm-to-ty Γ t))
    ≡⟨ cong (SuppTy (susp-ctx Γ)) (≃ty-to-≡ (tm-to-ty-susp t Γ)) ⟩
  SuppTy (susp-ctx Γ) (tm-to-ty (susp-ctx Γ) (susp-tm t))
    ≤⟨ SuppContainsType (susp-tm t) (susp-ctx Γ) ⟩
  SuppTm (susp-ctx Γ) (susp-tm t) ∎
  where
    open PReasoning (⊆-poset _)

DC-suspSupp : (Γ : Ctx n) → (xs : VarSet n) → DC (susp-ctx Γ) (suspSupp xs) ≡ suspSupp (DC Γ xs)
DC-suspSupp ∅ emp = refl
DC-suspSupp (Γ , A) (ewf xs) = cong ewf (DC-suspSupp Γ xs)
DC-suspSupp (Γ , A) (ewt xs) = cong ewt (begin
  DC (susp-ctx Γ) (suspSupp xs ∪ FVTy (susp-ty A))
    ≡⟨ cong (DC (susp-ctx Γ)) lem ⟩
  DC (susp-ctx Γ) (suspSupp (xs ∪ FVTy A))
    ≡⟨ DC-suspSupp Γ (xs ∪ FVTy A) ⟩
  suspSupp (DC Γ (xs ∪ FVTy A)) ∎)
  where
    open ≡-Reasoning
    lem : suspSupp xs ∪ FVTy (susp-ty A) ≡ suspSupp (xs ∪ FVTy A)
    lem = begin
      suspSupp xs ∪ FVTy (susp-ty A)
        ≡⟨ cong (suspSupp xs ∪_) (suspSuppTy A) ⟩
      suspSupp xs ∪ suspSupp (FVTy A)
        ≡⟨ suspSupp∪ xs (FVTy A) ⟩
      suspSupp (xs ∪ FVTy A) ∎

suspSuppTm′ : (Γ : Ctx n) → (t : Tm n) → SuppTm (susp-ctx Γ) (susp-tm t) ≡ suspSupp (SuppTm Γ t)
suspSuppTm′ Γ t = begin
  SuppTm (susp-ctx Γ) (susp-tm t)
    ≡⟨ suspSuppTmContainsEmpty Γ t ⟩
  SuppTm (susp-ctx Γ) (susp-tm t) ∪ suspSupp empty
    ≡⟨ ∪-comm (DC (susp-ctx Γ) (FVTm (susp-tm t))) (suspSupp empty) ⟩
  suspSupp empty ∪ SuppTm (susp-ctx Γ) (susp-tm t)
    ≡˘⟨ cong (_∪ SuppTm (susp-ctx Γ) (susp-tm t)) (trans (DC-suspSupp Γ empty) (cong suspSupp (DC-empty Γ))) ⟩
  DC (susp-ctx Γ) (suspSupp empty) ∪ DC (susp-ctx Γ) (FVTm (susp-tm t))
    ≡˘⟨ DC-∪ (susp-ctx Γ) (suspSupp empty) (FVTm (susp-tm t)) ⟩
  DC (susp-ctx Γ) (suspSupp empty ∪ FVTm (susp-tm t))
    ≡⟨ cong (DC (susp-ctx Γ)) (suspSuppTm t) ⟩
  DC (susp-ctx Γ) (suspSupp (FVTm t))
    ≡⟨ DC-suspSupp Γ (FVTm t) ⟩
  suspSupp (SuppTm Γ t) ∎
  where
    open ≡-Reasoning

suspSuppTy′ : (Γ : Ctx n) → (A : Ty n) → SuppTy (susp-ctx Γ) (susp-ty A) ≡ suspSupp (SuppTy Γ A)
suspSuppTy′ Γ A = begin
  SuppTy (susp-ctx Γ) (susp-ty A)
    ≡⟨ cong (DC (susp-ctx Γ)) (suspSuppTy A) ⟩
  DC (susp-ctx Γ) (suspSupp (FVTy A))
    ≡⟨ DC-suspSupp Γ (FVTy A) ⟩
  suspSupp (SuppTy Γ A) ∎
  where
    open ≡-Reasoning

SuspSuppTmProp : (s t : Tm n) → SuppTm Γ s ≡ SuppTm Γ t → SuppTm (susp-ctx Γ) (susp-tm s) ≡ SuppTm (susp-ctx Γ) (susp-tm t)
SuspSuppTmProp {Γ = Γ} s t p = begin
  SuppTm (susp-ctx Γ) (susp-tm s)
    ≡⟨ suspSuppTm′ Γ s ⟩
  suspSupp (SuppTm Γ s)
    ≡⟨ cong suspSupp p ⟩
  suspSupp (SuppTm Γ t)
    ≡˘⟨ suspSuppTm′ Γ t ⟩
  SuppTm (susp-ctx Γ) (susp-tm t) ∎
  where
    open ≡-Reasoning

suspSuppCondition : {b : Bool} → {A : Ty (suc n)} → {Γ : Ctx (suc n)} → supp-condition b A Γ → supp-condition b (susp-ty A) (susp-ctx Γ)
suspSuppCondition {b = false} {A} {Γ} sc = begin
  SuppTy (susp-ctx Γ) (susp-ty A)
    ≡⟨ suspSuppTy′ Γ A ⟩
  suspSupp (SuppTy Γ A)
    ≡⟨ cong suspSupp sc ⟩
  suspSupp full
    ≡⟨ suspSuppFull ⟩
  full ∎
  where
    open ≡-Reasoning
suspSuppCondition {b = true} {s ─⟨ A ⟩⟶ t} {Γ} (pd ,, nz ,, sc1 ,, sc2) = it ,, NonZero-subst (sym (susp-ctx-dim Γ)) it ,, l1 ,, l2
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
        ≡⟨ suspSuppTm′ Γ s ⟩
      suspSupp (SuppTm Γ s)
        ≡⟨ cong suspSupp sc1 ⟩
      suspSupp (pd-bd-supp (pred (ctx-dim Γ)) Γ false)
        ≡⟨ susp-pd-bd-compat (pred (ctx-dim Γ)) Γ false ⟩
      pd-bd-supp (suc (pred (ctx-dim Γ))) (susp-ctx Γ) false
        ≡⟨ cong (λ x → pd-bd-supp x (susp-ctx Γ) false) l3 ⟩
      pd-bd-supp (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) false ∎

    l2 : SuppTm (susp-ctx Γ) (susp-tm t) ≡ pd-bd-supp (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) true
    l2 = begin
      SuppTm (susp-ctx Γ) (susp-tm t)
        ≡⟨ suspSuppTm′ Γ t ⟩
      suspSupp (SuppTm Γ t)
        ≡⟨ cong suspSupp sc2 ⟩
      suspSupp (pd-bd-supp (pred (ctx-dim Γ)) Γ true)
        ≡⟨ susp-pd-bd-compat (pred (ctx-dim Γ)) Γ true ⟩
      pd-bd-supp (suc (pred (ctx-dim Γ))) (susp-ctx Γ) true
        ≡⟨ cong (λ x → pd-bd-supp x (susp-ctx Γ) true) l3 ⟩
      pd-bd-supp (pred (ctx-dim (susp-ctx Γ))) (susp-ctx Γ) true ∎

lookup-fst-var-snd : (n : ℕ) → lookup (trueAt (inject₁ (fromℕ n))) (fromℕ (suc n)) ≡ false
lookup-fst-var-snd zero = refl
lookup-fst-var-snd (suc n) = lookup-fst-var-snd n

suspSupp-non-empty : (xs : VarSet n) → Truth (varset-non-empty (suspSupp xs))
suspSupp-non-empty emp = tt
suspSupp-non-empty (ewf xs) = suspSupp-non-empty xs
suspSupp-non-empty (ewt xs) = tt

suspSupp-fst-var : (xs : VarSet n) → lookup (suspSupp xs) (fromℕ _) ≡ true
suspSupp-fst-var emp = refl
suspSupp-fst-var (x ∷ xs) = suspSupp-fst-var xs
