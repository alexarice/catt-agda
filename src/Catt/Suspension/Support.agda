module Catt.Suspension.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension.Pasting
open import Relation.Binary.Definitions
open import Relation.Nullary

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
                   → suspSupp (pdb-bd-supp n Γ b) ≡ pdb-bd-supp (suc n) (suspCtx Γ) ⦃ susp-pdb pdb ⦄ b
susp-pdb-bd-compat n ∅ b = ⊥-elim (pdb-odd-length it)
susp-pdb-bd-compat n (∅ , A) b = refl
susp-pdb-bd-compat n (Γ , B , A) b with  <-cmp n (ty-dim B) | <-cmp (suc n) (ty-dim (suspTy B)) | b
... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ | b = cong ewf (cong ewf (susp-pdb-bd-compat n Γ ⦃ pdb-prefix it ⦄ b))
... | tri< a ¬b ¬c | tri≈ ¬a b₁ ¬c₁ | b = ⊥-elim (¬a (<-transʳ a (<-transˡ (n<1+n (ty-dim B)) (≤-reflexive (sym (susp-dim B))))))
... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c | b = ⊥-elim (¬a (<-transʳ a (<-transˡ (n<1+n (ty-dim B)) (≤-reflexive (sym (susp-dim B))))))
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
                  → suspSupp (pd-bd-supp n Γ b) ≡ pd-bd-supp (suc n) (suspCtx Γ) ⦃ susp-pd pd ⦄ b
susp-pd-bd-compat n Γ b = susp-pdb-bd-compat n Γ ⦃ pd-to-pdb it ⦄ b

suspSupp∪ : (vs vs′ : VarSet n) → suspSupp vs ∪ suspSupp vs′ ≡ suspSupp (vs ∪ vs′)
suspSupp∪ emp emp = refl
suspSupp∪ (x ∷ xs) (y ∷ ys) = cong₂ _∷_ refl (suspSupp∪ xs ys)

suspSuppLem : (n : ℕ) → empty ∪ ewf (trueAt (fromℕ n)) ∪ trueAt (inject₁ (fromℕ n)) ≡ suspSupp empty
suspSuppLem zero = refl
suspSuppLem (suc n) = cong (ewf) (suspSuppLem n)

suspSuppFstTruth : (xs : VarSet n) → Truth (lookup-isVar (suspSupp xs) getFst)
suspSuppFstTruth emp = tt
suspSuppFstTruth (x ∷ xs) = suspSuppFstTruth xs

suspSuppSndTruth : (xs : VarSet n) → Truth (lookup-isVar (suspSupp xs) getSnd)
suspSuppSndTruth emp = tt
suspSuppSndTruth (x ∷ xs) = suspSuppSndTruth xs

suspSuppSnd : (xs : VarSet n) → FVTm getSnd ⊆ suspSupp xs
suspSuppSnd emp = refl
suspSuppSnd (x ∷ xs) = cong₂ _∷_ (sym (∨-identityʳ x)) (suspSuppSnd xs)

suspSuppEmpRight : (xs : VarSet n) → suspSupp xs ≡ suspSupp xs ∪ suspSupp empty
suspSuppEmpRight xs = sym (trans (suspSupp∪ xs empty) (cong suspSupp (∪-right-unit xs)))

suspSuppTy : (A : Ty n) → FVTy (suspTy A) ≡ suspSupp (FVTy A)
suspSuppTm : (t : Tm n) → (suspSupp empty) ∪ FVTm (suspTm t) ≡ suspSupp (FVTm t)
suspSuppSub : (σ : Sub n m ⋆) → FVSub (suspSub σ) ≡ suspSupp (FVSub σ)
suspSuppTyTm : (A : Ty n) → (t : Tm n) → FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ suspSupp (FVTy A ∪ FVTm t)

suspSuppTy ⋆ = suspSuppLem _
suspSuppTy (s ─⟨ A ⟩⟶ t) = begin
  FVTy (suspTy (s ─⟨ A ⟩⟶ t)) ≡⟨⟩
  FVTy (suspTy A) ∪ FVTm (suspTm s) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppTyTm A s) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVTy A ∪ FVTm s)) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVTy A ∪ FVTm s)) (suspSupp empty) (FVTm (suspTm t)) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪
    (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVTy A ∪ FVTm s) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVTy A ∪ FVTm s) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVTy A ∪ FVTm s) (FVTm t) ⟩
  suspSupp (FVTy (s ─⟨ A ⟩⟶ t)) ∎
  where
    open ≡-Reasoning

suspSuppTyTm A t = begin
  FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppTy A) ⟩
  suspSupp (FVTy A) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVTy A)) ⟩
  suspSupp (FVTy A) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVTy A)) (suspSupp empty) (FVTm (suspTm t)) ⟩
  suspSupp (FVTy A) ∪ (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVTy A) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVTy A) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVTy A) (FVTm t) ⟩
  suspSupp (FVTy A ∪ FVTm t) ∎
  where
    open ≡-Reasoning


suspSuppTm (Var i) = lem _ i
  where
    lem : (n : ℕ) → (i : Fin n) → suspSupp empty ∪ trueAt (inject₁ (inject₁ i)) ≡ suspSupp (trueAt i)
    lem (suc n) zero = cong ewt (∪-right-unit (suspSupp empty))
    lem (suc n) (suc i) = cong ewf (lem n i)
suspSuppTm (Coh Δ A σ) = trans (∪-comm (suspSupp empty) (FVTm (suspTm (Coh Δ A σ)))) (trans (cong (_∪ suspSupp empty) (suspSuppSub σ)) (sym (suspSuppEmpRight (FVSub σ))))

suspSuppSub ⟨⟩ = suspSuppLem _
suspSuppSub ⟨ σ , t ⟩ = begin
  FVSub (suspSub ⟨ σ , t ⟩) ≡⟨⟩
  FVSub (suspSub σ) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppSub σ) ⟩
  suspSupp (FVSub σ) ∪ FVTm (suspTm t) ≡⟨ cong (_∪ FVTm (suspTm t)) (suspSuppEmpRight (FVSub σ)) ⟩
  suspSupp (FVSub σ) ∪ suspSupp empty ∪ FVTm (suspTm t) ≡⟨ ∪-assoc (suspSupp (FVSub σ)) (suspSupp empty) (FVTm (suspTm t)) ⟩
  suspSupp (FVSub σ) ∪ (suspSupp empty ∪ FVTm (suspTm t)) ≡⟨ cong (suspSupp (FVSub σ) ∪_) (suspSuppTm t) ⟩
  suspSupp (FVSub σ) ∪ suspSupp (FVTm t) ≡⟨ suspSupp∪ (FVSub σ) (FVTm t) ⟩
  suspSupp (FVSub ⟨ σ , t ⟩) ∎
  where
    open ≡-Reasoning

suspSuppFull : suspSupp (full {n}) ≡ full
suspSuppFull {zero} = refl
suspSuppFull {suc n} = cong ewt suspSuppFull

TransportVarSet-susp : (xs : VarSet n) → (σ : Sub n m ⋆) → TransportVarSet (suspSupp xs) (suspSub σ) ≡ suspSupp (TransportVarSet xs σ)
TransportVarSet-susp emp ⟨⟩ = suspSuppLem _
TransportVarSet-susp (ewf xs) ⟨ σ , t ⟩ = TransportVarSet-susp xs σ
TransportVarSet-susp (ewt xs) ⟨ σ , t ⟩ = begin
  TransportVarSet (suspSupp xs) (suspSub σ) ∪ FVTm (suspTm t)
    ≡⟨ cong (_∪ FVTm (suspTm t)) (trans (TransportVarSet-susp xs σ) (suspSuppEmpRight (TransportVarSet xs σ))) ⟩
  suspSupp (TransportVarSet xs σ) ∪ suspSupp empty ∪ FVTm (suspTm t)
    ≡⟨ ∪-assoc (suspSupp (TransportVarSet xs σ)) (suspSupp empty) (FVTm (suspTm t)) ⟩
  suspSupp (TransportVarSet xs σ) ∪ (suspSupp empty ∪ FVTm (suspTm t))
    ≡⟨ cong (suspSupp (TransportVarSet xs σ) ∪_) (suspSuppTm t) ⟩
  suspSupp (TransportVarSet xs σ) ∪ suspSupp (FVTm t)
    ≡⟨ suspSupp∪ (TransportVarSet xs σ) (FVTm t) ⟩
  suspSupp (TransportVarSet xs σ ∪ FVTm t) ∎
  where
    open ≡-Reasoning

suspSuppTyContainsEmpty : (A : Ty n) → suspSupp empty ⊆ FVTy (suspTy A)
suspSuppTyContainsEmpty ⋆ = ⊆-reflexive (sym (suspSuppLem _))
suspSuppTyContainsEmpty (s ─⟨ A ⟩⟶ t) = begin
  suspSupp empty
    ≤⟨ suspSuppTyContainsEmpty A ⟩
  FVTy (suspTy A)
    ≤⟨ ∪-⊆-1 (FVTy (suspTy A)) (FVTm (suspTm s)) ⟩
  FVTy (suspTy A) ∪ FVTm (suspTm s)
    ≤⟨ ∪-⊆-1 (FVTy (suspTy A) ∪ FVTm (suspTm s)) (FVTm (suspTm t)) ⟩
  FVTy (suspTy A) ∪ FVTm (suspTm s) ∪ FVTm (suspTm t) ∎
  where
    open PReasoning (⊆-poset _)

suspSuppTmContainsEmpty : (Γ : Ctx n) → (t : Tm n) → suspSupp empty ⊆ SuppTm (suspCtx Γ) (suspTm t)
suspSuppTmContainsEmpty Γ t = begin
  suspSupp empty
    ≤⟨ suspSuppTyContainsEmpty (tm-to-ty Γ t) ⟩
  FVTy (suspTy (tm-to-ty Γ t))
    ≤⟨ DC-⊆ (suspCtx Γ) (FVTy (suspTy (tm-to-ty Γ t))) ⟩
  SuppTy (suspCtx Γ) (suspTy (tm-to-ty Γ t))
    ≡⟨ cong (SuppTy (suspCtx Γ)) (≃ty-to-≡ (tm-to-ty-susp t Γ)) ⟩
  SuppTy (suspCtx Γ) (tm-to-ty (suspCtx Γ) (suspTm t))
    ≤⟨ SuppContainsType (suspTm t) (suspCtx Γ) ⟩
  SuppTm (suspCtx Γ) (suspTm t) ∎
  where
    open PReasoning (⊆-poset _)

DC-suspSupp : (Γ : Ctx n) → (xs : VarSet n) → DC (suspCtx Γ) (suspSupp xs) ≡ suspSupp (DC Γ xs)
DC-suspSupp ∅ emp = refl
DC-suspSupp (Γ , A) (ewf xs) = cong ewf (DC-suspSupp Γ xs)
DC-suspSupp (Γ , A) (ewt xs) = cong ewt (begin
  DC (suspCtx Γ) (suspSupp xs ∪ FVTy (suspTy A))
    ≡⟨ cong (DC (suspCtx Γ)) lem ⟩
  DC (suspCtx Γ) (suspSupp (xs ∪ FVTy A))
    ≡⟨ DC-suspSupp Γ (xs ∪ FVTy A) ⟩
  suspSupp (DC Γ (xs ∪ FVTy A)) ∎)
  where
    open ≡-Reasoning
    lem : suspSupp xs ∪ FVTy (suspTy A) ≡ suspSupp (xs ∪ FVTy A)
    lem = begin
      suspSupp xs ∪ FVTy (suspTy A)
        ≡⟨ cong (suspSupp xs ∪_) (suspSuppTy A) ⟩
      suspSupp xs ∪ suspSupp (FVTy A)
        ≡⟨ suspSupp∪ xs (FVTy A) ⟩
      suspSupp (xs ∪ FVTy A) ∎

suspSuppTm′ : (Γ : Ctx n) → (t : Tm n) → SuppTm (suspCtx Γ) (suspTm t) ≡ suspSupp (SuppTm Γ t)
suspSuppTm′ Γ t = begin
  SuppTm (suspCtx Γ) (suspTm t)
    ≡⟨ suspSuppTmContainsEmpty Γ t ⟩
  SuppTm (suspCtx Γ) (suspTm t) ∪ suspSupp empty
    ≡⟨ ∪-comm (DC (suspCtx Γ) (FVTm (suspTm t))) (suspSupp empty) ⟩
  suspSupp empty ∪ SuppTm (suspCtx Γ) (suspTm t)
    ≡˘⟨ cong (_∪ SuppTm (suspCtx Γ) (suspTm t)) (trans (DC-suspSupp Γ empty) (cong suspSupp (DC-empty Γ))) ⟩
  DC (suspCtx Γ) (suspSupp empty) ∪ DC (suspCtx Γ) (FVTm (suspTm t))
    ≡˘⟨ DC-cup (suspCtx Γ) (suspSupp empty) (FVTm (suspTm t)) ⟩
  DC (suspCtx Γ) (suspSupp empty ∪ FVTm (suspTm t))
    ≡⟨ cong (DC (suspCtx Γ)) (suspSuppTm t) ⟩
  DC (suspCtx Γ) (suspSupp (FVTm t))
    ≡⟨ DC-suspSupp Γ (FVTm t) ⟩
  suspSupp (SuppTm Γ t) ∎
  where
    open ≡-Reasoning

suspSuppTy′ : (Γ : Ctx n) → (A : Ty n) → SuppTy (suspCtx Γ) (suspTy A) ≡ suspSupp (SuppTy Γ A)
suspSuppTy′ Γ A = begin
  SuppTy (suspCtx Γ) (suspTy A)
    ≡⟨ cong (DC (suspCtx Γ)) (suspSuppTy A) ⟩
  DC (suspCtx Γ) (suspSupp (FVTy A))
    ≡⟨ DC-suspSupp Γ (FVTy A) ⟩
  suspSupp (SuppTy Γ A) ∎
  where
    open ≡-Reasoning

SuspSuppTmProp : (s t : Tm n) → SuppTm Γ s ≡ SuppTm Γ t → SuppTm (suspCtx Γ) (suspTm s) ≡ SuppTm (suspCtx Γ) (suspTm t)
SuspSuppTmProp {Γ = Γ} s t p = begin
  SuppTm (suspCtx Γ) (suspTm s)
    ≡⟨ suspSuppTm′ Γ s ⟩
  suspSupp (SuppTm Γ s)
    ≡⟨ cong suspSupp p ⟩
  suspSupp (SuppTm Γ t)
    ≡˘⟨ suspSuppTm′ Γ t ⟩
  SuppTm (suspCtx Γ) (suspTm t) ∎
  where
    open ≡-Reasoning

suspSuppCondition : {b : Bool} → {A : Ty (suc n)} → {Γ : Ctx (suc n)} → .⦃ pd : Γ ⊢pd ⦄ → supp-condition b A Γ → supp-condition b (suspTy A) (suspCtx Γ) ⦃ susp-pd it ⦄
suspSuppCondition {b = false} {A} {Γ} sc = begin
  SuppTy (suspCtx Γ) (suspTy A)
    ≡⟨ suspSuppTy′ Γ A ⟩
  suspSupp (SuppTy Γ A)
    ≡⟨ cong suspSupp sc ⟩
  suspSupp full
    ≡⟨ suspSuppFull ⟩
  full ∎
  where
    open ≡-Reasoning
suspSuppCondition {b = true} {s ─⟨ A ⟩⟶ t} {Γ} ⦃ pd ⦄ (nz ,, sc1 ,, sc2) = NonZero-subst (sym (susp-ctx-dim Γ)) it ,, l1 ,, l2
  where
    instance _ = nz
    instance _ = susp-pd {Γ = Γ} (recompute (pd-dec Γ) it)
    open ≡-Reasoning

    l3 : suc (pred (ctx-dim Γ)) ≡ pred (ctx-dim (suspCtx Γ))
    l3 = begin
      suc (pred (ctx-dim Γ))
        ≡⟨ suc-pred (ctx-dim Γ) ⟩
      ctx-dim Γ
        ≡˘⟨ cong pred (susp-ctx-dim Γ) ⟩
      pred (ctx-dim (suspCtx Γ)) ∎

    l1 : SuppTm (suspCtx Γ) (suspTm s) ≡ pd-bd-supp (pred (ctx-dim (suspCtx Γ))) (suspCtx Γ) false
    l1 = begin
      SuppTm (suspCtx Γ) (suspTm s)
        ≡⟨ suspSuppTm′ Γ s ⟩
      suspSupp (SuppTm Γ s)
        ≡⟨ cong suspSupp sc1 ⟩
      suspSupp (pd-bd-supp (pred (ctx-dim Γ)) Γ false)
        ≡⟨ susp-pd-bd-compat (pred (ctx-dim Γ)) Γ false ⟩
      pd-bd-supp (suc (pred (ctx-dim Γ))) (suspCtx Γ) false
        ≡⟨ cong (λ x → pd-bd-supp x (suspCtx Γ) false) l3 ⟩
      pd-bd-supp (pred (ctx-dim (suspCtx Γ))) (suspCtx Γ) false ∎

    l2 : SuppTm (suspCtx Γ) (suspTm t) ≡ pd-bd-supp (pred (ctx-dim (suspCtx Γ))) (suspCtx Γ) true
    l2 = begin
      SuppTm (suspCtx Γ) (suspTm t)
        ≡⟨ suspSuppTm′ Γ t ⟩
      suspSupp (SuppTm Γ t)
        ≡⟨ cong suspSupp sc2 ⟩
      suspSupp (pd-bd-supp (pred (ctx-dim Γ)) Γ true)
        ≡⟨ susp-pd-bd-compat (pred (ctx-dim Γ)) Γ true ⟩
      pd-bd-supp (suc (pred (ctx-dim Γ))) (suspCtx Γ) true
        ≡⟨ cong (λ x → pd-bd-supp x (suspCtx Γ) true) l3 ⟩
      pd-bd-supp (pred (ctx-dim (suspCtx Γ))) (suspCtx Γ) true ∎
