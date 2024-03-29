module Deprecated.Tree.Structured.Support.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Wedge.Support
open import Deprecated.Tree.Support
open import Deprecated.Tree.Structured.Support

open import Algebra.Bundles
open import Algebra.Definitions
open import Tactic.MonoidSolver

FVLabel-WT-⋆ : (L : Label X S) → FVLabel-WT (L ,, S⋆) ≡ FVLabel L
FVLabel-WT-⋆ L = ∪m-left-unit (FVLabel L)

FVLabel′-map : {X : MaybeTree n}
             → {Y : MaybeTree m}
             → (f : (P : Path S) → MVarSet X)
             → (g : MVarSet X → MVarSet Y)
             → (∀ xs ys → g (xs ∪m ys) ≡ g xs ∪m g ys)
             → FVLabel′ (g ∘ f) ≡ g (FVLabel′ f)
FVLabel′-map {S = Sing} f g p = refl
FVLabel′-map {S = Join S T} f g p = begin
  g (f PHere) ∪m FVLabel′ (g ∘ f ∘ PExt) ∪m FVLabel′ (g ∘ f ∘ PShift)
    ≡⟨ cong₂ (λ a b → g (f PHere) ∪m a ∪m b) (FVLabel′-map (f ∘ PExt) g p) (FVLabel′-map (f ∘ PShift) g p) ⟩
  g (f PHere) ∪m g (FVLabel′ (f ∘ PExt)) ∪m g (FVLabel′ (f ∘ PShift))
    ≡˘⟨ cong (_∪m g (FVLabel′ (f ∘ PShift))) (p (f PHere) (FVLabel′ (f ∘ PExt))) ⟩
  g (f PHere ∪m FVLabel′ (f ∘ PExt)) ∪m g (FVLabel′ (f ∘ PShift))
    ≡˘⟨ p (f PHere ∪m FVLabel′ (f ∘ PExt)) (FVLabel′ (f ∘ PShift)) ⟩
  g (f PHere ∪m FVLabel′ (f ∘ PExt) ∪m FVLabel′ (f ∘ PShift)) ∎
  where
    open ≡-Reasoning

label-ap-⊆ : {X : MaybeTree n} → (L : Label X S) → (P : Path S) → FVLabel L ≡ FVLabel L ∪m FVSTm (L P)
label-ap-⊆ {S = Sing} L PHere = sym (∪m-idem (FVSTm (L PHere)))
label-ap-⊆ {S = Join S T} {X = X} L PHere = begin
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)
    ≡˘⟨ cong (λ - → - ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)) (∪m-idem (FVSTm (L PHere))) ⟩
  (FVSTm (L PHere) ∪m FVSTm (L PHere)) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  FVSTm (L PHere) ∪m (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift))
    ≡⟨ ∪m-comm (FVSTm (L PHere)) _ ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift) ∪m FVSTm (L PHere) ∎
  where
    open ≡-Reasoning
label-ap-⊆ {S = Join S T} {X = X} L (PExt P) = begin
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)
    ≡⟨ cong (λ x → FVSTm (L PHere) ∪m x ∪m FVLabel (L ∘ PShift)) (label-ap-⊆ (L ∘ PExt) P) ⟩
  FVSTm (L PHere) ∪m (FVLabel (L ∘ PExt) ∪m FVSTm (L (PExt P))) ∪m FVLabel (L ∘ PShift)
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m (FVSTm (L (PExt P)) ∪m FVLabel (L ∘ PShift))
    ≡⟨ cong (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m_) (∪m-comm _ _) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m (FVLabel (L ∘ PShift) ∪m FVSTm (L (PExt P)))
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift) ∪m FVSTm (L (PExt P)) ∎
  where
    open ≡-Reasoning
label-ap-⊆ {S = Join S T} {X = X} L (PShift P) = begin
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)
    ≡⟨ cong (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m_) (label-ap-⊆ (L ∘ PShift) P) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m (FVLabel (L ∘ PShift) ∪m FVSTm (L (PShift P)))
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift) ∪m FVSTm (L (PShift P)) ∎
  where
    open ≡-Reasoning

FVLabel-non-empty : (L : Label (someTree T) S) → Truth (tvarset-non-empty (FVLabel L))
FVSTm-non-empty : (a : STm (someTree S)) → Truth (tvarset-non-empty (FVSTm a))

FVLabel-non-empty {S = Sing} L = FVSTm-non-empty (L PHere)
FVLabel-non-empty {S = Join S T} L = tvarset-non-empty-∪t-left (FVSTm (L PHere) ∪t FVLabel (L ∘ PExt)) (FVLabel (L ∘ PShift))
                                       (tvarset-non-empty-∪t-left (FVSTm (L PHere)) (FVLabel (L ∘ PExt)) (FVSTm-non-empty (L PHere)))

FVSTm-non-empty (SCoh S A L) = tvarset-non-empty-∪t-right (FVSTy (lty L)) (FVLabel (ap L)) (FVLabel-non-empty (ap L))
FVSTm-non-empty {S = Join S T} (SExt a) = Truth-left (tvarset-non-empty (FVSTm a)) (tvarset-non-empty (tEmp {S = T})) (FVSTm-non-empty a)
FVSTm-non-empty {S = Join S T} (SShift a) = Truth-right (tvarset-non-empty (tEmp {S = S})) (tvarset-non-empty (FVSTm a))
                                              (FVSTm-non-empty a)
FVSTm-non-empty (SPath P) = fromPath-non-empty P

MtoVarSet-∪m : {ΓS : CtxOrTree n} (xs ys : MVarSet (COT-to-MT ΓS)) → MtoVarSet ΓS (xs ∪m ys) ≡ MtoVarSet ΓS xs ∪ MtoVarSet ΓS ys
MtoVarSet-∪m {ΓS = incTree x} xs ys = toVarSet-∪t xs ys
MtoVarSet-∪m {ΓS = incCtx Γ} xs ys = DC-∪ Γ xs ys

MtoVarSet-emp : (ΓS : CtxOrTree n) → MtoVarSet ΓS mEmp ≡ empty
MtoVarSet-emp (incTree S) = toVarSet-emp S
MtoVarSet-emp (incCtx Γ) = DC-empty Γ

open ≡-Reasoning

DCM-toVarSet : (xs : MVarSet (COT-to-MT ΓS)) → MtoVarSet ΓS (DCM ΓS xs) ≡ MtoVarSet ΓS xs
DCM-toVarSet {ΓS = incTree S} xs = DCT-toVarSet xs
DCM-toVarSet {ΓS = incCtx Γ} xs = DC-idem Γ xs

fromPath-to-term : (P : Path S) → toVarSet (fromPath P) ≡ SuppTm ⌊ S ⌋ (path-to-term P)
fromPath-to-term {S = S} PHere = begin
  toVarSet (fromPath (PHere {S = S}))
    ≡⟨ fromPath-PHere S ⟩
  trueAt (fromℕ _)
    ≡˘⟨ DC-fromℕ ⌊ S ⌋ ⟩
  SuppTm ⌊ S ⌋ (Var (fromℕ _)) ∎
fromPath-to-term {S = Join S T} (PExt P) rewrite Truth-prop (fromPath-non-empty P) = begin
  wedge-susp-vs (susp-vs (toVarSet (fromPath P))) (toVarSet (tEmp {S = T}))
    ≡⟨ cong₂ (λ x y → wedge-susp-vs (susp-vs x) y) (fromPath-to-term P) (toVarSet-emp T) ⟩
  wedge-susp-vs (susp-vs (SuppTm ⌊ S ⌋ (path-to-term P))) empty
    ≡⟨ wedge-susp-vs-ext ⌊ S ⌋ (path-to-term P) ⌊ T ⌋ ⟩
  SuppTm (⌊ Join S T ⌋) (susp-tm (path-to-term P) [ wedge-susp-inc-left _ _ ]tm) ∎
fromPath-to-term {S = Join S T} (PShift P) rewrite Truth-not-prop (tvarset-empty S) = begin
  wedge-susp-vs empty (toVarSet (fromPath P))
    ≡⟨ cong (wedge-susp-vs empty) (fromPath-to-term P) ⟩
  wedge-susp-vs empty (SuppTm ⌊ T ⌋ (path-to-term P))
    ≡⟨ wedge-susp-vs-shift ⌊ S ⌋ ⌊ T ⌋ (path-to-term P) ⟩
  SuppTm (wedge-susp ⌊ S ⌋ ⌊ T ⌋) (path-to-term P [ wedge-susp-inc-right _ _ ]tm) ∎

FVSTm-to-term : {ΓS : CtxOrTree n} → (a : STm (COT-to-MT ΓS)) → MtoVarSet ΓS (FVSTm a) ≡ SuppTm (COT-to-Ctx ΓS) (stm-to-term a)
FVSTy-to-type : {ΓS : CtxOrTree n} → (A : STy (COT-to-MT ΓS)) → MtoVarSet ΓS (FVSTy A) ≡ SuppTy (COT-to-Ctx ΓS) (sty-to-type A)
FVLabel-to-sub : {ΓS : CtxOrTree n} → (L : Label-WT (COT-to-MT ΓS) S) → MtoVarSet ΓS (FVLabel-WT L) ≡ SuppSub (COT-to-Ctx ΓS) (label-to-sub L)
FVLabel-to-sub′ : {ΓS : CtxOrTree n}
                → (L : Label-WT (COT-to-MT ΓS) S)
                → ((P : Path S)
                → MtoVarSet ΓS (FVSTm (ap L P)) ≡ SuppTm (COT-to-Ctx ΓS) (stm-to-term (ap L P)))
                → (MtoVarSet ΓS (FVSTy (lty L)) ≡ SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty L)))
                → MtoVarSet ΓS (FVLabel-WT L) ≡ SuppSub (COT-to-Ctx ΓS) (label-to-sub L)

FVSTm-to-term {ΓS = incTree x} (SPath P) = fromPath-to-term P
FVSTm-to-term {ΓS = incTree x} (SCoh S A L) = begin
  toVarSet (FVLabel-WT L)
    ≡⟨ FVLabel-to-sub L ⟩
  SuppSub ⌊ x ⌋ (label-to-sub L)
    ≡˘⟨ cong (DC ⌊ x ⌋) (coh-sub-fv ⌊ S ⌋ (sty-to-type A) (label-to-sub L)) ⟩
  SuppTm ⌊ x ⌋ (Coh ⌊ S ⌋ (sty-to-type A) idSub [ label-to-sub L ]tm) ∎
FVSTm-to-term {ΓS = incCtx Γ} (SCoh S A L) = begin
  DC Γ (FVLabel-WT L)
    ≡⟨ FVLabel-to-sub L ⟩
  SuppSub Γ (label-to-sub L)
    ≡˘⟨ cong (DC Γ) (coh-sub-fv ⌊ S ⌋ (sty-to-type A) (label-to-sub L)) ⟩
  SuppTm Γ (Coh ⌊ S ⌋ (sty-to-type A) idSub [ label-to-sub L ]tm) ∎
FVSTm-to-term {ΓS = incCtx _} (SOther t) = refl
FVSTm-to-term {ΓS = incTree (Join S T)} (SExt a) rewrite Truth-prop (FVSTm-non-empty a) = begin
  wedge-susp-vs (susp-vs (toVarSet (FVSTm a))) (toVarSet (tEmp {S = T}))
    ≡⟨ cong₂ (λ x y → wedge-susp-vs (susp-vs x) y) (FVSTm-to-term a) (toVarSet-emp T) ⟩
  wedge-susp-vs (susp-vs (SuppTm ⌊ S ⌋ (stm-to-term a))) empty
    ≡⟨ wedge-susp-vs-ext ⌊ S ⌋ (stm-to-term a) ⌊ T ⌋ ⟩
  SuppTm ⌊ Join S T ⌋ (susp-tm (stm-to-term a) [ wedge-susp-inc-left _ _ ]tm) ∎
FVSTm-to-term {ΓS = incTree (Join S T)} (SShift a) rewrite Truth-not-prop (tvarset-empty S) = begin
  wedge-susp-vs empty (toVarSet (FVSTm a))
    ≡⟨ cong (wedge-susp-vs empty) (FVSTm-to-term a) ⟩
  wedge-susp-vs empty (SuppTm ⌊ T ⌋ (stm-to-term a))
    ≡⟨ wedge-susp-vs-shift ⌊ S ⌋ ⌊ T ⌋ (stm-to-term a)  ⟩
  SuppTm ⌊ Join S T ⌋ (stm-to-term a [ wedge-susp-inc-right _ _ ]tm) ∎

FVSTy-to-type {ΓS = ΓS} S⋆ = trans (MtoVarSet-emp ΓS) (sym (DC-empty (COT-to-Ctx ΓS)))
FVSTy-to-type {ΓS = ΓS} (SArr s A t) = begin
  MtoVarSet ΓS (FVSTy A ∪m FVSTm s ∪m FVSTm t)
    ≡⟨ MtoVarSet-∪m (FVSTy A ∪m FVSTm s) (FVSTm t) ⟩
  MtoVarSet ΓS (FVSTy A ∪m FVSTm s) ∪ MtoVarSet ΓS (FVSTm t)
    ≡⟨ cong₂ _∪_ (MtoVarSet-∪m (FVSTy A) (FVSTm s)) (FVSTm-to-term t) ⟩
  MtoVarSet ΓS (FVSTy A) ∪ MtoVarSet ΓS (FVSTm s) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)
    ≡⟨ cong₂ (λ x y → x ∪ y ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)) (FVSTy-to-type A) (FVSTm-to-term s) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type A) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term s) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)
    ≡˘⟨ cong (_∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)) (DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type A)) (FVTm (stm-to-term s))) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type A) ∪ FVTm (stm-to-term s)) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)
    ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type A) ∪ FVTm (stm-to-term s)) (FVTm (stm-to-term t)) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type A) ∪ FVTm (stm-to-term s) ∪ FVTm (stm-to-term t)) ∎

FVLabel-to-sub L = FVLabel-to-sub′ L (λ P → FVSTm-to-term (ap L P)) (FVSTy-to-type (lty L))

FVLabel-to-sub′ {S = Sing} {ΓS = ΓS} L f g = begin
   MtoVarSet ΓS (FVSTy (lty L) ∪m FVSTm (ap L PHere))
    ≡⟨ MtoVarSet-∪m (FVSTy (lty L)) (FVSTm (ap L PHere)) ⟩
  MtoVarSet ΓS (FVSTy (lty L)) ∪ MtoVarSet ΓS (FVSTm (ap L PHere))
    ≡⟨ cong₂ _∪_ g (f PHere) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type (proj₂ L))) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (proj₁ L PHere))
    ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L))) (FVTm (stm-to-term (ap L PHere))) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L)) ∪ FVTm (stm-to-term (ap L PHere))) ∎
FVLabel-to-sub′ {S = Join S T} {ΓS = ΓS} L f g = begin
  MtoVarSet ΓS (FVSTy (lty L) ∪m ((FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt)) ∪m FVLabel (ap L ∘ PShift)))
    ≡⟨ cong (MtoVarSet ΓS) l1 ⟩
  MtoVarSet ΓS
    (FVSTy (lty L)
    ∪m FVSTm (ap L PHere)
    ∪m FVSTm (ap L (PShift PHere))
    ∪m FVLabel (ap L ∘ PExt)
    ∪m (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift)))
    ≡⟨ MtoVarSet-∪m (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
               ∪m FVLabel (ap L ∘ PExt)) (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift)) ⟩
  MtoVarSet ΓS (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
               ∪m FVLabel (ap L ∘ PExt))
  ∪ MtoVarSet ΓS (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift))
    ≡⟨⟩
  MtoVarSet ΓS (FVLabel-WT (label₁ L)) ∪ MtoVarSet ΓS (FVLabel-WT (label₂ L))
    ≡⟨ cong₂ _∪_ (FVLabel-to-sub′ (label₁ L) (f ∘ PExt) l2) (FVLabel-to-sub′ (label₂ L) (f ∘ PShift) g) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₁ L)) ∪ SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₂ L))
    ≡˘⟨ cong (λ x → DC (COT-to-Ctx ΓS) x ∪ SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₂ L))) (↓-fv (label-to-sub (label₁ L))) ⟩
  SuppSub (COT-to-Ctx ΓS) (↓ (label-to-sub (label₁ L))) ∪ SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₂ L))
    ≡˘⟨ sub-from-wedge-vs′ (↓ (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) l3 ⟩
  SuppSub (COT-to-Ctx ΓS)
          (sub-from-wedge (↓ (label-to-sub (label₁ L)))
                          (label-to-sub (label₂ L))) ∎
  where
    l1 : FVSTy (lty L) ∪m ((FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt)) ∪m FVLabel (ap L ∘ PShift))
       ≡ FVSTy (lty L)
       ∪m FVSTm (ap L PHere)
       ∪m FVSTm (ap L (PShift PHere))
       ∪m FVLabel (ap L ∘ PExt)
       ∪m (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift))
    l1 = begin
      FVSTy (lty L) ∪m (FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt) ∪m FVLabel (ap L ∘ PShift))
        ≡⟨ cong (λ - → FVSTy (lty L) ∪m (FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt) ∪m -)) (label-ap-⊆ (ap L ∘ PShift) PHere) ⟩
      FVSTy (lty L) ∪m (FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt) ∪m (FVLabel (ap L ∘ PShift) ∪m FVSTm (ap L (PShift PHere))))
        ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
      FVSTy (lty L)
      ∪m FVSTm (ap L PHere)
      ∪m ((FVLabel (ap L ∘ PExt) ∪m FVLabel (ap L ∘ PShift) )∪m FVSTm (ap L (PShift PHere)))
        ≡˘⟨ cong₂ (λ x y → x ∪m FVSTm (ap L PHere) ∪m y)
                 (∪m-idem (FVSTy (lty L)))
                 (∪m-comm _ _) ⟩
      (FVSTy (lty L) ∪m FVSTy (lty L))
      ∪m FVSTm (ap L PHere)
      ∪m (FVSTm (ap L (PShift PHere)) ∪m (FVLabel (ap L ∘ PExt) ∪m FVLabel (ap L ∘ PShift)))
        ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
      FVSTy (lty L) ∪m (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
      ∪m FVLabel (ap L ∘ PExt)) ∪m FVLabel (ap L ∘ PShift)
        ≡⟨ cong (_∪m FVLabel (ap L ∘ PShift)) (∪m-comm (FVSTy (lty L)) _) ⟩
      (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
      ∪m FVLabel (ap L ∘ PExt))
      ∪m FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift)
        ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
      FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
      ∪m FVLabel (ap L ∘ PExt)
      ∪m (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift)) ∎

    l2 : MtoVarSet ΓS (FVSTy (lty (label₁ L))) ≡ SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty (label₁ L)))
    l2 = begin
      MtoVarSet ΓS (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere)))
        ≡⟨ MtoVarSet-∪m (FVSTy (lty L) ∪m FVSTm (ap L PHere)) (FVSTm (ap L (PShift PHere))) ⟩
      MtoVarSet ΓS (FVSTy (lty L) ∪m FVSTm (ap L PHere)) ∪ MtoVarSet ΓS (FVSTm (ap L (PShift PHere)))
        ≡⟨ cong (_∪m MtoVarSet ΓS (FVSTm (ap L (PShift PHere)))) (MtoVarSet-∪m (FVSTy (lty L)) (FVSTm (ap L PHere))) ⟩
      MtoVarSet ΓS (FVSTy (lty L)) ∪ MtoVarSet ΓS (FVSTm (ap L PHere)) ∪m MtoVarSet ΓS (FVSTm (ap L (PShift PHere)))
        ≡⟨ cong₃ (λ x y z → x ∪ y ∪ z) g (f PHere) (f (PShift PHere)) ⟩
      SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty L))
      ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (ap L PHere))
      ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (ap L (PShift PHere)))
        ≡˘⟨ cong (_∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (proj₁ L (PShift PHere))))
              (DC-∪ (COT-to-Ctx ΓS) _ _) ⟩
      DC (COT-to-Ctx ΓS) (FVTy (sty-to-type (proj₂ L)) ∪ FVTm (stm-to-term (proj₁ L PHere))) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (proj₁ L (PShift PHere)))
        ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) _ _ ⟩
      SuppTy (COT-to-Ctx ΓS)
      (stm-to-term (ap L PHere) ─⟨ sty-to-type (lty L) ⟩⟶
       stm-to-term (ap L (PShift PHere))) ∎

    l3 : SuppTm (COT-to-Ctx ΓS) (Var (fromℕ _) [ label-to-sub (label₂ L) ]tm) ⊆ SuppSub (COT-to-Ctx ΓS) (↓ (label-to-sub (label₁ L)))
    l3 = PR.begin
      SuppTm (COT-to-Ctx ΓS) (Var (fromℕ _) [ label-to-sub (label₂ L) ]tm)
        ≈˘⟨ cong (DC (COT-to-Ctx ΓS)) (FVTm-≃ (label-to-sub-lem L)) ⟩
      SuppTm (COT-to-Ctx ΓS) (get-snd [ ↓ (label-to-sub (label₁ L)) ]tm)
        ≤⟨ DC-cong-⊆ (COT-to-Ctx ΓS) (FVTm-comp-⊆ get-snd (↓ (label-to-sub (label₁ L)))) ⟩
      SuppSub (COT-to-Ctx ΓS) (↓ (label-to-sub (label₁ L))) PR.∎
      where
        module PR = PReasoning (⊆-poset _)
        open PR

supp-condition-compat : (b : Bool) → (S : Tree n) → (As : STy (someTree S)) → supp-condition-s b S As → supp-condition b (sty-to-type As) ⌊ S ⌋
supp-condition-compat false S As sc = begin
  SuppTy ⌊ S ⌋ (sty-to-type As)
    ≡˘⟨ FVSTy-to-type As ⟩
  toVarSet (FVSTy As)
    ≡˘⟨ DCT-toVarSet (FVSTy As) ⟩
  toVarSet (DCT (FVSTy As))
    ≡⟨ cong toVarSet sc ⟩
  toVarSet (tFull {S = S})
    ≡⟨ toVarSet-full S ⟩
  full ∎
supp-condition-compat true S (SArr s As t) (nz ,, sc1 ,, sc2) = tree-to-pd S ,, NonZero-subst lem nz ,, lem1 ,, lem2
  where
    lem : tree-dim S ≡ ctx-dim ⌊ S ⌋
    lem = sym (tree-dim-ctx-dim S)

    instance _ = tree-to-pd S
    lem1 : SuppTm ⌊ S ⌋ (stm-to-term s)
         ≡ pd-bd-vs (pred (ctx-dim ⌊ S ⌋)) ⌊ S ⌋ false
    lem1 = begin
      SuppTm ⌊ S ⌋ (stm-to-term s)
        ≡˘⟨ FVSTm-to-term s ⟩
      toVarSet (FVSTm s)
        ≡˘⟨ DCT-toVarSet (FVSTm s) ⟩
      toVarSet (DCT (FVSTm s))
        ≡⟨ cong toVarSet sc1 ⟩
      toVarSet (tree-bd-vs (pred (tree-dim S)) S false)
        ≡⟨ cong (λ - → toVarSet (tree-bd-vs (pred -) S false)) lem  ⟩
      toVarSet (tree-bd-vs (pred (ctx-dim ⌊ S ⌋)) S false)
        ≡⟨ supp-compat′ (pred (ctx-dim ⌊ S ⌋)) S false ⟩
      pd-bd-vs (pred (ctx-dim ⌊ S ⌋)) ⌊ S ⌋ false ∎

    lem2 : SuppTm ⌊ S ⌋ (stm-to-term t)
         ≡ pd-bd-vs (pred (ctx-dim ⌊ S ⌋)) ⌊ S ⌋ true
    lem2 = begin
      SuppTm ⌊ S ⌋ (stm-to-term t)
        ≡˘⟨ FVSTm-to-term t ⟩
      toVarSet (FVSTm t)
        ≡˘⟨ DCT-toVarSet (FVSTm t) ⟩
      toVarSet (DCT (FVSTm t))
        ≡⟨ cong toVarSet sc2 ⟩
      toVarSet (tree-bd-vs (pred (tree-dim S)) S true)
        ≡⟨ cong (λ - → toVarSet (tree-bd-vs (pred -) S true)) lem  ⟩
      toVarSet (tree-bd-vs (pred (ctx-dim ⌊ S ⌋)) S true)
        ≡⟨ supp-compat′ (pred (ctx-dim ⌊ S ⌋)) S true ⟩
      pd-bd-vs (pred (ctx-dim ⌊ S ⌋)) ⌊ S ⌋ true ∎

DCM-reflect : {xs ys : MVarSet (COT-to-MT ΓS)} → MtoVarSet ΓS xs ≡ MtoVarSet ΓS ys → DCM ΓS xs ≡ DCM ΓS ys
DCM-reflect {ΓS = incTree x} p = DCT-reflect p
DCM-reflect {ΓS = incCtx x} p = p

DCM-∪ : (ΓS : CtxOrTree n) → (xs ys : MVarSet (COT-to-MT ΓS)) → DCM ΓS (xs ∪m ys) ≡ DCM ΓS xs ∪m DCM ΓS ys
DCM-∪ (incTree x) xs ys = DCT-∪ xs ys
DCM-∪ (incCtx x) xs ys = DC-∪ x xs ys

FVSTm-≃ : {a b : STm (COT-to-MT ΓS)} → a ≃stm b → DCM ΓS (FVSTm a) ≡ DCM ΓS (FVSTm b)
FVSTm-≃ {ΓS = ΓS} {a = a} {b = b} [ p ] = DCM-reflect (begin
  MtoVarSet ΓS (FVSTm a)
    ≡⟨ FVSTm-to-term a ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term a)
    ≡⟨ cong (SuppTm (COT-to-Ctx ΓS)) (≃tm-to-≡ p) ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term b)
    ≡˘⟨ FVSTm-to-term b ⟩
  MtoVarSet ΓS (FVSTm b) ∎)

FVSTy-≃ : {As Bs : STy (COT-to-MT ΓS)} → As ≃sty Bs → DCM ΓS (FVSTy As) ≡ DCM ΓS (FVSTy Bs)
FVSTy-≃ {ΓS = ΓS} {As = As} {Bs = Bs} [ p ] = DCM-reflect (begin
  MtoVarSet ΓS (FVSTy As)
    ≡⟨ FVSTy-to-type As ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type As)
    ≡⟨ cong (SuppTy (COT-to-Ctx ΓS)) (≃ty-to-≡ p) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type Bs)
    ≡˘⟨ FVSTy-to-type Bs ⟩
  MtoVarSet ΓS (FVSTy Bs) ∎)

FVLabel-≃ : {L M : Label (COT-to-MT ΓS) S} → L ≃l M → DCM ΓS (FVLabel L) ≡ DCM ΓS (FVLabel M)
FVLabel-≃ {S = Sing} {L = L} {M = M} [ p ] = FVSTm-≃ (p PHere)
FVLabel-≃ {ΓS = ΓS} {S = Join S T} {L = L} {M = M} [ p ] = begin
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift))
    ≡⟨ DCM-∪ ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) (FVLabel (λ x → L (PShift x))) ⟩
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt)) ∪m DCM ΓS (FVLabel (L ∘ PShift))
    ≡⟨ cong₂ _∪m_ (DCM-∪ ΓS (FVSTm (L PHere)) (FVLabel (L ∘ PExt))) (FVLabel-≃ [ p ∘ PShift ]) ⟩
  DCM ΓS (FVSTm (L PHere)) ∪m DCM ΓS (FVLabel (L ∘ PExt)) ∪m DCM ΓS (FVLabel (M ∘ PShift))
    ≡⟨ cong₂ (λ a b → a ∪m b ∪m DCM ΓS (FVLabel (M ∘ PShift))) (FVSTm-≃ (p PHere)) (FVLabel-≃ [ p ∘ PExt ]) ⟩
  DCM ΓS (FVSTm (M PHere)) ∪m DCM ΓS (FVLabel (M ∘ PExt)) ∪m DCM ΓS (FVLabel (M ∘ PShift))
    ≡˘⟨ cong (_∪m DCM ΓS (FVLabel (M ∘ PShift))) (DCM-∪ ΓS (FVSTm (M PHere)) (FVLabel (M ∘ PExt))) ⟩
  DCM ΓS (FVSTm (M PHere) ∪m FVLabel (M ∘ PExt)) ∪m DCM ΓS (FVLabel (M ∘ PShift))
    ≡˘⟨ DCM-∪ ΓS (FVSTm (M PHere) ∪m FVLabel (M ∘ PExt)) (FVLabel (M ∘ PShift)) ⟩
  DCM ΓS (FVSTm (M PHere) ∪m FVLabel (M ∘ PExt) ∪m FVLabel (M ∘ PShift)) ∎

FVLabel-WT-≃ : {L M : Label-WT (COT-to-MT ΓS) S} → ap L ≃l ap M → lty L ≃sty lty M → DCM ΓS (FVLabel-WT L) ≡ DCM ΓS (FVLabel-WT M)
FVLabel-WT-≃ {ΓS = ΓS} {L = L} {M = M} p q = begin
  DCM ΓS (FVSTy (lty L) ∪m FVLabel (ap L))
    ≡⟨ DCM-∪ ΓS (FVSTy (lty L)) (FVLabel (ap L)) ⟩
  DCM ΓS (FVSTy (lty L)) ∪m DCM ΓS (FVLabel (ap L))
    ≡⟨ cong₂ _∪m_ (FVSTy-≃ q) (FVLabel-≃ p) ⟩
  DCM ΓS (FVSTy (lty M)) ∪m DCM ΓS (FVLabel (ap M))
    ≡˘⟨ DCM-∪ ΓS (FVSTy (lty M)) (FVLabel (ap M)) ⟩
  DCM ΓS (FVSTy (lty M) ∪m FVLabel (ap M)) ∎

FVSTm-susp : (a : STm (someTree S)) → susp-tvarset (DCT (FVSTm a)) ≡ DCT (FVSTm (susp-stm a))
FVSTm-susp {S = S} a rewrite Truth-prop (FVSTm-non-empty a) = refl

id-label-full : (S : Tree n) → FVLabel (id-label S) ≡ tFull
id-label-full Sing = refl
id-label-full (Join S T) = begin
  VSJoin true tEmp tEmp ∪t
      FVLabel′ (λ x → VSJoin false (fromPath x) tEmp)
      ∪t FVLabel′ (λ x → VSJoin false tEmp (fromPath x))
    ≡⟨ cong₂ (λ a b → VSJoin true tEmp tEmp ∪t a ∪t b) (FVLabel′-map fromPath (λ x → VSJoin false x tEmp) λ xs ys → cong (VSJoin false (xs ∪t ys)) (sym (∪t-left-unit tEmp))) (FVLabel′-map fromPath (VSJoin false tEmp) λ xs ys → cong (λ x → VSJoin false x (xs ∪t ys)) (sym (∪t-left-unit tEmp))) ⟩
  VSJoin true tEmp tEmp ∪t VSJoin false (FVLabel′ fromPath) tEmp ∪t VSJoin false tEmp (FVLabel′ fromPath)
    ≡⟨ cong₂ (VSJoin true) (trans (∪t-right-unit (tEmp ∪t FVLabel′ fromPath)) (∪t-left-unit (FVLabel (id-label S)))) (trans (cong (_∪t FVLabel (id-label T)) (∪t-left-unit tEmp)) (∪t-left-unit (FVLabel (id-label T)))) ⟩
  VSJoin true (FVLabel (id-label S)) (FVLabel (id-label T))
    ≡⟨ cong₂ (VSJoin true) (id-label-full S) (id-label-full T) ⟩
  VSJoin true tFull tFull
    ≡⟨⟩
  tFull ∎

id-label-wt-full : (S : Tree n) → FVLabel-WT (id-label-wt S) ≡ tFull
id-label-wt-full S = begin
  FVLabel-WT (id-label-wt S)
    ≡⟨ FVLabel-WT-⋆ (id-label S) ⟩
  FVLabel (id-label S)
    ≡⟨ id-label-full S ⟩
  tFull ∎

ppath-≃-full : (p : S ≃′ T) → FVLabel (SPath ∘ ppath-≃ p) ≡ tFull
ppath-≃-full {S = S} Refl≃′ = id-label-full S
ppath-≃-full (Join≃′ {S′ = S′} {T′ = T′} p q) = begin
  VSJoin true tEmp tEmp
  ∪t FVLabel′ (λ x → VSJoin false (fromPath (ppath-≃ p x)) tEmp)
  ∪t FVLabel′ (λ x → VSJoin false tEmp (fromPath (ppath-≃ q x)))
    ≡⟨ cong₂ (λ a b → VSJoin true tEmp tEmp ∪t a ∪t b) (FVLabel′-map (fromPath ∘ ppath-≃ p) (λ x → VSJoin false x tEmp) (λ xs ys → cong (VSJoin false (xs ∪t ys)) (sym (∪t-left-unit tEmp)))) (FVLabel′-map (fromPath ∘ ppath-≃ q) (VSJoin false tEmp) (λ xs ys → cong (λ x → VSJoin false x (xs ∪t ys)) (sym (∪t-left-unit tEmp)))) ⟩
  VSJoin true tEmp tEmp ∪t
    VSJoin false (FVLabel′ (λ x → fromPath (ppath-≃ p x))) tEmp
    ∪t VSJoin false tEmp (FVLabel′ (λ x → fromPath (ppath-≃ q x)))
    ≡⟨ cong₂ (VSJoin true) (solve (∪t-monoid {S = S′})) (solve (∪t-monoid {S = T′})) ⟩
  VSJoin true (FVLabel (SPath ∘ ppath-≃ p)) (FVLabel (SPath ∘ ppath-≃ q))
    ≡⟨ cong₂ (VSJoin true) (ppath-≃-full p) (ppath-≃-full q) ⟩
  tFull ∎

++t-incs-full : (S : Tree n) → (T : Tree m) → FVLabel (ap (++t-inc-left S T)) ∪m FVLabel (ap (++t-inc-right S T)) ≡ tFull
++t-incs-full Sing T = begin
  fromPath PHere ∪t FVLabel (id-label T)
    ≡⟨ cong (fromPath PHere ∪t_) (id-label-full T) ⟩
  fromPath PHere ∪t tFull
    ≡⟨ ∪t-right-zero (fromPath PHere) ⟩
  tFull ∎
++t-incs-full (Join S₁ S₂) T = begin
  VSJoin true tEmp tEmp ∪t
      FVLabel′ (λ x → VSJoin false (fromPath x) tEmp)
      ∪t
      FVLabel′
      (λ x →
         VSJoin false tEmp (fromPath (++t-inc-left′ S₂ T x)))
      ∪t
      FVLabel′
      (λ P →
         VSJoin false tEmp (fromPath (++t-inc-right′ S₂ T P)))
    ≡⟨ cong₃ (λ a b c → VSJoin true tEmp tEmp ∪t a ∪t b ∪t c)
             (FVLabel′-map fromPath (λ x → VSJoin false x tEmp) (λ xs ys → cong (VSJoin false (xs ∪t ys)) (sym (∪t-left-unit tEmp))))
             (FVLabel′-map (λ x → fromPath (++t-inc-left′ S₂ T x)) (VSJoin false tEmp) (λ xs ys → cong (λ x → VSJoin false x (xs ∪t ys)) (sym (∪t-left-unit tEmp))))
             ((FVLabel′-map (λ x → fromPath (++t-inc-right′ S₂ T x)) (VSJoin false tEmp) (λ xs ys → cong (λ x → VSJoin false x (xs ∪t ys)) (sym (∪t-left-unit tEmp))))) ⟩
  VSJoin true
    (tEmp ∪t FVLabel (id-label S₁) ∪t tEmp ∪t tEmp)
    (tEmp ∪t tEmp ∪t
     FVLabel′ (λ x → fromPath (++t-inc-left′ S₂ T x))
     ∪t FVLabel′ (λ x → fromPath (++t-inc-right′ S₂ T x)))
    ≡⟨ cong₂ (VSJoin true) lem1 lem2 ⟩
  tFull ∎
  where
    lem1 : tEmp ∪t FVLabel (id-label S₁) ∪t tEmp ∪t tEmp ≡ tFull
    lem1 = begin
      tEmp ∪t FVLabel (id-label S₁) ∪t tEmp ∪t tEmp
        ≡⟨ solve (∪t-monoid {S = S₁}) ⟩
      FVLabel (id-label S₁)
        ≡⟨ id-label-full S₁ ⟩
      tFull ∎

    lem2 : tEmp ∪t tEmp ∪t
             FVLabel (ap (++t-inc-left S₂ T))
             ∪t FVLabel (ap (++t-inc-right S₂ T))
             ≡ tFull
    lem2 = begin
      tEmp ∪t tEmp ∪t FVLabel (ap (++t-inc-left S₂ T)) ∪t
        FVLabel (ap (++t-inc-right S₂ T))
        ≡⟨ solve (∪t-monoid {S = S₂ ++t T}) ⟩
      FVLabel (ap (++t-inc-left S₂ T)) ∪t
        FVLabel (ap (++t-inc-right S₂ T))
        ≡⟨ ++t-incs-full S₂ T ⟩
      tFull ∎

vs-label-DCT : {ΓS : CtxOrTree n} → (xs : TVarSet S) → (L : Label (COT-to-MT ΓS) S) → DCT xs [ L ]vl ≡ xs [ L ]vl
vs-label-DCT xs L = cong (λ a → a [ label-to-sub (L ,, S⋆) ]vs) (DCT-toVarSet xs)
