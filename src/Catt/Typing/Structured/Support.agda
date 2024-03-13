open import Catt.Typing.Rule

module Catt.Typing.Structured.Support (ops : Op)
                                      (rules : RuleSet)
                                      (tame : Tame ops rules)
                                      (supp-cond : SupportCond ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

open import Catt.Typing ops rules
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Typing.Properties.Support ops rules supp-cond
open import Catt.Tree.Structured.Typing.Properties ops rules tame

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Support.Properties

open import Tactic.MonoidSolver

open ≡-Reasoning

EqSuppSTy : {As Bs : STy (COT-to-MT ΓS)} → As ≈[ COT-to-Ctx ΓS ]sty Bs → DCM ΓS (FVSTy As) ≡ DCM ΓS (FVSTy Bs)
EqSuppSTy {ΓS = ΓS} {As = As} {Bs = Bs} [ p ] = DCM-reflect (begin
  MtoVarSet ΓS (FVSTy As)
    ≡⟨ FVSTy-to-type As ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type As)
    ≡⟨ EqSuppTy p ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type Bs)
    ≡˘⟨ FVSTy-to-type Bs ⟩
  MtoVarSet ΓS (FVSTy Bs) ∎)

EqSuppSTm : {a b : STm (COT-to-MT ΓS)} → a ≈[ COT-to-Ctx ΓS ]stm b → DCM ΓS (FVSTm a) ≡ DCM ΓS (FVSTm b)
EqSuppSTm {ΓS = ΓS} {a = a} {b = b} [ p ] = DCM-reflect (begin
  MtoVarSet ΓS (FVSTm a)
    ≡⟨ FVSTm-to-term a ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term a)
    ≡⟨ EqSuppTm p ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term b)
    ≡˘⟨ FVSTm-to-term b ⟩
  MtoVarSet ΓS (FVSTm b) ∎)

EqSuppLabel : {L M : Label (COT-to-MT ΓS) S} → L ≈[ COT-to-Ctx ΓS ]l M → DCM ΓS (FVLabel L) ≡ DCM ΓS (FVLabel M)
EqSuppLabel {ΓS = ΓS} {L = L} {M = M} p = DCM-reflect (begin
  MtoVarSet ΓS (FVLabel L)
    ≡˘⟨ cong (MtoVarSet ΓS) (FVLabel-WT-⋆ L) ⟩
  MtoVarSet ΓS (FVLabel-WT (L ,, S⋆))
    ≡⟨ FVLabel-to-sub (L ,, S⋆) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (L ,, S⋆))
    ≡⟨ EqSuppSub (label-equality-to-sub (L ,, S⋆) (M ,, S⋆) p refl≈sty) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (M ,, S⋆))
    ≡˘⟨ FVLabel-to-sub (M ,, S⋆) ⟩
  MtoVarSet ΓS (FVLabel-WT (M ,, S⋆))
    ≡⟨ cong (MtoVarSet ΓS) (FVLabel-WT-⋆ M) ⟩
  MtoVarSet ΓS (FVLabel M) ∎)

vs-label-Label : {ΓS : CtxOrTree n} → (L : Label (someTree T) S) → (M : Label (COT-to-MT ΓS) T) → Typing-Label (COT-to-Ctx ΓS) (M ,, S⋆) → MtoVarSet ΓS (FVLabel (L ●l (M ,, S⋆))) ≡ FVLabel L [ M ]vl
vs-label-Label {T = T} {ΓS = ΓS} L M Mty = begin
  MtoVarSet ΓS (FVLabel (L ●l (M ,, S⋆)))
    ≡˘⟨ cong (MtoVarSet ΓS) (FVLabel-WT-⋆ (L ●l (M ,, S⋆))) ⟩
  MtoVarSet ΓS (FVLabel-WT ((L ,, S⋆) ●lt (M ,, S⋆)))
    ≡⟨ FVLabel-to-sub (L ●l (M ,, S⋆) ,, S⋆) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (L ●l (M ,, S⋆) ,, S⋆))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (FVSub-≃ (label-comp-to-sub (L ,, S⋆) (M ,, S⋆))) ⟩
  DC (COT-to-Ctx ΓS) (FVSub (label-to-sub (L ,, S⋆) ● label-to-sub (M ,, S⋆)))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (vs-sub-sub (label-to-sub (L ,, S⋆)) (label-to-sub (M ,, S⋆))) ⟩
  DC (COT-to-Ctx ΓS) (FVSub (label-to-sub (L ,, S⋆)) [ label-to-sub (M ,, S⋆) ]vs)
    ≡⟨ vs-sub-DC (FVSub (label-to-sub (L ,, S⋆))) (label-to-sub-Ty Mty TySStar) ⟩
  DC ⌊ T ⌋ (FVSub (label-to-sub (L ,, S⋆))) [ label-to-sub (M ,, S⋆) ]vs
    ≡˘⟨ cong (_[ label-to-sub (M ,, S⋆) ]vs) (FVLabel-to-sub (L ,, S⋆)) ⟩
  FVLabel-WT (L ,, S⋆) [ M ]vl
    ≡⟨ cong (λ a → a [ M ]vl) (FVLabel-WT-⋆ L) ⟩
  FVLabel L [ M ]vl ∎

vs-label-STm : {ΓS : CtxOrTree n} → (a : STm (someTree T)) → (M : Label (COT-to-MT ΓS) T) → Typing-Label (COT-to-Ctx ΓS) (M ,, S⋆) → MtoVarSet ΓS (FVSTm (a >>= (M ,, S⋆))) ≡ FVSTm a [ M ]vl
vs-label-STm {T = T} {ΓS = ΓS} a M Mty = begin
  MtoVarSet ΓS (FVSTm (a >>= (M ,, S⋆)))
    ≡⟨ FVSTm-to-term (a >>= (M ,, S⋆)) ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term (a >>= (M ,, S⋆)))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (FVTm-≃ (label-to-sub-stm (M ,, S⋆) a)) ⟩
  DC (COT-to-Ctx ΓS) (FVTm (stm-to-term a [ label-to-sub (M ,, S⋆) ]tm))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (vs-sub-tm (stm-to-term a) (label-to-sub (M ,, S⋆))) ⟩
  DC (COT-to-Ctx ΓS) (FVTm (stm-to-term a) [ label-to-sub (M ,, S⋆) ]vs)
    ≡⟨ vs-sub-DC (FVTm (stm-to-term a)) (label-to-sub-Ty Mty TySStar) ⟩
  DC ⌊ T ⌋ (FVTm (stm-to-term a)) [ label-to-sub (M ,, S⋆) ]vs
    ≡˘⟨ cong (_[ label-to-sub (M ,, S⋆) ]vs) (FVSTm-to-term a) ⟩
  FVSTm a [ M ]vl ∎

vs-label-STy : {ΓS : CtxOrTree n} → (As : STy (someTree T)) → (M : Label (COT-to-MT ΓS) T) → Typing-Label (COT-to-Ctx ΓS) (M ,, S⋆) → MtoVarSet ΓS (FVSTy (As >>=′ (M ,, S⋆))) ≡ FVSTy As [ M ]vl
vs-label-STy {T = T} {ΓS = ΓS} As M Mty = begin
  MtoVarSet ΓS (FVSTy (As >>=′ (M ,, S⋆)))
    ≡⟨ FVSTy-to-type (As >>=′ (M ,, S⋆)) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type (As >>=′ (M ,, S⋆)))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (FVTy-≃ (label-to-sub-sty (M ,, S⋆) As)) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type As [ label-to-sub (M ,, S⋆) ]ty))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (vs-sub-ty (sty-to-type As) (label-to-sub (M ,, S⋆))) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type As) [ label-to-sub (M ,, S⋆) ]vs)
    ≡⟨ vs-sub-DC (FVTy (sty-to-type As)) (label-to-sub-Ty Mty TySStar) ⟩
  DC ⌊ T ⌋ (FVTy (sty-to-type As)) [ label-to-sub (M ,, S⋆) ]vs
    ≡˘⟨ cong (_[ label-to-sub (M ,, S⋆) ]vs) (FVSTy-to-type As) ⟩
  FVSTy As [ M ]vl ∎

vs-label-full : {ΓS : CtxOrTree n} → (L : Label (COT-to-MT ΓS) S) → Typing-Label (COT-to-Ctx ΓS) (L ,, S⋆)
              → tFull [ L ]vl ≡ MtoVarSet ΓS (FVLabel L)
vs-label-full {S = S} {ΓS = ΓS} L Lty = begin
  tFull [ L ]vl
    ≡⟨ cong (_[ label-to-sub (L ,, S⋆) ]vs) (toVarSet-full S) ⟩
  full [ label-to-sub (L ,, S⋆) ]vs
    ≡⟨ vs-sub-full (label-to-sub (L ,, S⋆)) ⟩
  FVSub (label-to-sub (L ,, S⋆))
    ≡˘⟨ SuppSubFV (label-to-sub-Ty Lty TySStar) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (L ,, S⋆))
    ≡˘⟨ FVLabel-to-sub (L ,, S⋆) ⟩
  MtoVarSet ΓS (FVLabel-WT (L ,, S⋆))
    ≡⟨ cong (MtoVarSet ΓS) (FVLabel-WT-⋆ L) ⟩
  MtoVarSet ΓS (FVLabel L) ∎

FV-label-comp-full : (L : Label (someTree T) S) → (M : Label (COT-to-MT ΓS) T) → Typing-Label (COT-to-Ctx ΓS) (M ,, S⋆) → DCT (FVLabel L) ≡ tFull → DCM ΓS (FVLabel (L ●l (M ,, S⋆))) ≡ DCM ΓS (FVLabel M)
FV-label-comp-full {T = T} {ΓS = ΓS} L M Mty p = DCM-reflect (begin
  MtoVarSet ΓS (FVLabel (L ●l (M ,, S⋆)))
    ≡⟨ vs-label-Label L M Mty ⟩
  FVLabel L [ M ]vl
    ≡˘⟨ vs-label-DCT (FVLabel L) M ⟩
  DCT (FVLabel L) [ M ]vl
    ≡⟨ cong (_[ M ]vl) p ⟩
  tFull [ M ]vl
    ≡⟨ vs-label-full M Mty ⟩
  MtoVarSet ΓS (FVLabel M) ∎)

replace-label-supp : {ΓS : CtxOrTree n} → (L : Label (COT-to-MT ΓS) S) → (a : STm (COT-to-MT ΓS)) → a ≈[ COT-to-Ctx ΓS ]stm L PHere → DCM ΓS (FVLabel (replace-label L a)) ≡ DCM ΓS (FVSTm a) ∪m DCM ΓS (FVLabel L)
replace-label-supp {S = Sing} L a p = trans (sym (∪m-idem (DCM _ (FVLabel (replace-label L a))))) (cong (DCM _ (FVSTm a) ∪m_) (EqSuppSTm p))
replace-label-supp {S = Join S₁ S₂} {ΓS = ΓS} L a p = begin
  DCM _ (FVSTm a ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift))
    ≡⟨ DCM-∪ _ (FVSTm a ∪m FVLabel (λ x → L (PExt x))) (FVLabel (λ x → L (PShift x))) ⟩
  DCM _ (FVSTm a ∪m FVLabel (λ x → L (PExt x))) ∪m DCM _ (FVLabel (λ x → L (PShift x)))
    ≡⟨ cong (_∪m _) (DCM-∪ _ (FVSTm a) (FVLabel (λ x → L (PExt x)))) ⟩
  DCM _ (FVSTm a) ∪m DCM _ (FVLabel (L ∘ PExt)) ∪m DCM _ (FVLabel (L ∘ PShift))
    ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
  DCM _ (FVSTm a) ∪m (DCM _ (FVLabel (L ∘ PExt)) ∪m DCM _ (FVLabel (L ∘ PShift)))
    ≡⟨ cong (_∪m _) (trans (sym (∪m-idem (DCM ΓS (FVSTm a)))) (cong (_ ∪m_) (EqSuppSTm p))) ⟩
  DCM _ (FVSTm a) ∪m DCM _ (FVSTm (L PHere)) ∪m (DCM _ (FVLabel (L ∘ PExt)) ∪m DCM _ (FVLabel (L ∘ PShift)))
    ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
  DCM _ (FVSTm a) ∪m (DCM _ (FVSTm (L PHere)) ∪m DCM _ (FVLabel (L ∘ PExt)) ∪m DCM _ (FVLabel (L ∘ PShift)))
    ≡˘⟨ cong (λ a → _ ∪m (a ∪m DCM _ (FVLabel (L ∘ PShift)))) (DCM-∪ _ (FVSTm (L PHere)) (FVLabel (λ x → L (PExt x)))) ⟩
  DCM _ (FVSTm a) ∪m
    (DCM _ (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) ∪m
     DCM _ (FVLabel (λ x → L (PShift x))))
    ≡˘⟨ cong (_ ∪m_) (DCM-∪ _ (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) (FVLabel (λ x → L (PShift x)))) ⟩
  DCM _ (FVSTm a) ∪m DCM _ (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)) ∎

++l-supp : {ΓS : CtxOrTree n} → (L : Label (COT-to-MT ΓS) S) → (M : Label (COT-to-MT ΓS) T) → L (last-path S) ≈[ COT-to-Ctx ΓS ]stm M PHere → DCM ΓS (FVLabel (L ++l M)) ≡ DCM ΓS (FVLabel L) ∪m DCM ΓS (FVLabel M)
++l-supp {S = Sing} L M p = replace-label-supp M (L PHere) p
++l-supp {S = Join S₁ S₂} {ΓS = ΓS} L M p = begin
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift ++l M))
    ≡⟨ DCM-∪ ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) (FVLabel (L ∘ PShift ++l M)) ⟩
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) ∪m DCM ΓS (FVLabel (L ∘ PShift ++l M))
    ≡⟨ cong (_ ∪m_) (++l-supp (L ∘ PShift) M p) ⟩
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) ∪m (DCM ΓS (FVLabel (L ∘ PShift)) ∪m DCM ΓS (FVLabel M))
    ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) ∪m DCM ΓS (FVLabel (L ∘ PShift)) ∪m DCM ΓS (FVLabel M)
    ≡˘⟨ cong (_∪m _) (DCM-∪ ΓS (FVSTm (L PHere) ∪m FVLabel′ (λ x → FVSTm (L (PExt x)))) (FVLabel′ (λ x → FVSTm (L (PShift x))))) ⟩
  DCM ΓS (FVLabel L) ∪m DCM ΓS (FVLabel M) ∎

++l′-supp : {ΓS : CtxOrTree n} → (L : Label (COT-to-MT ΓS) S) → (M : Label (COT-to-MT ΓS) T) → L (last-path S) ≈[ COT-to-Ctx ΓS ]stm M PHere → DCM ΓS (FVLabel (L ++l′ M)) ≡ DCM ΓS (FVLabel L) ∪m DCM ΓS (FVLabel M)
++l′-supp {S = Sing} {ΓS = ΓS} L M p = begin
  DCM ΓS (FVLabel M)
    ≡⟨ cong (DCM ΓS) (label-ap-⊆ M PHere) ⟩
  DCM ΓS (FVLabel M ∪m FVSTm (M PHere))
    ≡⟨ DCM-∪ ΓS (FVLabel M) (FVSTm (M PHere)) ⟩
  DCM ΓS (FVLabel M) ∪m DCM ΓS (FVSTm (M PHere))
    ≡⟨ ∪m-comm (DCM ΓS (FVLabel M)) (DCM ΓS (FVSTm (M PHere))) ⟩
  DCM ΓS (FVSTm (M PHere)) ∪m DCM ΓS (FVLabel M)
    ≡˘⟨ cong (_∪m DCM ΓS (FVLabel M)) (EqSuppSTm p) ⟩
  DCM ΓS (FVSTm (L PHere)) ∪m DCM ΓS (FVLabel M) ∎
++l′-supp {S = Join S₁ S₂} {ΓS = ΓS} L M p = begin
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift ++l′ M))
    ≡⟨ DCM-∪ ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) (FVLabel (L ∘ PShift ++l′ M)) ⟩
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) ∪m DCM ΓS (FVLabel (L ∘ PShift ++l′ M))
    ≡⟨ cong (_ ∪m_) (++l′-supp (L ∘ PShift) M p) ⟩
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) ∪m (DCM ΓS (FVLabel (L ∘ PShift)) ∪m DCM ΓS (FVLabel M))
    ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) ∪m DCM ΓS (FVLabel (L ∘ PShift)) ∪m DCM ΓS (FVLabel M)
    ≡˘⟨ cong (_∪m _) (DCM-∪ ΓS (FVSTm (L PHere) ∪m FVLabel′ (λ x → FVSTm (L (PExt x)))) (FVLabel′ (λ x → FVSTm (L (PShift x))))) ⟩
  DCM ΓS (FVLabel L) ∪m DCM ΓS (FVLabel M) ∎

label-between-++t-full : (L : Label (someTree S′) S) → (M : Label (someTree T′) T)
                                 → L (last-path S) ≈[ ⌊ S′ ⌋ ]stm SPath (last-path S′)
                                 → M PHere ≈[ ⌊ T′ ⌋ ]stm SHere
                                 → DCM (incTree S′) (FVLabel L) ≡ tFull
                                 → DCM (incTree T′) (FVLabel M) ≡ tFull
                                 → DCM (incTree (S′ ++t T′)) (FVLabel (label-between-++t L M)) ≡ tFull
label-between-++t-full {S′ = S′} {T′ = T′} L M p q r s = begin
  DCM (incTree (S′ ++t T′)) (FVLabel (label-between-++t L M))
    ≡⟨ ++l′-supp (L ●l (++t-inc-left S′ T′)) (M ●l (++t-inc-right S′ T′)) (label-between-++t-lem L M p q) ⟩
  DCM (incTree (S′ ++t T′))
    (FVLabel (L ●l (++t-inc-left S′ T′)))
    ∪m
    DCM (incTree (S′ ++t T′))
    (FVLabel (M ●l (++t-inc-right S′ T′)))
    ≡⟨ cong₂ _∪m_ (FV-label-comp-full L (ap (++t-inc-left S′ T′)) (++t-inc-left-Ty S′ T′) r) (FV-label-comp-full M (ap (++t-inc-right S′ T′)) (++t-inc-right-Ty S′ T′) s) ⟩
  DCT (FVLabel (ap (++t-inc-left S′ T′))) ∪m DCT (FVLabel (ap (++t-inc-right S′ T′)))
    ≡˘⟨ DCT-∪ (FVLabel′ (λ P → FVSTm (proj₁ (++t-inc-left S′ T′) P))) (FVLabel (proj₁ (++t-inc-right S′ T′))) ⟩
  DCT (FVLabel (ap (++t-inc-left S′ T′)) ∪m FVLabel (ap (++t-inc-right S′ T′)))
    ≡⟨ cong DCT (++t-incs-full S′ T′) ⟩
  DCT tFull
    ≡⟨ DCT-full ⟩
  tFull ∎

label-between-joins-full : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → DCT (FVLabel L) ≡ tFull → DCT (FVLabel M) ≡ tFull → DCT (FVLabel (label-between-joins L M)) ≡ tFull
label-between-joins-full {S′ = S′} {T′ = T′} L M p q = begin
  DCT
      (VSJoin true tEmp tEmp ∪t
       FVLabel′ (λ x → VSJoin false (FVSTm (L x)) tEmp)
       ∪t FVLabel′ (λ x → VSJoin false tEmp (FVSTm (M x))))
    ≡⟨ cong DCT (cong₂ (λ a b → VSJoin true tEmp tEmp ∪t a ∪t b) (FVLabel′-map (FVSTm ∘ L) (λ x → VSJoin false x tEmp) (λ xs ys → cong (VSJoin false (xs ∪t ys)) (sym (∪t-left-unit tEmp)))) (FVLabel′-map (FVSTm ∘ M) (VSJoin false tEmp) (λ xs ys → cong (λ x → VSJoin false x (xs ∪t ys)) (sym (∪t-right-unit tEmp))))) ⟩
  DCT
    (VSJoin true tEmp tEmp ∪t
     VSJoin false (FVLabel′ (λ x → FVSTm (L x))) tEmp
     ∪t VSJoin false tEmp (FVLabel′ (λ x → FVSTm (M x))))
    ≡⟨⟩
  VSJoin true (DCT (tEmp ∪t FVLabel′ (λ x → FVSTm (L x)) ∪t tEmp))
      (if
       tvarset-non-empty (tEmp ∪t FVLabel′ (λ x → FVSTm (L x)) ∪t tEmp)
       then
       set-fst-true (DCT (tEmp ∪t tEmp ∪t FVLabel′ (λ x → FVSTm (M x))))
       else DCT (tEmp ∪t tEmp ∪t FVLabel′ (λ x → FVSTm (M x))))
    ≡⟨ cong₃ (λ a b c → VSJoin true a (if tvarset-non-empty (tEmp ∪t FVLabel′ (λ x → FVSTm (L x)) ∪t tEmp) then b else c)) lem1 (trans (cong set-fst-true lem2) set-fst-true-full) lem2 ⟩
  VSJoin true tFull (if tvarset-non-empty (tEmp ∪t FVLabel′ (λ x → FVSTm (L x)) ∪t tEmp)
     then tFull else tFull)
    ≡⟨ cong (VSJoin true tFull) (if-lem-const (tvarset-non-empty (tEmp ∪t FVLabel′ (λ x → FVSTm (L x)) ∪t tEmp)) tFull) ⟩
  VSJoin true tFull tFull
    ≡⟨⟩
  tFull ∎
  where
    lem1 : DCT (tEmp ∪t FVLabel L ∪t tEmp) ≡ tFull
    lem1 = begin
      DCT (tEmp ∪t FVLabel L ∪t tEmp)
        ≡⟨ cong DCT (solve (∪t-monoid {S = S′})) ⟩
      DCT (FVLabel L)
        ≡⟨ p ⟩
      tFull ∎

    lem2 : DCT (tEmp ∪t tEmp ∪t FVLabel M) ≡ tFull
    lem2 = begin
      DCT (tEmp ∪t tEmp ∪t FVLabel M)
        ≡⟨ cong DCT (solve (∪t-monoid {S = T′})) ⟩
      DCT (FVLabel M)
        ≡⟨ q ⟩
      tFull ∎
