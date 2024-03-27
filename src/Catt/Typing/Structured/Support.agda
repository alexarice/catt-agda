open import Catt.Typing.Rule

module Catt.Typing.Structured.Support (ops : Op)
                                      (rules : RuleSet)
                                      (tame : Tame ops rules)
                                      (supp-cond : SupportCond ops rules) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

open import Catt.Typing ops rules
open import Catt.Tree.Structured.Typing ops rules
open import Catt.Tree.Structured.Typing.Properties ops rules tame
open import Catt.Typing.Properties.Support ops rules supp-cond

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Wedge.Support
open import Catt.Suspension.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Construct.Support

import Algebra.Solver.IdempotentCommutativeMonoid as Solver
open import Tactic.MonoidSolver

open ≡-Reasoning

EqSuppSTy : {As Bs : STy (COT-to-MT ΓS)} → As ≈[ COT-to-Ctx ΓS ]sty Bs → SuppSTy ΓS As ≡ SuppSTy ΓS Bs
EqSuppSTy {ΓS = ΓS} {As = As} {Bs = Bs} [ p ] = begin
  SuppSTy ΓS As
    ≡⟨ SuppSTy-to-type ΓS As ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type As)
    ≡⟨ EqSuppTy p ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type Bs)
    ≡˘⟨ SuppSTy-to-type ΓS Bs ⟩
  SuppSTy ΓS Bs ∎

EqSuppSTm : {As Bs : STm (COT-to-MT ΓS)} → As ≈[ COT-to-Ctx ΓS ]stm Bs → SuppSTm ΓS As ≡ SuppSTm ΓS Bs
EqSuppSTm {ΓS = ΓS} {As = As} {Bs = Bs} [ p ] = begin
  SuppSTm ΓS As
    ≡⟨ SuppSTm-to-term ΓS As ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term As)
    ≡⟨ EqSuppTm p ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term Bs)
    ≡˘⟨ SuppSTm-to-term ΓS Bs ⟩
  SuppSTm ΓS Bs ∎


EqSuppLabel : {L M : Label (COT-to-MT ΓS) S} → L ≈[ COT-to-Ctx ΓS ]l M → SuppLabel ΓS L ≡ SuppLabel ΓS M
EqSuppLabel {ΓS = ΓS} {L = L} {M = M} p = begin
  SuppLabel ΓS L
    ≡˘⟨ ∪-left-unit (SuppLabel ΓS L) ⟩
  SuppLabel-WT ΓS (L ,, S⋆)
    ≡⟨ SuppLabel-to-sub ΓS (L ,, S⋆) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (L ,, S⋆))
    ≡⟨ EqSuppSub (label-equality-to-sub (L ,, S⋆) (M ,, S⋆) p refl≈sty) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (M ,, S⋆))
    ≡˘⟨ SuppLabel-to-sub ΓS (M ,, S⋆) ⟩
  SuppLabel-WT ΓS (M ,, S⋆)
    ≡⟨ ∪-left-unit (SuppLabel ΓS M) ⟩
  SuppLabel ΓS M ∎

vs-label-Label : (ΓS : CtxOrTree n) → (L : Label (someTree T) S) → (M : Label (COT-to-MT ΓS) T)
               → Typing-Label (COT-to-Ctx ΓS) (M ,, S⋆)
               → SuppLabel ΓS (L ●l (M ,, S⋆)) ≡ SuppLabel (incTree T) L [ M ]vl
vs-label-Label {T = T} ΓS L M Mty = begin
  SuppLabel ΓS (L ●l (M ,, S⋆))
    ≡˘⟨ ∪-left-unit (SuppLabel ΓS (L ●l (M ,, S⋆))) ⟩
  SuppLabel-WT ΓS ((L ,, S⋆) ●lt (M ,, S⋆))
    ≡⟨ SuppLabel-to-sub ΓS ((L ,, S⋆) ●lt (M ,, S⋆)) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub ((L ,, S⋆) ●lt (M ,, S⋆)))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (FVSub-≃ (label-comp-to-sub (L ,, S⋆) (M ,, S⋆))) ⟩
  DC (COT-to-Ctx ΓS) (FVSub (label-to-sub (L ,, S⋆) ● label-to-sub (M ,, S⋆)))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (vs-sub-sub (label-to-sub (L ,, S⋆)) (label-to-sub (M ,, S⋆))) ⟩
  DC (COT-to-Ctx ΓS) (FVSub (label-to-sub (L ,, S⋆)) [ label-to-sub (M ,, S⋆) ]vs)
    ≡⟨ vs-sub-DC (FVSub (label-to-sub (L ,, S⋆))) (label-to-sub-Ty Mty TySStar) ⟩
  SuppSub ⌊ T ⌋ (label-to-sub (L ,, S⋆)) [ label-to-sub (M ,, S⋆) ]vs
    ≡˘⟨ cong (_[ label-to-sub (M ,, S⋆) ]vs) (SuppLabel-to-sub (incTree T) (L ,, S⋆)) ⟩
  SuppLabel-WT (incTree T) (L ,, S⋆) [ label-to-sub (M ,, S⋆) ]vs
    ≡⟨ cong (_[ M ]vl) (∪-left-unit (SuppLabel (incTree T) L)) ⟩
  SuppLabel (incTree T) L [ M ]vl ∎

vs-label-STm : (ΓS : CtxOrTree n) → (a : STm (someTree T)) → (M : Label (COT-to-MT ΓS) T)
             → Typing-Label (COT-to-Ctx ΓS) (M ,, S⋆)
             → SuppSTm ΓS (a >>= (M ,, S⋆)) ≡ SuppSTm (incTree T) a [ M ]vl
vs-label-STm {T = T} ΓS a M Mty = begin
  SuppSTm ΓS (a >>= (M ,, S⋆))
    ≡⟨ SuppSTm-to-term ΓS (a >>= (M ,, S⋆)) ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term (a >>= (M ,, S⋆)))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (FVTm-≃ (label-to-sub-stm (M ,, S⋆) a)) ⟩
  DC (COT-to-Ctx ΓS) (FVTm (stm-to-term a [ label-to-sub (M ,, S⋆) ]tm))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (vs-sub-tm (stm-to-term a) (label-to-sub (M ,, S⋆))) ⟩
  DC (COT-to-Ctx ΓS) (FVTm (stm-to-term a) [ label-to-sub (M ,, S⋆) ]vs)
    ≡⟨ vs-sub-DC (FVTm (stm-to-term a)) (label-to-sub-Ty Mty TySStar) ⟩
  DC ⌊ T ⌋ (FVTm (stm-to-term a)) [ label-to-sub (M ,, S⋆) ]vs
    ≡˘⟨ cong (_[ label-to-sub (M ,, S⋆) ]vs) (SuppSTm-to-term (incTree T) a) ⟩
  SuppSTm (incTree T) a [ M ]vl ∎

vs-label-STy : (ΓS : CtxOrTree n) → (As : STy (someTree T)) → (M : Label (COT-to-MT ΓS) T)
             → Typing-Label (COT-to-Ctx ΓS) (M ,, S⋆)
             → SuppSTy ΓS (As >>=′ (M ,, S⋆)) ≡ SuppSTy (incTree T) As [ M ]vl
vs-label-STy {T = T} ΓS As M Mty = begin
  SuppSTy ΓS (As >>=′ (M ,, S⋆))
    ≡⟨ SuppSTy-to-type ΓS (As >>=′ (M ,, S⋆)) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type (As >>=′ (M ,, S⋆)))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (FVTy-≃ (label-to-sub-sty (M ,, S⋆) As)) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type As [ label-to-sub (M ,, S⋆) ]ty))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (vs-sub-ty (sty-to-type As) (label-to-sub (M ,, S⋆))) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type As) [ label-to-sub (M ,, S⋆) ]vs)
    ≡⟨ vs-sub-DC (FVTy (sty-to-type As)) (label-to-sub-Ty Mty TySStar) ⟩
  DC ⌊ T ⌋ (FVTy (sty-to-type As)) [ label-to-sub (M ,, S⋆) ]vs
    ≡˘⟨ cong (_[ label-to-sub (M ,, S⋆) ]vs) (SuppSTy-to-type (incTree T) As) ⟩
  SuppSTy (incTree T) As [ M ]vl ∎

vs-label-full : (ΓS : CtxOrTree n) → (L : Label (COT-to-MT ΓS) S)
              → Typing-Label (COT-to-Ctx ΓS) (L ,, S⋆)
              → full [ L ]vl ≡ SuppLabel ΓS L
vs-label-full {S = S} ΓS L Lty = begin
  full [ label-to-sub (L ,, S⋆) ]vs
    ≡⟨ vs-sub-full (label-to-sub (L ,, S⋆)) ⟩
  FVSub (label-to-sub (L ,, S⋆))
    ≡˘⟨ SuppSubFV (label-to-sub-Ty Lty TySStar) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (L ,, S⋆))
    ≡˘⟨ SuppLabel-to-sub ΓS (L ,, S⋆) ⟩
  SuppLabel-WT ΓS (L ,, S⋆)
    ≡⟨ ∪-left-unit (SuppLabel ΓS L) ⟩
  SuppLabel ΓS L ∎

SuppLabel-comp-full : (ΓS : CtxOrTree n) → (L : Label (someTree T) S) → (M : Label (COT-to-MT ΓS) T)
                    → Typing-Label (COT-to-Ctx ΓS) (M ,, S⋆)
                    → SuppLabel (incTree T) L ≡ full
                    → SuppLabel ΓS (L ●l (M ,, S⋆)) ≡ SuppLabel ΓS M
SuppLabel-comp-full {T = T} ΓS L M Mty p = begin
  SuppLabel ΓS (L ●l (M ,, S⋆))
    ≡⟨ vs-label-Label ΓS L M Mty ⟩
  SuppLabel (incTree T) L [ M ]vl
    ≡⟨ cong (_[ M ]vl) p ⟩
  full [ M ]vl
    ≡⟨ vs-label-full ΓS M Mty ⟩
  SuppLabel ΓS M ∎

replace-label-supp : {ΓS : CtxOrTree n}
                   → (L : Label (COT-to-MT ΓS) S)
                   → (a : STm (COT-to-MT ΓS))
                   → a ≈[ COT-to-Ctx ΓS ]stm L PHere
                   → SuppLabel ΓS (replace-label L a) ≡ SuppSTm ΓS a ∪ SuppLabel ΓS L
replace-label-supp {S = Sing} {ΓS = ΓS} L a p = begin
  SuppSTm ΓS a
    ≡˘⟨ ∪-idem (SuppSTm ΓS a) ⟩
  SuppSTm ΓS a ∪ SuppSTm ΓS a
    ≡⟨ cong (SuppSTm ΓS a ∪_) (EqSuppSTm p) ⟩
  SuppSTm ΓS a ∪ SuppLabel ΓS L ∎
replace-label-supp {S = Join S T} {ΓS = ΓS} L a p = begin
  SuppSTm ΓS a ∪ SuppLabel ΓS (L ∘ PExt) ∪ SuppLabel ΓS (L ∘ PShift)
    ≡⟨ prove 3 ((var 0F ⊕ var 1F) ⊕ var 2F )
               (var 0F ⊕ ((var 0F ⊕ var 1F) ⊕ var 2F))
               (SuppSTm ΓS a ∷ SuppLabel ΓS (L ∘ PExt) ∷ SuppLabel ΓS (L ∘ PShift) ∷ emp) ⟩
  SuppSTm ΓS a ∪
   (SuppSTm ΓS a ∪ SuppLabel ΓS (L ∘ PExt) ∪
    SuppLabel ΓS (L ∘ PShift))
    ≡⟨ cong (λ - → SuppSTm ΓS a ∪ (- ∪ SuppLabel ΓS (L ∘ PExt) ∪ SuppLabel ΓS (L ∘ PShift)))
            (EqSuppSTm p) ⟩
  SuppSTm ΓS a
  ∪ (SuppSTm ΓS (L PHere)
     ∪ SuppLabel ΓS (L ∘ PExt)
     ∪ SuppLabel ΓS (L ∘ PShift)) ∎
     where
       open Solver ∪-idempotentCommutativeMonoid

++l′-supp : {ΓS : CtxOrTree n} → (L : Label (COT-to-MT ΓS) S) → (M : Label (COT-to-MT ΓS) T)
          → L (last-path S) ≈[ COT-to-Ctx ΓS ]stm M PHere
          → SuppLabel ΓS (L ++l′ M) ≡ SuppLabel ΓS L ∪ SuppLabel ΓS M
++l′-supp {S = Sing} {ΓS = ΓS} L M p = begin
  SuppLabel ΓS M
    ≡⟨ SuppLabel-PHere-⊆ ΓS M ⟩
  SuppLabel ΓS M ∪ SuppSTm ΓS (M PHere)
    ≡⟨ ∪-comm (SuppLabel ΓS M) (SuppSTm ΓS (M PHere)) ⟩
  SuppSTm ΓS (M PHere) ∪ SuppLabel ΓS M
    ≡˘⟨ cong (_∪ SuppLabel ΓS M) (EqSuppSTm p) ⟩
  SuppSTm ΓS (L PHere) ∪ SuppLabel ΓS M ∎
++l′-supp {n = n} {S = Join S S₁} {ΓS = ΓS} L M p = begin
  SuppSTm ΓS (L PHere)
  ∪ SuppLabel ΓS (L ∘ PExt)
  ∪ SuppLabel ΓS ((L ∘ PShift) ++l′ M)
    ≡⟨ cong (SuppSTm ΓS (L PHere) ∪ SuppLabel ΓS (L ∘ PExt) ∪_) (++l′-supp (L ∘ PShift) M p) ⟩
  SuppSTm ΓS (L PHere) ∪ SuppLabel ΓS (L ∘ PExt) ∪ (SuppLabel ΓS (L ∘ PShift) ∪ SuppLabel ΓS M)
    ≡⟨ solve (∪-monoid {n = n}) ⟩
  SuppSTm ΓS (L PHere)
  ∪ SuppLabel ΓS (L ∘ PExt)
  ∪ SuppLabel ΓS (L ∘ PShift)
  ∪ SuppLabel ΓS M ∎

label-between-++t-full : (L : Label (someTree S′) S) → (M : Label (someTree T′) T)
                       → L (last-path S) ≈[ ⌊ S′ ⌋ ]stm SPath (last-path S′)
                       → M PHere ≈[ ⌊ T′ ⌋ ]stm SHere
                       → SuppLabel (incTree S′) L ≡ full
                       → SuppLabel (incTree T′) M ≡ full
                       → SuppLabel (incTree (S′ ++t T′)) (label-between-++t L M) ≡ full
label-between-++t-full {S′ = S′} {T′ = T′} L M p q r s = begin
  SuppLabel (incTree (S′ ++t T′)) (label-between-++t L M)
    ≡⟨ ++l′-supp (L ●l (++t-inc-left S′ T′)) (M ●l ++t-inc-right S′ T′) (label-between-++t-lem L M p q) ⟩
  SuppLabel (incTree (S′ ++t T′)) (L ●l ++t-inc-left S′ T′)
  ∪ SuppLabel (incTree (S′ ++t T′)) (M ●l ++t-inc-right S′ T′)
    ≡⟨ cong₂ _∪_ (SuppLabel-comp-full (incTree (S′ ++t T′))
                                      L
                                      (ap (++t-inc-left S′ T′))
                                      (++t-inc-left-Ty S′ T′)
                                      r)
                 (SuppLabel-comp-full (incTree (S′ ++t T′))
                                      M
                                      (ap (++t-inc-right S′ T′))
                                      (++t-inc-right-Ty S′ T′)
                                      s) ⟩
  SuppLabel (incTree (S′ ++t T′)) (ap (++t-inc-left S′ T′)) ∪
   SuppLabel (incTree (S′ ++t T′)) (ap (++t-inc-right S′ T′))
    ≡⟨ ++t-incs-full S′ T′ ⟩
  full ∎

label-between-joins-full : (L : Label (someTree S′) S) → (M : Label (someTree T′) T)
                         → SuppLabel _ L ≡ full
                         → SuppLabel _ M ≡ full
                         → SuppLabel _ (label-between-joins L M) ≡ full
label-between-joins-full {S′ = S′} {T′ = T′} L M p q = begin
  trueAt (fromℕ _)
   ∪ SuppLabel _ (SExt {T = T′} ∘ L)
   ∪ SuppLabel _ (SShift {S = S′} ∘ M)
    ≡⟨ cong₂ (λ a b → trueAt (fromℕ _) ∪ a ∪ b)
             (SuppLabel-ext L T′)
             (SuppLabel-shift M S′) ⟩
  trueAt (fromℕ (_ + (2 + _))) ∪
   wedge-susp-vs (susp-vs (SuppLabel (incTree S′) L)) empty
   ∪ wedge-susp-vs empty (SuppLabel (incTree T′) M)
    ≡⟨ ∪-assoc _ _ _ ⟩
  trueAt (fromℕ (_ + (2 + _))) ∪
   (wedge-susp-vs (susp-vs (SuppLabel (incTree S′) L)) empty ∪
    wedge-susp-vs empty (SuppLabel (incTree T′) M))
    ≡⟨ cong (trueAt (fromℕ (_ + (2 + _))) ∪_)
            (wedge-vs-∪ (susp-vs (SuppLabel (incTree S′) L)) empty empty (SuppLabel (incTree T′) M) get-snd) ⟩
  trueAt (fromℕ (_ + (2 + _))) ∪
   wedge-susp-vs (susp-vs (SuppLabel (incTree S′) L) ∪ empty) (empty ∪ SuppLabel (incTree T′) M)
    ≡⟨ cong (trueAt (fromℕ (_ + (2 + _))) ∪_)
            (cong₂ wedge-susp-vs l1 l2) ⟩
  trueAt (fromℕ (_ + (2 + _))) ∪ wedge-susp-vs full full
    ≡⟨ cong (trueAt (fromℕ (_ + (2 + _))) ∪_) (wedge-vs-full (suc _) get-snd _) ⟩
  trueAt (fromℕ (_ + (2 + _))) ∪ full
    ≡⟨ ∪-right-zero (trueAt (fromℕ (_ + (2 + _)))) ⟩
  full ∎
  where
    l1 : susp-vs (SuppLabel (incTree S′) L) ∪ empty ≡ full
    l1 = begin
      susp-vs (SuppLabel (incTree S′) L) ∪ empty
        ≡⟨ ∪-right-unit (susp-vs (SuppLabel (incTree S′) L)) ⟩
      susp-vs (SuppLabel (incTree S′) L)
        ≡⟨ cong susp-vs p ⟩
      susp-vs full
        ≡⟨ susp-vs-full ⟩
      full ∎

    l2 : empty ∪ SuppLabel (incTree T′) M ≡ full
    l2 = begin
      empty ∪ SuppLabel (incTree T′) M
        ≡⟨ ∪-left-unit (SuppLabel (incTree T′) M) ⟩
      SuppLabel (incTree T′) M
        ≡⟨ q ⟩
      full ∎
