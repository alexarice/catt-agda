module Catt.Tree.Structured.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.ToTerm

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Wedge.Support
open import Catt.Tree.Path.Support

import Algebra.Solver.IdempotentCommutativeMonoid as Solver

infixr 30 _[_]vl
_[_]vl : {X : MaybeTree n} → VarSet (suc (tree-size S)) → (L : Label X S) → VarSet n
xs [ L ]vl = xs [ label-to-sub (L ,, S⋆) ]vs

SuppSTm : (ΓS : CtxOrTree n) → STm (COT-to-MT ΓS) → VarSet n
SuppLabel : (ΓS : CtxOrTree n) → Label (COT-to-MT ΓS) S → VarSet n
SuppLabel-WT : (ΓS : CtxOrTree n) → Label-WT (COT-to-MT ΓS) S → VarSet n
SuppSTy : (ΓS : CtxOrTree n) → STy (COT-to-MT ΓS) → VarSet n

SuppSTm (incTree T) (SPath P) = SuppPath P
SuppSTm (incTree T) (SCoh S A L) = SuppLabel-WT (incTree T) L
SuppSTm (incTree (Join S T)) (SExt a) = wedge-susp-vs (susp-vs (SuppSTm (incTree S) a)) empty
SuppSTm (incTree (Join S T)) (SShift a) = wedge-susp-vs empty (SuppSTm (incTree T) a)
SuppSTm (incCtx Γ) (SCoh S A L) = SuppLabel-WT (incCtx Γ) L
SuppSTm (incCtx Γ) (SOther t) = DC Γ (FVTm t)

SuppSTy ΓS S⋆ = empty
SuppSTy ΓS (SArr s As t) = SuppSTy ΓS As ∪ SuppSTm ΓS s ∪ SuppSTm ΓS t

SuppLabel′ : ((P : Path S) → VarSet n) → VarSet n
SuppLabel′ {S = Sing} f = f PHere
SuppLabel′ {S = Join S T} f = f PHere ∪ SuppLabel′ (f ∘ PExt) ∪ SuppLabel′ (f ∘ PShift)

SuppLabel ΓS L = SuppLabel′ (SuppSTm ΓS ∘ L)

SuppLabel-WT ΓS L = SuppSTy ΓS (lty L) ∪ SuppLabel ΓS (ap L)

open ≡-Reasoning

SuppLabel-PHere-⊆ : (ΓS : CtxOrTree n) → (L : Label (COT-to-MT ΓS) S) → SuppSTm ΓS (L PHere) ⊆ SuppLabel ΓS L
SuppLabel-PHere-⊆ {S = Sing} ΓS L = ⊆-refl
SuppLabel-PHere-⊆ {S = Join S T} ΓS L = ⊆-trans (∪-⊆-1 _ _) (∪-⊆-1 _ _)

SuppSTm-to-term : (ΓS : CtxOrTree n)
                → (a : STm (COT-to-MT ΓS))
                → SuppSTm ΓS a ≡ SuppTm (COT-to-Ctx ΓS) (stm-to-term a)
SuppSTy-to-type : (ΓS : CtxOrTree n)
                → (A : STy (COT-to-MT ΓS))
                → SuppSTy ΓS A ≡ SuppTy (COT-to-Ctx ΓS) (sty-to-type A)
SuppLabel-to-sub : (ΓS : CtxOrTree n)
                 → (L : Label-WT (COT-to-MT ΓS) S)
                 → SuppLabel-WT ΓS L ≡ SuppSub (COT-to-Ctx ΓS) (label-to-sub L)
SuppLabel-to-sub′ : (ΓS : CtxOrTree n)
                  → (L : Label-WT (COT-to-MT ΓS) S)
                  → ((P : Path S) → SuppSTm ΓS (ap L P)
                                    ≡
                                    SuppTm (COT-to-Ctx ΓS) (stm-to-term (ap L P)))
                  → SuppSTy ΓS (lty L) ≡ SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty L))
                  → SuppLabel-WT ΓS L ≡ SuppSub (COT-to-Ctx ΓS) (label-to-sub L)

SuppSTm-to-term (incTree T) (SPath P) = SuppPath-to-term P
SuppSTm-to-term (incTree T) (SCoh S A L) = begin
  SuppLabel-WT (incTree T) L
    ≡⟨ SuppLabel-to-sub (incTree T) L ⟩
  SuppSub ⌊ T ⌋ (label-to-sub L)
    ≡˘⟨ cong (DC ⌊ T ⌋) (FVTm-coh-sub ⌊ S ⌋ (sty-to-type A) (label-to-sub L)) ⟩
  SuppTm ⌊ T ⌋ (Coh ⌊ S ⌋ (sty-to-type A) idSub [ label-to-sub L ]tm) ∎
SuppSTm-to-term (incTree (Join S T)) (SExt a) = begin
  wedge-susp-vs (susp-vs (SuppSTm (incTree S) a)) empty
    ≡⟨ cong (λ - → wedge-susp-vs (susp-vs -) empty) (SuppSTm-to-term (incTree S) a) ⟩
  wedge-susp-vs (susp-vs (SuppTm ⌊ S ⌋ (stm-to-term a))) empty
    ≡⟨ wedge-susp-vs-ext ⌊ S ⌋ (stm-to-term a) ⌊ T ⌋ ⟩
  SuppTm (wedge-susp ⌊ S ⌋ ⌊ T ⌋) (susp-tm (stm-to-term a) [ wedge-susp-inc-left _ _ ]tm) ∎
SuppSTm-to-term (incTree (Join S T)) (SShift a) = begin
  wedge-susp-vs empty (SuppSTm (incTree T) a)
    ≡⟨ cong (wedge-susp-vs empty) (SuppSTm-to-term (incTree T) a) ⟩
  wedge-susp-vs empty (SuppTm ⌊ T ⌋ (stm-to-term a))
    ≡⟨ wedge-susp-vs-shift ⌊ S ⌋ ⌊ T ⌋ (stm-to-term a) ⟩
  SuppTm (wedge-susp ⌊ S ⌋ ⌊ T ⌋) (stm-to-term a [ wedge-susp-inc-right _ _ ]tm) ∎
SuppSTm-to-term (incCtx Γ) (SCoh S A L) = begin
  SuppLabel-WT (incCtx Γ) L
    ≡⟨ SuppLabel-to-sub (incCtx Γ) L ⟩
  SuppSub Γ (label-to-sub L)
    ≡˘⟨ cong (DC Γ) (FVTm-coh-sub ⌊ S ⌋ (sty-to-type A) (label-to-sub L)) ⟩
  SuppTm Γ (Coh ⌊ S ⌋ (sty-to-type A) idSub [ label-to-sub L ]tm) ∎
SuppSTm-to-term (incCtx Γ) (SOther t) = refl

SuppSTy-to-type ΓS S⋆ = sym (DC-empty (COT-to-Ctx ΓS))
SuppSTy-to-type ΓS (SArr s As t) = begin
  SuppSTy ΓS As ∪ SuppSTm ΓS s ∪ SuppSTm ΓS t
    ≡⟨ cong₃ (λ a b c → a ∪ b ∪ c) (SuppSTy-to-type ΓS As)
                                   (SuppSTm-to-term ΓS s)
                                   (SuppSTm-to-term ΓS t) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type As) ∪
   SuppTm (COT-to-Ctx ΓS) (stm-to-term s) ∪
   SuppTm (COT-to-Ctx ΓS) (stm-to-term t)
    ≡˘⟨ cong (_∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)) (DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type As)) (FVTm (stm-to-term s))) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type As) ∪ FVTm (stm-to-term s)) ∪
   SuppTm (COT-to-Ctx ΓS) (stm-to-term t)
    ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type As) ∪ FVTm (stm-to-term s)) (FVTm (stm-to-term t)) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type As) ∪ FVTm (stm-to-term s) ∪ FVTm (stm-to-term t)) ∎

SuppLabel-to-sub ΓS L = SuppLabel-to-sub′ ΓS L (SuppSTm-to-term ΓS ∘ ap L) (SuppSTy-to-type ΓS (lty L))

SuppLabel-to-sub′ {S = Sing} ΓS L f p = begin
  SuppSTy ΓS (lty L) ∪ SuppSTm ΓS (ap L PHere)
    ≡⟨ cong₂ _∪_ p (f PHere) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty L)) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (ap L PHere))
    ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L))) (FVTm (stm-to-term (ap L PHere))) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L)) ∪ FVTm (stm-to-term (ap L PHere))) ∎
SuppLabel-to-sub′ {S = Join S T} ΓS L f p = begin
  SuppSTy ΓS (lty L) ∪
      (SuppSTm ΓS (ap L PHere) ∪
       SuppLabel ΓS (ap (label₁ L)) ∪
       SuppLabel ΓS (ap (label₂ L)))
    ≡⟨ cong
        (λ - →
           SuppSTy ΓS (lty L) ∪
           (SuppSTm ΓS (ap L PHere) ∪ SuppLabel ΓS (ap (label₁ L)) ∪ -))
        (SuppLabel-PHere-⊆ ΓS (ap (label₂ L))) ⟩
  SuppSTy ΓS (lty L) ∪
   (SuppSTm ΓS (ap L PHere)
    ∪ SuppLabel ΓS (ap (label₁ L))
    ∪ (SuppLabel ΓS (ap (label₂ L))
       ∪ SuppSTm ΓS (ap L (PShift PHere))))
    ≡⟨ prove 5 (var 0F ⊕ ((var 1F ⊕ var 2F) ⊕ (var 3F ⊕ var 4F)))
               ((((var 0F ⊕ var 1F) ⊕ var 4F) ⊕ var 2F) ⊕ (var 0F ⊕ var 3F))
               (SuppSTy ΓS (lty L) ∷
                SuppSTm ΓS (ap L PHere) ∷
                SuppLabel ΓS (ap (label₁ L)) ∷
                SuppLabel ΓS (ap (label₂ L)) ∷
                SuppSTm ΓS (ap L (PShift PHere)) ∷ emp) ⟩
  SuppSTy ΓS (lty L)
  ∪ SuppSTm ΓS (ap L PHere)
  ∪ SuppSTm ΓS (ap L (PShift PHere))
  ∪ SuppLabel ΓS (ap (label₁ L))
  ∪ (SuppSTy ΓS (lty L) ∪ SuppLabel ΓS (ap (label₂ L)))
    ≡⟨ cong₂ _∪_ (trans (SuppLabel-to-sub′ ΓS (label₁ L) (f ∘ PExt) l1)
                        (cong (DC (COT-to-Ctx ΓS)) (sym (↓-fv (label-to-sub (label₁ L))))))
                 (SuppLabel-to-sub′ ΓS (label₂ L) (f ∘ PShift) p) ⟩
  SuppSub (COT-to-Ctx ΓS) (↓ (label-to-sub (label₁ L)))
   ∪ SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₂ L))
    ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) _ _ ⟩
  DC (COT-to-Ctx ΓS)
   (FVSub (↓ (label-to-sub (label₁ L))) ∪ FVSub (label-to-sub (label₂ L)))
    ≡˘⟨ cong (DC (COT-to-Ctx ΓS)) (sub-from-wedge-vs (↓ (label-to-sub (label₁ L)))
                                                     (label-to-sub (label₂ L))
                                                     lem) ⟩
  SuppSub (COT-to-Ctx ΓS)
       (sub-from-wedge
        (↓ (label-to-sub (label₁ L)))
        (label-to-sub (label₂ L))) ∎
  where
    open Solver ∪-idempotentCommutativeMonoid

    lem : FVTm (Var (fromℕ _) [ label-to-sub (label₂ L) ]tm) ⊆ FVSub (↓ (label-to-sub (label₁ L)))
    lem = PR.begin
      FVTm (fromℕ _ [ label-to-sub (label₂ L) ]v)
        ≈⟨ FVTm-≃ (label-to-sub-phere (label₂ L)) ⟩
      FVTm (apt (label₂ L) PHere)
        ≤⟨ ∪-⊆-2 (FVTy (sty-to-type (lty L)) ∪ FVTm (apt L PHere)) (FVTm (apt L (PShift PHere))) ⟩
      FVTy (sty-to-type (lty (label₁ L)))
        ≤⟨ sub-type-⊆ (label-to-sub (label₁ L)) ⟩
      FVSub (label-to-sub (label₁ L))
        ≈˘⟨ ↓-fv (label-to-sub (label₁ L)) ⟩
      FVSub (↓ (label-to-sub (label₁ L))) PR.∎
      where
        module PR = PReasoning (⊆-poset _)
        open PR

    l1 : SuppSTy ΓS (lty (label₁ L)) ≡
          SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty (label₁ L)))
    l1 = begin
      SuppSTy ΓS (lty L)
        ∪ SuppSTm ΓS (ap L PHere)
        ∪ SuppSTm ΓS (ap L (PShift PHere))
        ≡⟨ cong₃ (λ a b c → a ∪ b ∪ c) p
                                       (f PHere)
                                       (f (PShift PHere)) ⟩
      SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty L)) ∪
       SuppTm (COT-to-Ctx ΓS) (apt L PHere)
       ∪ SuppTm (COT-to-Ctx ΓS) (apt L (PShift PHere))
        ≡˘⟨ cong (_∪ SuppTm (COT-to-Ctx ΓS) (apt L (PShift PHere))) (DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L))) (FVTm (apt L PHere))) ⟩
      DC (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L)) ∪ FVTm (apt L PHere))
       ∪ SuppTm (COT-to-Ctx ΓS) (apt L (PShift PHere))
        ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L)) ∪ FVTm (apt L PHere)) (FVTm (apt L (PShift PHere))) ⟩
      SuppTy (COT-to-Ctx ΓS)
      (apt L PHere ─⟨ sty-to-type (lty L) ⟩⟶
       apt L (PShift PHere)) ∎

SuppSTm-≃ : (ΓS : CtxOrTree n) → {a b : STm (COT-to-MT ΓS)} → a ≃stm b → SuppSTm ΓS a ≡ SuppSTm ΓS b
SuppSTm-≃ ΓS {a} {b} [ p ] = begin
  SuppSTm ΓS a
    ≡⟨ SuppSTm-to-term ΓS a ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term a)
    ≡⟨ cong (DC (COT-to-Ctx ΓS)) (FVTm-≃ p) ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term b)
    ≡˘⟨ SuppSTm-to-term ΓS b ⟩
  SuppSTm ΓS b ∎

SuppSTy-≃ : (ΓS : CtxOrTree n) → {a b : STy (COT-to-MT ΓS)} → a ≃sty b → SuppSTy ΓS a ≡ SuppSTy ΓS b
SuppSTy-≃ ΓS {a} {b} [ p ] = begin
  SuppSTy ΓS a
    ≡⟨ SuppSTy-to-type ΓS a ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type a)
    ≡⟨ cong (DC (COT-to-Ctx ΓS)) (FVTy-≃ p) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type b)
    ≡˘⟨ SuppSTy-to-type ΓS b ⟩
  SuppSTy ΓS b ∎

SuppLabel-≃ : (ΓS : CtxOrTree n) → {L M : Label (COT-to-MT ΓS) S} → L ≃l M → SuppLabel ΓS L ≡ SuppLabel ΓS M
SuppLabel-≃ ΓS {L} {M} p = begin
  SuppLabel ΓS L
    ≡˘⟨ ∪-left-unit (SuppLabel ΓS L) ⟩
  SuppLabel-WT ΓS (L ,, S⋆)
    ≡⟨ SuppLabel-to-sub ΓS (L ,, S⋆) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (L ,, S⋆))
    ≡⟨ cong (DC (COT-to-Ctx ΓS)) (FVSub-≃ (label-to-sub-≃ (L ,, S⋆) (M ,, S⋆) p refl≃sty)) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (M ,, S⋆))
    ≡˘⟨ SuppLabel-to-sub ΓS (M ,, S⋆) ⟩
  SuppLabel-WT ΓS (M ,, S⋆)
    ≡⟨ ∪-left-unit (SuppLabel ΓS M) ⟩
  SuppLabel ΓS M ∎

SuppLabel′-map : (f : Path S → VarSet n)
               → (g : VarSet n → VarSet m)
               → (p : ∀ xs ys → g xs ∪ g ys ≡ g (xs ∪ ys))
               → SuppLabel′ (g ∘ f) ≡ g (SuppLabel′ f)
SuppLabel′-map {S = Sing} f g p = refl
SuppLabel′-map {S = Join S T} f g p = begin
  g (f PHere) ∪ SuppLabel′ (g ∘ f ∘ PExt) ∪ SuppLabel′ (g ∘ f ∘ PShift)
    ≡⟨ cong₂ (λ a b → g (f PHere) ∪ a ∪ b) (SuppLabel′-map (f ∘ PExt) g p) (SuppLabel′-map (f ∘ PShift) g p) ⟩
  g (f PHere) ∪ g (SuppLabel′ (f ∘ PExt)) ∪ g (SuppLabel′ (f ∘ PShift))
    ≡⟨ cong (_∪ g (SuppLabel′ (f ∘ PShift))) (p (f PHere) (SuppLabel′ (f ∘ PExt))) ⟩
  g (f PHere ∪ SuppLabel′ (f ∘ PExt)) ∪ g (SuppLabel′ (f ∘ PShift))
    ≡⟨ p (f PHere ∪ SuppLabel′ (f ∘ PExt)) (SuppLabel′ (f ∘ PShift)) ⟩
  g (f PHere ∪ SuppLabel′ (f ∘ PExt) ∪ SuppLabel′ (f ∘ PShift)) ∎



SuppLabel-ext : {S : Tree m}
              → (L : Label (someTree S) U)
              → (T : Tree n)
              → SuppLabel (incTree (Join S T)) (SExt ∘ L)
                ≡
                wedge-susp-vs (susp-vs (SuppLabel (incTree S) L)) empty
SuppLabel-ext {S = S} L T
  = SuppLabel′-map (SuppSTm (incTree S) ∘ L)
                   (λ - → wedge-susp-vs (susp-vs -) empty)
                   λ xs ys → begin
                     wedge-susp-vs (susp-vs xs) empty ∪ wedge-susp-vs (susp-vs ys) empty
                       ≡⟨ wedge-vs-∪ (susp-vs xs) (susp-vs ys) empty empty get-snd ⟩
                     wedge-susp-vs (susp-vs xs ∪ susp-vs ys) (empty ∪ empty)
                       ≡⟨ cong₂ wedge-susp-vs (susp-vs-∪ xs ys) (∪-idem empty) ⟩
                     wedge-susp-vs (susp-vs (xs ∪ ys)) empty ∎

SuppLabel-shift : {T : Tree m}
                → (L : Label (someTree T) U)
                → (S : Tree n)
                → SuppLabel (incTree (Join S T)) (SShift ∘ L)
                  ≡
                  wedge-susp-vs empty (SuppLabel (incTree T) L)
SuppLabel-shift {T = T} L S
  = SuppLabel′-map (SuppSTm (incTree T) ∘ L)
                   (λ - → wedge-susp-vs empty -)
                   λ xs ys → begin
                     wedge-susp-vs empty xs ∪ wedge-susp-vs empty ys
                       ≡⟨ wedge-vs-∪ empty empty xs ys get-snd ⟩
                     wedge-susp-vs (empty ∪ empty) (xs ∪ ys)
                       ≡⟨ cong (λ - → wedge-susp-vs - (xs ∪ ys)) (∪-idem empty) ⟩
                     wedge-susp-vs empty (xs ∪ ys) ∎
