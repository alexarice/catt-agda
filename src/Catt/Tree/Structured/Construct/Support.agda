module Catt.Tree.Structured.Construct.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Wedge.Support
open import Catt.Suspension.Support
open import Catt.Tree.Structured.Support

import Algebra.Solver.IdempotentCommutativeMonoid as Solver
open import Tactic.MonoidSolver

open ≡-Reasoning

id-label-full : (T : Tree n) → SuppLabel (incTree T) (id-label T) ≡ full
id-label-full Sing = refl
id-label-full (Join S T) = begin
  trueAt (fromℕ _)
  ∪ SuppLabel (incTree (Join S T)) (SExt ∘ id-label S)
  ∪ SuppLabel (incTree (Join S T)) (SShift ∘ id-label T)
    ≡⟨ cong₂ (λ a b → trueAt (fromℕ _) ∪ a ∪ b)
             (SuppLabel-ext (id-label S) T)
             (SuppLabel-shift (id-label T) S) ⟩
  trueAt (fromℕ _)
  ∪ wedge-susp-vs (susp-vs (SuppLabel (incTree S) (id-label S))) empty
  ∪ wedge-susp-vs empty (SuppLabel (incTree T) (id-label T))
    ≡⟨ ∪-assoc _ _ _ ⟩
  trueAt (fromℕ _)
  ∪ (wedge-susp-vs (susp-vs (SuppLabel (incTree S) (id-label S))) empty
     ∪ wedge-susp-vs empty (SuppLabel (incTree T) (id-label T)))
    ≡⟨ cong (trueAt (fromℕ _) ∪_) (wedge-vs-∪ (susp-vs (SuppLabel (incTree S) (id-label S)))
                                              empty
                                              empty
                                              (SuppLabel (incTree T) (id-label T))
                                              get-snd) ⟩
  trueAt (fromℕ _)
  ∪ wedge-susp-vs (susp-vs (SuppLabel (incTree S) (id-label S)) ∪ empty)
                  (empty ∪ SuppLabel (incTree T) (id-label T))
    ≡⟨ cong₂ (λ a b → trueAt (fromℕ _) ∪ wedge-susp-vs a b)
             (trans (∪-right-unit _) (trans (cong susp-vs (id-label-full S)) susp-vs-full))
             (trans (∪-left-unit _) (id-label-full T)) ⟩
  trueAt (fromℕ _) ∪ wedge-susp-vs full full
    ≡⟨ cong (trueAt (fromℕ _) ∪_) (wedge-vs-full _ get-snd _) ⟩
  trueAt (fromℕ _) ∪ full
    ≡⟨ ∪-right-zero (trueAt (fromℕ _)) ⟩
  full ∎

id-label-wt-full : (T : Tree n) → SuppLabel-WT (incTree T) (id-label-wt T) ≡ full
id-label-wt-full T = begin
  SuppLabel-WT (incTree T) (id-label-wt T)
    ≡⟨ ∪-left-unit (SuppLabel (incTree T) (id-label T)) ⟩
  SuppLabel (incTree T) (id-label T)
    ≡⟨ id-label-full T ⟩
  full ∎

ppath-≃-full : (p : S ≃′ T) → SuppLabel (incTree T) (SPath ∘ ppath-≃ p) ≡ full
ppath-≃-full {S = S} {T = T} p with ≃-to-same-n (≃′-to-≃ p)
... | refl with ≃-to-≡ (≃′-to-≃ p)
... | refl = begin
  SuppLabel (incTree T) (SPath ∘ ppath-≃ p)
    ≡⟨ SuppLabel-≃ (incTree T) {L = SPath ∘ ppath-≃ p} {M = id-label T} [ (λ P → SPath≃ (sym≃p (ppath-≃-≃p p P))) ] ⟩
  SuppLabel (incTree T) (id-label T)
    ≡⟨ id-label-full T ⟩
  full ∎

extend-disc-label-supp : (ΓS : CtxOrTree m)
                       → (L : Label (COT-to-MT ΓS) S)
                       → .⦃ _ : is-linear S ⦄
                       → (t : STm (COT-to-MT ΓS))
                       → (a : STm (COT-to-MT ΓS))
                       → SuppLabel ΓS (extend-disc-label L t a)
                         ≡
                         SuppLabel ΓS L ∪ SuppSTm ΓS t ∪ SuppSTm ΓS a
extend-disc-label-supp {S = Sing} ΓS L t a
  = prove 3 ((var 0F ⊕ var 1F) ⊕ var 2F)
            ((var 0F ⊕ var 2F) ⊕ var 1F)
            (SuppSTm ΓS (L PHere) ∷ SuppSTm ΓS a ∷ SuppSTm ΓS t ∷ emp)
  where
    open Solver ∪-idempotentCommutativeMonoid
extend-disc-label-supp {S = Susp S} ΓS L t a = begin
  SuppSTm ΓS (L PHere)
  ∪ SuppLabel ΓS (extend-disc-label (L ∘ PExt) t a)
  ∪ SuppSTm ΓS (L (PShift PHere))
    ≡⟨ cong (λ - → SuppSTm ΓS (L PHere) ∪ - ∪ SuppSTm ΓS (L (PShift PHere)))
            (extend-disc-label-supp ΓS (L ∘ PExt) t a) ⟩
  SuppSTm ΓS (L PHere)
  ∪ (SuppLabel ΓS (L ∘ PExt) ∪ SuppSTm ΓS t ∪ SuppSTm ΓS a)
  ∪ SuppSTm ΓS (L (PShift PHere))
    ≡⟨ prove 5 ((var 0F ⊕ ((var 1F ⊕ var 2F) ⊕ var 3F)) ⊕ var 4F)
               ((((var 0F ⊕ var 1F) ⊕ var 4F) ⊕ var 2F) ⊕ var 3F)
               (SuppSTm ΓS (L PHere) ∷
                SuppLabel ΓS (L ∘ PExt) ∷
                SuppSTm ΓS t ∷
                SuppSTm ΓS a ∷
                SuppSTm ΓS (L (PShift PHere)) ∷ emp) ⟩
  SuppLabel ΓS L ∪ SuppSTm ΓS t ∪ SuppSTm ΓS a ∎
  where
    open Solver ∪-idempotentCommutativeMonoid

stm-to-label-supp : (ΓS : CtxOrTree m)
                  → (S : Tree n)
                  → .⦃ _ : is-linear S ⦄
                  → (a : STm (COT-to-MT ΓS))
                  → (As : STy (COT-to-MT ΓS))
                  → .⦃ _ : has-dim (tree-dim S) As ⦄
                  → SuppLabel ΓS (stm-to-label S a As) ≡ SuppSTy ΓS As ∪ SuppSTm ΓS a
stm-to-label-supp ΓS Sing a S⋆ = sym (∪-left-unit (SuppSTm ΓS a))
stm-to-label-supp ΓS (Susp S) a (SArr s As t) = begin
  SuppLabel ΓS (extend-disc-label (stm-to-label S s As) t a)
    ≡⟨ extend-disc-label-supp ΓS (stm-to-label S s As) t a ⟩
  SuppLabel ΓS (stm-to-label S s As) ∪ SuppSTm ΓS t ∪ SuppSTm ΓS a
    ≡⟨ cong (λ - → - ∪ SuppSTm ΓS t ∪ SuppSTm ΓS a) (stm-to-label-supp ΓS S s As) ⟩
  SuppSTy ΓS (SArr s As t) ∪ SuppSTm ΓS a ∎

++t-incs-full : (S : Tree n) → (T : Tree m)
              → SuppLabel (incTree (S ++t T)) (ap (++t-inc-left S T))
                ∪ SuppLabel (incTree (S ++t T)) (ap (++t-inc-right S T))
                ≡ full
++t-incs-full Sing T = begin
  trueAt (fromℕ _) ∪ SuppLabel (incTree T) (id-label T)
    ≡⟨ cong (trueAt (fromℕ _) ∪_) (id-label-full T) ⟩
  trueAt (fromℕ _) ∪ full
    ≡⟨ ∪-right-zero (trueAt (fromℕ _)) ⟩
  full ∎
++t-incs-full (Join S₁ S₂) T = begin
  trueAt (fromℕ _)
   ∪ SuppLabel _ (SExt {T = S₂ ++t T} ∘ id-label S₁)
   ∪ SuppLabel _ (SShift {S = S₁} ∘ ap (++t-inc-left S₂ T) )
   ∪ SuppLabel _ (SShift {S = S₁} ∘ ap (++t-inc-right S₂ T))
    ≡⟨ cong₃ (λ a b c → trueAt (fromℕ _) ∪ a ∪ b ∪ c)
             (SuppLabel-ext (id-label S₁) (S₂ ++t T))
             (SuppLabel-shift (ap (++t-inc-left S₂ T)) S₁)
             (SuppLabel-shift (ap (++t-inc-right S₂ T)) S₁) ⟩
  trueAt (fromℕ (++t-length S₂ T + (2 + tree-size S₁))) ∪
   wedge-susp-vs (susp-vs (SuppLabel (incTree S₁) (id-label S₁)))
   empty
   ∪
   wedge-susp-vs empty
   (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-left S₂ T)))
   ∪
   wedge-susp-vs empty
   (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-right S₂ T)))
    ≡⟨ solve (∪-monoid {n = suc (++t-length S₂ T + (2 + tree-size S₁))}) ⟩
  trueAt (fromℕ _) ∪
   (wedge-susp-vs (susp-vs (SuppLabel (incTree S₁) (id-label S₁)))
   empty
   ∪
   (wedge-susp-vs empty
   (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-left S₂ T)))
   ∪
   wedge-susp-vs empty
   (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-right S₂ T)))))
    ≡⟨ cong (trueAt (fromℕ _) ∪_) lem ⟩
  trueAt (fromℕ _) ∪ full
    ≡⟨ ∪-right-zero _ ⟩
  full ∎
  where
    lem : wedge-susp-vs (susp-vs (SuppLabel (incTree S₁) (id-label S₁)))
           empty
           ∪
           (wedge-susp-vs empty
            (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-left S₂ T)))
            ∪
            wedge-susp-vs empty
            (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-right S₂ T))))
           ≡ full
    lem = begin
      wedge-susp-vs (susp-vs (SuppLabel (incTree S₁) (id-label S₁)))
       empty
       ∪
       (wedge-susp-vs empty
        (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-left S₂ T)))
        ∪
        wedge-susp-vs empty
        (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-right S₂ T))))
        ≡⟨ cong₂ (λ a b → wedge-susp-vs (susp-vs a) empty ∪ b)
                 (id-label-full S₁)
                 (wedge-vs-∪ empty empty (SuppLabel (incTree (S₂ ++t T)) (ap (++t-inc-left S₂ T)))
                                         (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-right S₂ T)))
                                         get-snd) ⟩
      wedge-susp-vs (susp-vs full) empty ∪
       wedge-susp-vs (empty ∪ empty)
       (SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-left S₂ T)) ∪
        SuppLabel (incTree (S₂ ++t T)) (proj₁ (++t-inc-right S₂ T)))
        ≡⟨ cong₃ (λ a b c → wedge-susp-vs a empty ∪ wedge-susp-vs b c)
                 susp-vs-full
                 (∪-idem empty)
                 (++t-incs-full S₂ T) ⟩
      wedge-susp-vs full empty ∪
       wedge-susp-vs empty full
        ≡⟨ wedge-vs-∪ full empty empty full get-snd ⟩
      wedge-susp-vs (full ∪ empty) (empty ∪ full)
        ≡⟨ cong₂ wedge-susp-vs (∪-right-unit full) (∪-left-unit full) ⟩
      wedge-susp-vs full full
        ≡⟨ wedge-vs-full (2+ _) get-snd (++t-length S₂ T) ⟩
      full ∎
