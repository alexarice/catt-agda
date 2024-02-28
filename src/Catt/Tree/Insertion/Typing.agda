open import Catt.Typing.Rule

module Catt.Tree.Insertion.Typing (rules : RuleSet)
                                  (tame : Tame rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Globular.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Standard
open import Catt.Tree.Standard.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties

open import Catt.Typing rules
open import Catt.Tree.Structured.Typing rules
open import Catt.Tree.Structured.Typing.Properties rules tame
open import Catt.Tree.Standard.Typing rules tame

ι-Ty : (S : Tree n)
     → (p : Branch S d)
     → (T : Tree m)
     → .⦃ _ : has-trunk-height d T ⦄
     → Typing-Label ⌊ S >>[ p ] T ⌋ (ι S p T ,, S⋆)
ι-Ty (Join S₁ S₂) BHere T = ++t-inc-left-Ty T S₂
ι-Ty (Join S₁ S₂) (BExt p) (Susp T)
  = ↓-label-Ty (map-ext-Ty (ι-Ty S₁ p T)) (map-sty-ext-Ty TySStar)
ι-Ty (Join S₁ S₂) (BShift p) T = map-shift-Ty (ι-Ty S₂ p T)

κ-Ty : (S : Tree n)
     → (P : Branch S d)
     → (T : Tree m)
     → .⦃ _ : has-trunk-height d T ⦄
     → Typing-Label ⌊ S >>[ P ] T ⌋ (κ S P T ,, S⋆)
κ-Ty (Join S₁ S₂) BHere T
  = label-between-++t-Ty (replace-label-Ty (standard-label-Ty (Susp S₁) T)
                                                     (TySPath PHere)
                                                     (reflexive≈stm (standard-label-fst (Susp S₁) T)))
                                   (id-label-Ty S₂)
                                   (reflexive≈stm (standard-label-last (Susp S₁) T))
                                   refl≈stm
κ-Ty (Join S₁ S₂) (BExt p) (Susp T)
  = label-between-joins-Ty (κ-Ty S₁ p T)
                           (id-label-Ty S₂)
                           refl≈stm
κ-Ty (Join S₁ S₂) (BShift p) T
  = label-between-joins-Ty (id-label-Ty S₁)
                           (κ-Ty S₂ p T)
                           (reflexive≈stm (κ-phere S₂ p T) )

label-from-insertion-lem : (S₁ : Tree n)
                         → (S₂ : Tree m)
                         → (T : Tree l)
                         → (As : STy (someTree S₁))
                         → (L : Label X (Join S₁ S₂))
                         → (M : Label X T)
                         → (d : ℕ)
                         → .⦃ NonZero d ⦄
                         → map-sty-ext As >>=′ (L ,, Cs) ≈[ Γ ]sty standard-sty d T >>=′ (M ,, Cs)
                         → SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (L ,, Cs)
                           ≈[ Γ ]sty
                           SArr SHere S⋆ (SPath (last-path T)) >>=′ (M ,, Cs)
label-from-insertion-lem {Cs = Cs} S₁ S₂ T As L M d p = begin
  SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (L ,, Cs)
    ≈˘⟨ reflexive≈sty (>>=′-≃ (truncate-sty-1-map-ext As) refl≃l refl≃sty) ⟩
  truncate-sty 1 (map-sty-ext As) >>=′ (L ,, Cs)
    ≈˘⟨ reflexive≈sty (truncate-sty-label 1 (map-sty-ext As) (L ,, Cs)) ⟩
  truncate-sty (1 + sty-dim Cs) (map-sty-ext As >>=′ (L ,, Cs))
    ≈⟨ truncate-sty-≈ {d = 1 + sty-dim Cs} refl p ⟩
  truncate-sty (1 + sty-dim Cs) (standard-sty d T >>=′ (M ,, Cs))
    ≈⟨ reflexive≈sty (truncate-sty-label 1 (standard-sty d T) (M ,, Cs)) ⟩
  truncate-sty 1 (standard-sty d T) >>=′ (M ,, Cs)
    ≈⟨ reflexive≈sty (>>=′-≃ (truncate-sty-1-1-Full (standard-sty d T)) (refl≃l {L = M}) refl≃sty) ⟩
  SArr SHere S⋆ (SPath (last-path T)) >>=′ (M ,, Cs) ∎
  where
    open Reasoning sty-setoid-≈

label-from-insertion-phere : (L : Label X S)
                           → (P : Branch S l)
                           → {T : Tree m}
                           → (M : Label X T)
                           → .⦃ _ : has-trunk-height l T ⦄
                           → (d : ℕ)
                           → .⦃ NonZero d ⦄
                           → branch-type S P >>=′ (L ,, Bs) ≈[ Γ ]sty standard-sty d T >>=′ (M ,, Bs)
                           → (L >>l[ P ] M) PHere ≈[ Γ ]stm L PHere
label-from-insertion-phere {S = Join S₁ S₂} {Bs = Bs} L BHere {T} M d p = begin
  (M ++l L ∘ PShift) PHere
    ≈⟨ reflexive≈stm (++l-phere M (L ∘ PShift)) ⟩
  M PHere
    ≈˘⟨ ≈SArr-proj₁ lem ⟩
  L PHere ∎
  where
    l2 : map-sty-ext (standard-sty (tree-dim S₁) S₁) >>=′ (L ,, Bs)
         ≈[ _ ]sty
         standard-sty d T >>=′ (M ,, Bs)
    l2 = begin
      map-sty-ext (standard-sty (tree-dim S₁) S₁) >>=′ (L ,, Bs)
        ≈˘⟨ reflexive≈sty (>>=′-≃ (map-sty-ext-≃ (disc-sty-is-standard S₁)) refl≃l refl≃sty) ⟩
      map-sty-ext (disc-sty S₁) >>=′ (L ,, Bs)
        ≈⟨ p ⟩
      standard-sty d T >>=′ (M ,, Bs) ∎
      where
        open Reasoning sty-setoid-≈
    open Reasoning stm-setoid-≈

    lem : SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (L ,, Bs) ≈[ _ ]sty SArr SHere S⋆ (SPath (last-path T)) >>=′ (M ,, Bs)
    lem = label-from-insertion-lem S₁ S₂ T (standard-sty (tree-dim S₁) S₁) L M d l2
label-from-insertion-phere {S = Join S₁ S₂} L (BExt P) {Susp T} M d p = sym≈stm (≈SArr-proj₁ lem)
  where
    lem : SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (L ,, _) ≈[ _ ]sty SArr SHere S⋆ (SPath (last-path (Susp T))) >>=′ (M ,, _)
    lem = label-from-insertion-lem S₁ S₂ (Susp T) (branch-type S₁ P) L M d p
label-from-insertion-phere L (BShift P) M d p = refl≈stm

label-from-insertion-Ty : {L : Label X S}
                        → Typing-Label Γ (L ,, As)
                        → (P : Branch S l)
                        → {T : Tree m}
                        → {M : Label X T}
                        → Typing-Label Γ (M ,, As)
                        → .⦃ _ : has-trunk-height l T ⦄
                        → branch-type S P >>=′ (L ,, As)
                          ≈[ Γ ]sty
                          standard-sty (lh P) T >>=′ (M ,, As)
                        → Typing-Label Γ (L >>l[ P ] M ,, As)
label-from-insertion-Ty {S = Join S₁ S₂} {As = As} {L = L} (TyJoin x Lty Lty′) BHere {T} {M} Mty p
  = ++l-Ty Mty Lty′ (sym≈stm (≈SArr-proj₃ lem))
  where
    lem : SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (L ,, As) ≈[ _ ]sty SArr SHere S⋆ (SPath (last-path T)) >>=′ (M ,, As)
    lem = label-from-insertion-lem S₁ S₂ T (disc-sty S₁) L M (suc (tree-dim S₁)) p
label-from-insertion-Ty {S = Join S₁ S₂} {As = As} {L = L} (TyJoin x LTy LTy′) (BExt {n = n} P) {Susp T} {M} (TyJoin y MTy (TySing z)) p
  = TyJoin y (label-from-insertion-Ty (label-typing-conv LTy lem) P MTy lem2) (replace-label-Ty LTy′ z (≈SArr-proj₃ lem))
  where
    lem : (SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (L ,, As)) ≈[ _ ]sty
            (SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (M ,, As))
    lem = label-from-insertion-lem S₁ S₂ (Susp T) (branch-type S₁ P) L M (suc (lh P)) p

    open Reasoning sty-setoid-≈

    lem2 : branch-type S₁ P >>=′
             ((L ∘ PExt) ,, SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (M ,, As))
             ≈[ _ ]sty
           standard-sty (lh P) T >>=′
             ((M ∘ PExt) ,, SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (M ,, As))
    lem2 = begin
      branch-type S₁ P >>=′
        (L ∘ PExt ,, SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (M ,, As))
        ≈˘⟨ >>=′-≈ (branch-type S₁ P) refl≈l lem ⟩
      branch-type S₁ P >>=′ (label₁ (L ,, As))
        ≈˘⟨ reflexive≈sty (map-sty-ext-label (branch-type S₁ P) (L ,, As)) ⟩
      map-sty-ext (branch-type S₁ P) >>=′ (L ,, As)
        ≈⟨ p ⟩
      standard-sty (suc (lh P)) (Susp T) >>=′ (M ,, As)
        ≈˘⟨ reflexive≈sty (>>=′-≃ (standard-sty-susp-lem (lh P) T) refl≃l refl≃sty) ⟩
      susp-sty (standard-sty (lh P) T) >>=′ (M ,, As)
        ≈˘⟨ reflexive≈sty (>>=′-≃ (map-sty-ext-susp-compat (standard-sty (lh P) T)) refl≃l refl≃sty) ⟩
      map-sty-ext (standard-sty (lh P) T) >>=′ (M ,, As)
        ≈⟨ reflexive≈sty (map-sty-ext-label (standard-sty (lh P) T) (M ,, As)) ⟩
      standard-sty (lh P) T >>=′ (label₁ (M ,, As)) ∎

label-from-insertion-Ty {S = Join S₁ S₂} {As = As} {L = L} (TyJoin x Lty Lty′) (BShift {n = n} P) {T} {M} Mty p
  = TyJoin x (label-typing-conv Lty (≈SArr refl≈stm
                                           refl≈sty
                                           (sym≈stm (label-from-insertion-phere (L ∘ PShift) P M (lh P) lem))))
             (label-from-insertion-Ty Lty′ P Mty lem)

  where
    open Reasoning sty-setoid-≈
    lem : branch-type S₂ P >>=′ ((L ∘ PShift) ,, As)
          ≈[ _ ]sty
          standard-sty (lh P) T >>=′ (M ,, As)
    lem = begin
      branch-type S₂ P >>=′ ((L ∘ PShift) ,, As)
        ≈˘⟨ reflexive≈sty (map-sty-shift-label (branch-type S₂ P) (L ,, As)) ⟩
      map-sty-shift (branch-type S₂ P) >>=′ (L ,, As)
        ≈⟨ p ⟩
      standard-sty (lh P) T >>=′ (M ,, As) ∎

label-from-insertion-eq : (L : Label X S)
                        → (P : Branch S l)
                        → {T : Tree m}
                        → (M : Label X T)
                        → .⦃ _ : has-trunk-height l T ⦄
                        → branch-type S P >>=′ (L ,, As) ≈[ Γ ]sty standard-sty (lh P) T >>=′ (M ,, As)
                        → L >>l[ P ] M ≈[ Γ ]l L >>l′[ P ] M
label-from-insertion-eq {S = Join S₁ S₂} L BHere {T} M p
  = trans≈l (++l-eq M (L ∘ PShift) (sym≈stm (≈SArr-proj₃ lem)))
            (sym≈l (replace-label-eq (M ++l′ L ∘ PShift)
                                     (L PHere)
                                     (trans≈stm (≈SArr-proj₁ lem) (++l′-phere M (L ∘ PShift) (sym≈stm (≈SArr-proj₃ lem))))))
  where
    lem : SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (L ,, _) ≈[ _ ]sty SArr SHere S⋆ (SPath (last-path T)) >>=′ (M ,, _)
    lem = label-from-insertion-lem S₁ S₂ T (disc-sty S₁) L M (suc (tree-dim S₁)) p
label-from-insertion-eq {S = Join S₁ S₂} {As = As} L (BExt {n = n} P) {Susp T} M p = γ
  where
    lem : (SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (M ,, As))
          ≈[ _ ]sty
          (SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (L ,, As))
    lem = sym≈sty (label-from-insertion-lem S₁ S₂ (Susp T) (branch-type S₁ P) L M (suc (lh P)) p)

    open Reasoning sty-setoid-≈

    lem2 : branch-type S₁ P >>=′
             ((L ∘ PExt) ,, SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (M ,, As))
             ≈[ _ ]sty
           standard-sty (lh P) T >>=′
             ((M ∘ PExt) ,, SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (M ,, As))
    lem2 = begin
      branch-type S₁ P >>=′
        (L ∘ PExt ,, SArr SHere S⋆ (SPath (PShift PHere)) >>=′ (M ,, As))
        ≈⟨ >>=′-≈ (branch-type S₁ P) refl≈l lem ⟩
      branch-type S₁ P >>=′ (label₁ (L ,, As))
        ≈˘⟨ reflexive≈sty (map-sty-ext-label (branch-type S₁ P) (L ,, As)) ⟩
      map-sty-ext (branch-type S₁ P) >>=′ (L ,, As)
        ≈⟨ p ⟩
      standard-sty (suc (lh P)) (Susp T) >>=′ (M ,, As)
        ≈˘⟨ reflexive≈sty (>>=′-≃ (standard-sty-susp-lem (lh P) T) refl≃l refl≃sty) ⟩
      susp-sty (standard-sty (lh P) T) >>=′ (M ,, As)
        ≈˘⟨ reflexive≈sty (>>=′-≃ (map-sty-ext-susp-compat (standard-sty (lh P) T)) refl≃l refl≃sty) ⟩
      map-sty-ext (standard-sty (lh P) T) >>=′ (M ,, As)
        ≈⟨ reflexive≈sty (map-sty-ext-label (standard-sty (lh P) T) (M ,, As)) ⟩
      standard-sty (lh P) T >>=′ (label₁ (M ,, As)) ∎

    γ : L >>l[ BExt P ] M
        ≈[ _ ]l
        L >>l′[ BExt P ] M
    γ .get PHere = ≈SArr-proj₁ lem
    γ .get (PExt Z) = label-from-insertion-eq (L ∘ PExt) P (M ∘ PExt) lem2 .get Z
    γ .get (PShift Z) = replace-label-eq (L ∘ PShift) (M (PShift PHere)) (≈SArr-proj₃ lem) .get Z

label-from-insertion-eq L (BShift P) M p .get PHere = refl≈stm
label-from-insertion-eq L (BShift P) M p .get (PExt Z) = refl≈stm
label-from-insertion-eq {S = Join S₁ S₂} {As = As} L (BShift {n = n} P) {T} M p .get (PShift Z)
  = label-from-insertion-eq (L ∘ PShift) P M lem .get Z
  where
    open Reasoning sty-setoid-≈
    lem : branch-type S₂ P >>=′ ((L ∘ PShift) ,, As)
          ≈[ _ ]sty
          standard-sty (lh P) T >>=′ (M ,, As)
    lem = begin
      branch-type S₂ P >>=′ ((L ∘ PShift) ,, As)
        ≈˘⟨ reflexive≈sty (map-sty-shift-label (branch-type S₂ P) (L ,, As)) ⟩
      map-sty-shift (branch-type S₂ P) >>=′ (L ,, As)
        ≈⟨ p ⟩
      standard-sty (lh P) T >>=′ (M ,, As) ∎

⌊⌋p-Ty : (P : Branch S l) → Typing-STm ⌊ S ⌋ (SPath ⌊ P ⌋p) (branch-type S P)
⌊⌋p-Ty P = TySConv (TySPath ⌊ P ⌋p) (reflexive≈sty (branch-type-is-path-type P))
