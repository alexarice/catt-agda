module Catt.Tree.Structured.Construct.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Discs
open import Catt.Discs.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Globular.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

connect-tree-inc-left-phere : (S : Tree n)
                            → (T : Tree m)
                            → connect-tree-inc-left′ S T PHere ≃p PHere {S = connect-tree S T}
connect-tree-inc-left-phere Sing T = refl≃p
connect-tree-inc-left-phere (Join S₁ S₂) T = refl≃p

connect-tree-inc-phere : (S : Tree n)
                       → (T : Tree m)
                       → connect-tree-inc-left′ S T (last-path S) ≃p connect-tree-inc-right′ S T PHere
connect-tree-inc-phere Sing T = refl≃p
connect-tree-inc-phere (Join S₁ S₂) T = Shift≃ refl≃ (connect-tree-inc-phere S₂ T)

connect-tree-inc-right-last-path : (S : Tree n)
                                 → (T : Tree m)
                                 → connect-tree-inc-right′ S T (last-path T) ≃p last-path (connect-tree S T)
connect-tree-inc-right-last-path Sing T = refl≃p
connect-tree-inc-right-last-path (Join S₁ S₂) T = Shift≃ refl≃ (connect-tree-inc-right-last-path S₂ T)


lift-stm-to-term : (a : STm (Other n)) → stm-to-term (lift-stm a) ≃tm lift-tm (stm-to-term a)
lift-sty-to-type : (A : STy (Other n)) → sty-to-type (lift-sty A) ≃ty lift-ty (sty-to-type A)
lift-label-to-sub′ : (L : Label-WT (Other n) S) → ((P : Path S) → apt (lift-label L) P ≃tm lift-tm (apt L P)) → sty-to-type (lift-sty (lty L)) ≃ty lift-ty (sty-to-type (lty L)) → label-to-sub (lift-label L) ≃s lift-sub (label-to-sub L)
lift-label-to-sub : (L : Label-WT (Other n) S) → label-to-sub (lift-label L) ≃s lift-sub (label-to-sub L)

lift-stm-to-term (SCoh S A L) = begin
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub (lift-label L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type A) idSub}) (lift-label-to-sub L) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ lift-sub (label-to-sub L) ]tm >tm
    ≈⟨ apply-lifted-sub-tm-≃ (Coh (tree-to-ctx S) (sty-to-type A) idSub) (label-to-sub L) ⟩
  < lift-tm (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) >tm ∎
  where
    open Reasoning tm-setoid
lift-stm-to-term (SOther t) = refl≃tm

lift-sty-to-type S⋆ = refl≃ty
lift-sty-to-type (SArr s A t) = Arr≃ (lift-stm-to-term s) (lift-sty-to-type A) (lift-stm-to-term t)

lift-label-to-sub′ {S = Sing} L f p = Ext≃ (Null≃ p) (f PHere)
lift-label-to-sub′ {S = Join S T} L f p = begin
  < sub-from-connect (unrestrict (label-to-sub (lift-label (label₁ L)))) (label-to-sub (lift-label (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (lift-label-to-sub′ (label₁ L) (λ P → f (PExt P)) (Arr≃ (f PHere) p (f (PShift PHere))))) (lift-label-to-sub′ (label₂ L) (λ P → f (PShift P)) p) ⟩
  < sub-from-connect (unrestrict (lift-sub (label-to-sub (label₁ L)))) (lift-sub (label-to-sub (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-lift (label-to-sub (label₁ L))) (refl≃s {σ = lift-sub (label-to-sub (label₂ L))}) ⟩
  < sub-from-connect (lift-sub (unrestrict (label-to-sub (label₁ L)))) (lift-sub (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-lift (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < lift-sub (sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))) >s ∎
  where
    open Reasoning sub-setoid

lift-label-to-sub L = lift-label-to-sub′ L (λ P → lift-stm-to-term (ap L P)) (lift-sty-to-type (lty L))

connect-tree-inc-left-unit : (T : Tree n)
                           → connect-tree-inc-left′ T Sing ≃lp (λ Z → Z)
connect-tree-inc-left-unit Sing .get PHere = refl≃p
connect-tree-inc-left-unit (Join S T) .get PHere = Here≃ (≃′-to-≃ (Join≃′ Refl≃′ (connect-tree-right-unit T)))
connect-tree-inc-left-unit (Join S T) .get (PExt Z) = Ext≃ refl≃p (≃′-to-≃ (connect-tree-right-unit T))
connect-tree-inc-left-unit (Join S T) .get (PShift Z) = Shift≃ refl≃ (connect-tree-inc-left-unit T .get Z)

connect-label-right-unit : (L : Label X S)
                         → (M : Label X Sing)
                         → connect-label L M ≃l label-≃ (connect-tree-right-unit S) L
connect-label-right-unit {S = Sing} L M .get PHere = refl≃stm
connect-label-right-unit {S = Join S T} L M .get PHere = refl≃stm
connect-label-right-unit {S = Join S T} L M .get (PExt Z) = refl≃stm
connect-label-right-unit {S = Join S T} L M .get (PShift Z) = connect-label-right-unit (L ∘ PShift) M .get Z

stm-≃-spath : (p : S ≃′ T)
            → (P : Path S)
            → stm-≃ p (SPath P) ≃stm SPath (ppath-≃ p P)
stm-≃-spath Refl≃′ P = refl≃stm
stm-≃-spath (Join≃′ p q) P = refl≃stm

replace-not-here : (L : Label X S) → (a : STm X) → (P : Path S) → .⦃ not-here P ⦄ → replace-label L a P ≃stm L P
replace-not-here L a (PExt P) = refl≃stm
replace-not-here L a (PShift P) = refl≃stm

replace-join-≃lm : (L : Label X S) → .⦃ is-join S ⦄ → (a : STm X) → replace-label L a ≃lm L
replace-join-≃lm L a .get Z = replace-not-here L a Z ⦃ maximal-join-not-here Z ⦄

connect-label-phere : (L : Label X S)
                    → (M : Label X T)
                    → connect-label L M PHere ≃stm L PHere
connect-label-phere {S = Sing} L M = refl≃stm
connect-label-phere {S = Join S₁ S₂} L M = refl≃stm

connect-label-inc-left : (L : Label X S)
                       → (M : Label X T)
                       → (A : STy X)
                       → (ap (connect-tree-inc-left S T) ●l (connect-label L M ,, A)) ≃l L
connect-label-inc-left {S = Sing} L M A .get PHere = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get PHere = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get (PExt Q) = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get (PShift Q) = connect-label-inc-left (L ∘ PShift) M A .get Q

connect-label-inc-right : (L : Label X S)
                        → (M : Label X T)
                        → (A : STy X)
                        → (Z : Path T) → .⦃ not-here Z ⦄ → .⦃ is-maximal Z ⦄ → (ap (connect-tree-inc-right S T) ●l (connect-label L M ,, A)) Z ≃stm M Z
connect-label-inc-right {S = Sing} L M A Z = replace-not-here M (L PHere) Z
connect-label-inc-right {S = Join S₁ S₂} L M A Z = connect-label-inc-right (L ∘ PShift) M A Z

replace-label-map : (f : STm X → STm Y) → (L : Label X S) → (a : STm X) → (f ∘ replace-label L a) ≃l replace-label (f ∘ L) (f a)
replace-label-map f L P .get PHere = refl≃stm
replace-label-map f L P .get (PExt Z) = refl≃stm
replace-label-map f L P .get (PShift Z) = refl≃stm

connect-label-map : (f : STm X → STm Y) → (L : Label X S) → (M : Label X T) → (f ∘ connect-label L M) ≃l connect-label (f ∘ L) (f ∘ M)
connect-label-map {S = Sing} f L M = replace-label-map f M (L PHere)
connect-label-map {S = Join S₁ S₂} f L M .get PHere = refl≃stm
connect-label-map {S = Join S₁ S₂} f L M .get (PExt Z) = refl≃stm
connect-label-map {S = Join S₁ S₂} f L M .get (PShift Z) = connect-label-map f (λ X → L (PShift X)) M .get Z

replace-label-≃ : ∀ {L : Label X S} {M : Label Y S} → L ≃l M → a ≃stm b → replace-label L a ≃l replace-label M b
replace-label-≃ p q .get PHere = q
replace-label-≃ p q .get (PExt Z) = p .get (PExt Z)
replace-label-≃ p q .get (PShift Z) = p .get (PShift Z)

connect-label-≃ : ∀ {L : Label X S} {M : Label X T} {L′ : Label Y S} {M′ : Label Y T}
                → L ≃l L′
                → M ≃l M′
                → connect-label L M ≃l connect-label L′ M′
connect-label-≃ {S = Sing} p q = replace-label-≃ q (p .get PHere)
connect-label-≃ {S = Join S₁ S₂} p q .get PHere = p .get PHere
connect-label-≃ {S = Join S₁ S₂} p q .get (PExt Z) = p .get (PExt Z)
connect-label-≃ {S = Join S₁ S₂} p q .get (PShift Z) = connect-label-≃ [ (λ P → p .get (PShift P)) ] q .get Z

replace-label-≃m : ∀ {L : Label X S} {M : Label Y S} → L ≃lm M → a ≃stm b → replace-label L a ≃lm replace-label M b
replace-label-≃m p q .get PHere = q
replace-label-≃m p q .get (PExt Z) = p .get (PExt Z)
replace-label-≃m p q .get (PShift Z) = p .get (PShift Z)

connect-label-≃m : ∀ {L : Label X S} {M : Label X T} {L′ : Label Y S} {M′ : Label Y T}
                → L ≃lm L′
                → M ≃lm M′
                → connect-label L M ≃lm connect-label L′ M′
connect-label-≃m {S = Sing} p q = replace-label-≃m q (p .get PHere)
connect-label-≃m {S = Join S₁ S₂} p q .get PHere = p .get PHere
connect-label-≃m {S = Join S₁ S₂} p q .get (PExt Z) = p .get (PExt Z)
connect-label-≃m {S = Join S₁ Sing} {L = L} {M} {L′} {M′} p q .get (PShift Z) = begin
  < replace-label M (L (PShift PHere)) Z >stm
    ≈⟨ replace-not-here M (L (PShift PHere)) Z ⟩
  < M Z >stm
    ≈⟨ q .get Z ⟩
  < M′ Z >stm
    ≈˘⟨ replace-not-here M′ (L′ (PShift PHere)) Z ⟩
  < replace-label M′ (L′ (PShift PHere)) Z >stm ∎
  where
    open Reasoning stm-setoid
connect-label-≃m {S = Join S₁ (Join S₂ S₃)} {L = L} {M} {L′} p q .get (PShift Z) = connect-label-≃m {L = L ∘ PShift} {L′ = L′ ∘ PShift} [ (λ Q → p .get (PShift Q) ⦃ build ⦃ maximal-join-not-here Q ⦄ ⦄) ] q .get Z

connect-label-sing : (L : Label X S) → (M M′ : Label X Sing) → connect-label L M ≃l connect-label L M′
connect-label-sing {S = Sing} L M M′ .get PHere = refl≃stm
connect-label-sing {S = Join S₁ S₂} L M M′ .get PHere = refl≃stm
connect-label-sing {S = Join S₁ S₂} L M M′ .get (PExt Z) = refl≃stm
connect-label-sing {S = Join S₁ S₂} L M M′ .get (PShift Z) = connect-label-sing (L ∘ PShift) M M′ .get Z

replace-label-prop : (L : Label X S) → (a : STm X) → a ≃stm L PHere → replace-label L a ≃l L
replace-label-prop L a p .get PHere = p
replace-label-prop L a p .get (PExt Q) = refl≃stm
replace-label-prop L a p .get (PShift Q) = refl≃stm

connect-label-prop : (S : Tree n) → (T : Tree m) → connect-label (ap (connect-tree-inc-left S T)) (ap (connect-tree-inc-right S T)) ≃l id-label (connect-tree S T)
connect-label-prop Sing T = replace-label-prop (id-label T) SHere refl≃stm
connect-label-prop (Join S₁ S₂) T .get PHere = refl≃stm
connect-label-prop (Join S₁ S₂) T .get (PExt Z) = refl≃stm
connect-label-prop (Join S₁ S₂) T .get (PShift Z) = begin
  < connect-label
       (λ x → SPath (PShift (connect-tree-inc-left′ S₂ T x)))
       (λ x → SPath (PShift (connect-tree-inc-right′ S₂ T x))) Z >stm
    ≈⟨ connect-label-≃ {L′ = SShift ∘ ap (connect-tree-inc-left S₂ T)} [ (λ P → [ refl≃tm ]) ] [ (λ P → [ refl≃tm ]) ] .get Z ⟩
  < connect-label (SShift ∘ ap (connect-tree-inc-left S₂ T))
                  (SShift ∘ ap (connect-tree-inc-right S₂ T)) Z >stm
    ≈˘⟨ connect-label-map SShift (ap (connect-tree-inc-left S₂ T)) (ap (connect-tree-inc-right S₂ T)) .get Z ⟩
  < SShift (connect-label (ap (connect-tree-inc-left S₂ T))
                          (ap (connect-tree-inc-right S₂ T)) Z) >stm
    ≈⟨ SShift≃ refl≃ (connect-label-prop S₂ T .get Z) ⟩
  < SShift {S = S₁} (SPath Z) >stm
    ≈⟨ [ refl≃tm ] ⟩
  < SPath (PShift Z) >stm ∎
  where
    open Reasoning stm-setoid

connect-tree-inc-left-assoc : (S : Tree n)
                            → (T : Tree m)
                            → (U : Tree l)
                            → (connect-tree-inc-left′ (connect-tree S T) U ∘ connect-tree-inc-left′ S T)
                            ≃lp connect-tree-inc-left′ S (connect-tree T U)
connect-tree-inc-left-assoc Sing T U .get Z = connect-tree-inc-left-phere T U
connect-tree-inc-left-assoc (Join S₁ S₂) T U .get PHere = Here≃ (≃′-to-≃ (sym≃′ (connect-tree-assoc (Join S₁ S₂) T U)))
connect-tree-inc-left-assoc (Join S₁ S₂) T U .get (PExt Z) = Ext≃ refl≃p (sym≃ (≃′-to-≃ (connect-tree-assoc S₂ T U)))
connect-tree-inc-left-assoc (Join S₁ S₂) T U .get (PShift Z) = Shift≃ refl≃ (connect-tree-inc-left-assoc S₂ T U .get Z)

connect-tree-inc-right-assoc : (S : Tree n)
                             → (T : Tree m)
                             → (U : Tree l)
                             → (connect-tree-inc-right′ S (connect-tree T U) ∘ connect-tree-inc-right′ T U)
                             ≃lp connect-tree-inc-right′ (connect-tree S T) U
connect-tree-inc-right-assoc Sing T U .get Z = refl≃p
connect-tree-inc-right-assoc (Join S₁ S₂) T U .get Z = Shift≃ refl≃ (connect-tree-inc-right-assoc S₂ T U .get Z)

connect-tree-inc-assoc : (S : Tree n)
                       → (T : Tree m)
                       → (U : Tree l)
                       → (connect-tree-inc-right′ S (connect-tree T U) ∘ connect-tree-inc-left′ T U)
                       ≃lp (connect-tree-inc-left′ (connect-tree S T) U ∘ connect-tree-inc-right′ S T)
connect-tree-inc-assoc Sing T U .get Z = refl≃p
connect-tree-inc-assoc (Join S₁ S₂) T U .get Z = Shift≃ refl≃ (connect-tree-inc-assoc S₂ T U .get Z)

replace-connect-label : (L : Label X S)
                      → (M : Label X T)
                      → (a : STm X)
                      → replace-label (connect-label L M) a ≃l connect-label (replace-label L a) M
replace-connect-label {S = Sing} L M a .get PHere = refl≃stm
replace-connect-label {S = Sing} L M a .get (PExt Z) = refl≃stm
replace-connect-label {S = Sing} L M a .get (PShift Z) = refl≃stm
replace-connect-label {S = Join S₁ S₂} L M a .get PHere = refl≃stm
replace-connect-label {S = Join S₁ S₂} L M a .get (PExt Z) = refl≃stm
replace-connect-label {S = Join S₁ S₂} L M a .get (PShift Z) = refl≃stm

connect-label-assoc : (L : Label X S)
                    → (M : Label X T)
                    → (N : Label X U)
                    → connect-label L (connect-label M N)
                    ≃l label-≃ (connect-tree-assoc S T U) (connect-label (connect-label L M) N)
connect-label-assoc {S = Sing} L M N = replace-connect-label M N (L PHere)
connect-label-assoc {S = Join S₁ S₂} L M N .get PHere = refl≃stm
connect-label-assoc {S = Join S₁ S₂} L M N .get (PExt Z) = refl≃stm
connect-label-assoc {S = Join S₁ S₂} L M N .get (PShift Z) = connect-label-assoc (L ∘ PShift) M N .get Z

stm-≃-≃stm : (p : S ≃′ T) → (a : STm (someTree S)) → a ≃stm stm-≃ p a
sty-≃-≃sty : (p : S ≃′ T) → (A : STy (someTree S)) → A ≃sty sty-≃ p A
≃-label-≃l : (p : S ≃′ T) → (L : Label (someTree S) U) → L ≃l ≃-label p L

stm-≃-≃stm Refl≃′ a = refl≃stm
stm-≃-≃stm (Join≃′ p q) (SExt a) = SExt≃ (stm-≃-≃stm p a) (≃′-to-≃ q)
stm-≃-≃stm (Join≃′ p q) (SShift a) = SShift≃ (≃′-to-≃ p) (stm-≃-≃stm q a)
stm-≃-≃stm (Join≃′ p q) (SPath P) = SPath≃ (ppath-≃-≃p (Join≃′ p q) P)
stm-≃-≃stm (Join≃′ p q) (SCoh S A L) = SCoh≃ S refl≃sty (≃-label-≃l (Join≃′ p q) (ap L)) (sty-≃-≃sty (Join≃′ p q) (lty L))

sty-≃-≃sty p S⋆ = S⋆-≃ (≃′-to-≃ p)
sty-≃-≃sty p (SArr s A t) = SArr≃ (stm-≃-≃stm p s) (sty-≃-≃sty p A) (stm-≃-≃stm p t)

≃-label-≃l p L .get Z = stm-≃-≃stm p (L Z)

stm-≃-≃ : (p : S ≃′ T) → a ≃stm b → stm-≃ p a ≃stm stm-≃ p b
stm-≃-≃ {a = a} {b = b} p q = begin
  < stm-≃ p a >stm
    ≈˘⟨ stm-≃-≃stm p a ⟩
  < a >stm
    ≈⟨ q ⟩
  < b >stm
    ≈⟨ stm-≃-≃stm p b ⟩
  < stm-≃ p b >stm ∎
  where
    open Reasoning stm-setoid

lift-stm-≃ : a ≃stm b → lift-stm a ≃stm lift-stm b
lift-stm-≃ {a = a} {b = b} [ p ] .get = begin
  < stm-to-term (lift-stm a) >tm
    ≈⟨ lift-stm-to-term a ⟩
  < lift-tm (stm-to-term a) >tm
    ≈⟨ lift-tm-≃ p ⟩
  < lift-tm (stm-to-term b) >tm
    ≈˘⟨ lift-stm-to-term b ⟩
  < stm-to-term (lift-stm b) >tm ∎
  where
    open Reasoning tm-setoid

susp-sty-dim : (As : STy X) → sty-dim (susp-sty As) ≡ suc (sty-dim As)
susp-sty-dim S⋆ = refl
susp-sty-dim (SArr s As t) = cong suc (susp-sty-dim As)

susp-unrestrict-label : (L : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → (susp-stm ∘ unrestrict-label L) ≃l unrestrict-label (susp-label L) ⦃ NonZero-subst (sym (susp-sty-dim (lty L))) it ⦄
susp-unrestrict-label (L ,, SArr s As t) .get PHere = refl≃stm
susp-unrestrict-label (L ,, SArr s As t) .get (PExt Z) = refl≃stm
susp-unrestrict-label (L ,, SArr s As t) .get (PShift Z) = refl≃stm

unrestrict-label-≃ : (L : Label-WT X S) → (M : Label-WT Y S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → ap L ≃l ap M → (q : lty L ≃sty lty M) → unrestrict-label L ≃l unrestrict-label M ⦃ NonZero-subst (sty-dim-≃ q) it ⦄
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get PHere = [ x ]
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get (PExt Z) = p .get Z
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get (PShift PHere) = [ y ]

unrestrict-label-prop : (M : Label-WT X (susp-tree S)) → ap M ≃l unrestrict-label (label₁ M)
unrestrict-label-prop M .get PHere = refl≃stm
unrestrict-label-prop M .get (PExt Z) = refl≃stm
unrestrict-label-prop M .get (PShift PHere) = refl≃stm

-- label-from-linear-tree-dim : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (As : STy X) → sty-dim (label-from-linear-tree-type S As) ≡ sty-dim As ∸ tree-dim S
-- label-from-linear-tree-dim Sing As = refl
-- label-from-linear-tree-dim (Join S Sing) As = begin
--   sty-dim
--       (label-from-linear-tree-type S (sty-base As))
--     ≡⟨ label-from-linear-tree-dim S (sty-base As) ⟩
--   sty-dim (sty-base As) ∸ tree-dim S
--     ≡⟨ cong (_∸ tree-dim S) (sty-base-dim As) ⟩
--   sty-dim As ∸ 1 ∸ tree-dim S
--     ≡⟨ ∸-+-assoc (sty-dim As) 1 (tree-dim S) ⟩
--   sty-dim As ∸ suc (tree-dim S) ∎
--   where
--     open ≡-Reasoning

-- label-from-linear-tree-≃ : (S : Tree n)
--                          → .⦃ _ : is-linear S ⦄
--                          → (a ≃stm b)
--                          → (q : As ≃sty Bs) → .(r : tree-dim S ≤ sty-dim As) → label-from-linear-tree S a As r ≃l label-from-linear-tree S b Bs (≤-trans r (≤-reflexive (sty-dim-≃ q)))
-- label-from-linear-tree-≃ Sing p q r .get P = p
-- label-from-linear-tree-≃ (Join S Sing) p q r = unrestrict-label-≃ (label-from-linear-tree S _ _ _ ,, truncate-sty′ (tree-dim S) _)
--                                                                    (label-from-linear-tree S _ _ _ ,, truncate-sty′ (tree-dim S) _)
--                                                                    ⦃ _ ⦄
--                                                                    (label-from-linear-tree-≃ S p q (≤-step′ r))
--                                                                    (truncate-sty′-≃ {d = tree-dim S} refl q)

extend-disc-label-max : (L : Label X S)
                      → .⦃ _ : is-linear S ⦄
                      → (t : STm X)
                      → (a : STm X)
                      → (Z : Path (susp-tree S))
                      → .⦃ is-maximal Z ⦄
                      → extend-disc-label L t a Z ≃stm a
extend-disc-label-max {S = Sing} L t a (PExt PHere) = refl≃stm
extend-disc-label-max {S = Sing} L t a (PShift PHere) = ⊥-elim it
extend-disc-label-max {S = Join S Sing} L t a (PExt Z) = extend-disc-label-max (L ∘ PExt) t a Z
extend-disc-label-max {S = Join S Sing} L t a (PShift PHere) = ⊥-elim it

extend-disc-label-disc-sty : (L : Label X S)
                            → .⦃ _ : is-linear S ⦄
                            → (t : STm X)
                            → (a : STm X)
                            → (As : STy X)
                            → disc-sty (susp-tree S) >>=′ (extend-disc-label L t a ,, As)
                              ≃sty SArr (L (is-linear-max-path S)) (disc-sty S >>=′ (L ,, As)) t
extend-disc-label-disc-sty {S = Sing} L t a As = refl≃sty
extend-disc-label-disc-sty {S = Join S Sing} L t a As = begin
  < disc-sty (susp-tree (susp-tree S)) >>=′ (extend-disc-label L t a ,, As) >sty
    ≈⟨ map-sty-ext-label (disc-sty (susp-tree S)) (extend-disc-label L t a ,, As) ⟩
  < disc-sty (susp-tree S) >>=′ (extend-disc-label (L ∘ PExt) t a ,, SArr (L PHere) As (L (PShift PHere))) >sty
    ≈⟨ extend-disc-label-disc-sty (L ∘ PExt) t a (SArr (L PHere) As (L (PShift PHere))) ⟩
  < SArr (L (PExt (is-linear-max-path S)))
         (disc-sty S >>=′ (L ∘ PExt ,, SArr (L PHere) As (L (PShift PHere))))
         t >sty
    ≈˘⟨ SArr≃ refl≃stm
              (map-sty-ext-label (disc-sty S) (L ,, As))
              refl≃stm ⟩
  < SArr (L (is-linear-max-path (susp-tree S)))
         (disc-sty (susp-tree S) >>=′ (L ,, As))
         t >sty ∎
  where
    open Reasoning sty-setoid

stm-to-label-max : (S : Tree n)
                  → .⦃ _ : is-linear S ⦄
                  → (a : STm X)
                  → (As : STy X)
                  → .⦃ _ : tree-dim S ≃n sty-dim As ⦄
                  → (Z : Path S)
                  → .⦃ is-maximal Z ⦄
                  → stm-to-label S a As Z ≃stm a
stm-to-label-max Sing a S⋆ Z = refl≃stm
stm-to-label-max (Join S Sing) a (SArr s As t) Z = extend-disc-label-max (stm-to-label S s As) t a Z

stm-to-label-disc-sty : (S : Tree n)
                        → .⦃ _ : is-linear S ⦄
                        → (a : STm X)
                        → (As : STy X)
                        → .⦃ _ : tree-dim S ≃n sty-dim As ⦄
                        → disc-sty S >>=′ (stm-to-label S a As ,, S⋆) ≃sty As
stm-to-label-disc-sty Sing a S⋆ = refl≃sty
stm-to-label-disc-sty (Join S Sing) a (SArr s As t) = begin
  < disc-sty (susp-tree S) >>=′ (extend-disc-label (stm-to-label S s As) t a ,, S⋆) >sty
    ≈⟨ extend-disc-label-disc-sty (stm-to-label S s As) t a S⋆ ⟩
  < SArr (stm-to-label S s As (is-linear-max-path S))
         (disc-sty S >>=′ (stm-to-label S s As ,, S⋆))
         t >sty
    ≈⟨ SArr≃ (stm-to-label-max S s As (is-linear-max-path S))
             (stm-to-label-disc-sty S s As)
             refl≃stm ⟩
  < SArr s As t >sty ∎
  where
    open Reasoning sty-setoid

stm-to-label-1-Full-src : (S : Tree n)
                         → .⦃ _ : is-linear S ⦄
                         → (a : STm (someTree T))
                         → (As : STy (someTree T))
                         → .⦃ _ : tree-dim S ≃n sty-dim As ⦄
                         → ⦃ 1-Full As ⦄
                         → stm-to-label S a As PHere ≃stm (SHere {S = T})
stm-to-label-1-Full-src (Join Sing Sing) a (SArr s S⋆ t) ⦃ _ ⦄ ⦃ full ⦄ = full .proj₁
stm-to-label-1-Full-src (Join (Join S Sing) Sing) a (SArr s (SArr s′ As t′) t) = begin
  < stm-to-label (Join (Join S Sing) Sing) a (SArr s (SArr s′ As t′) t) PHere >stm
    ≡⟨⟩
  < stm-to-label (Join S Sing) s (SArr s′ As t′) PHere >stm
    ≈⟨ stm-to-label-1-Full-src (Join S Sing) s (SArr s′ As t′) ⟩
  < SHere >stm ∎
  where
    open Reasoning stm-setoid

stm-to-label-1-Full-tgt : (S : Tree n)
                         → .⦃ _ : is-linear S ⦄
                         → (a : STm (someTree T))
                         → (As : STy (someTree T))
                         → .⦃ _ : tree-dim S ≃n sty-dim As ⦄
                         → ⦃ 1-Full As ⦄
                         → stm-to-label S a As (last-path S) ≃stm SPath (last-path T)
stm-to-label-1-Full-tgt (Join Sing Sing) a (SArr s S⋆ t) ⦃ _ ⦄ ⦃ full ⦄ = full .proj₂
stm-to-label-1-Full-tgt {T = T} (Join (Join S Sing) Sing) a (SArr s (SArr s′ As t′) t) = begin
  < stm-to-label (Join (Join S Sing) Sing) a (SArr s (SArr s′ As t′) t) (PShift PHere) >stm
    ≡⟨⟩
  < stm-to-label (Join S Sing) s (SArr s′ As t′) (PShift PHere) >stm
    ≈⟨ stm-to-label-1-Full-tgt (Join S Sing) s (SArr s′ As t′) ⟩
  < SPath (last-path T) >stm ∎
  where
    open Reasoning stm-setoid

extend-disc-label-to-sub : (L : Label X S)
                         → .⦃ _ : is-linear S ⦄
                         → (t : STm X)
                         → (a : STm X)
                         → (As : STy X)
                         → label-to-sub (extend-disc-label L t a ,, As) ≃s ⟨ ⟨ label-to-sub (L ,, As) , stm-to-term t ⟩ , stm-to-term a ⟩
extend-disc-label-to-sub {S = Sing} L t a As = refl≃s
extend-disc-label-to-sub {S = Join S Sing} L t a As = unrestrict-≃ (extend-disc-label-to-sub (L ∘ PExt) t a (SArr (L PHere) As (L (PShift PHere))))

stm-to-label-to-sub : (S : Tree n)
                     → .⦃ _ : is-linear S ⦄
                     → (a : STm (someTree T))
                     → (As : STy (someTree T))
                     → .⦃ _ : tree-dim S ≃n sty-dim As ⦄
                     → label-to-sub (stm-to-label S a As ,, S⋆) ≃s sub-from-disc (sty-dim As) (sty-to-type As) (sty-to-type-dim As) (stm-to-term a)
stm-to-label-to-sub Sing a S⋆ = refl≃s
stm-to-label-to-sub (Join S Sing) a (SArr s As t) = begin
  < label-to-sub (extend-disc-label (stm-to-label S s As) t a ,, S⋆) >s
    ≈⟨ extend-disc-label-to-sub (stm-to-label S s As) t a S⋆ ⟩
  < ⟨ ⟨ label-to-sub (stm-to-label S s As ,, S⋆) , stm-to-term t ⟩ , stm-to-term a ⟩ >s
    ≈⟨ Ext≃ (Ext≃ (stm-to-label-to-sub S s As) refl≃tm) refl≃tm ⟩
  < ⟨ ⟨ sub-from-disc (sty-dim As) (sty-to-type As) _ (stm-to-term s) , stm-to-term t ⟩ , stm-to-term a ⟩ >s ∎
  where
    open Reasoning sub-setoid

sty-to-coh-≃ : {As : STy (someTree S)} → {Bs : STy (someTree T)} → S ≃ T → As ≃sty Bs → sty-to-coh As ≃stm sty-to-coh Bs
sty-to-coh-≃ {S = S} {T = T} p [ q ] = [ (Coh≃ (tree-to-ctx-≃ p) q lem) ]
  where
    lem : label-to-sub (id-label-wt S) ● idSub ≃s label-to-sub (id-label-wt T) ● idSub
    lem = begin
      < label-to-sub (id-label-wt S) ● idSub >s
        ≈⟨ id-right-unit (label-to-sub (id-label-wt S)) ⟩
      < label-to-sub (id-label-wt S) >s
        ≈⟨ id-label-to-sub S ⟩
      < idSub >s
        ≈⟨ idSub-≃ (cong suc (≃-to-same-n p)) ⟩
      < idSub >s
        ≈˘⟨ id-label-to-sub T ⟩
      < label-to-sub (id-label-wt T) >s
        ≈˘⟨ id-right-unit (label-to-sub (id-label-wt T)) ⟩
      < label-to-sub (id-label-wt T) ● idSub >s ∎
      where
        open Reasoning sub-setoid

sty-to-coh-map-ext : (As : STy (someTree S)) → sty-to-coh (map-sty-ext {T = Sing} As) ≃stm SExt {T = Sing} (sty-to-coh As)
sty-to-coh-map-ext {S = S} As = begin
  < SCoh (susp S) (map-sty-ext As) (id-label-wt (susp S)) >stm
    ≈⟨ SCoh≃ (susp S) (map-sty-ext-susp-compat As) (sym≃l (id-label-susp-full S)) refl≃sty ⟩
  < SCoh (susp S) (susp-sty As) (susp-label-full (id-label S) ,, S⋆) >stm
    ≈˘⟨ SCoh-unrestrict S As (susp-label (id-label-wt S)) ⟩
  < SCoh S As (susp-label (id-label-wt S)) >stm
    ≈˘⟨ susp-stm-SCoh S As (id-label-wt S) ⟩
  < SExt (sty-to-coh As) >stm ∎
  where
    open Reasoning stm-setoid

replace-replace : (L : Label X S) → (a b : STm X) → replace-label (replace-label L a) b ≃l replace-label L b
replace-replace L a b .get PHere = refl≃stm
replace-replace L a b .get (PExt Z) = refl≃stm
replace-replace L a b .get (PShift Z) = refl≃stm

map-sty-ext-dim : (As : STy (someTree S)) → sty-dim (map-sty-ext {T = T} As) ≡ suc (sty-dim As)
map-sty-ext-dim S⋆ = refl
map-sty-ext-dim (SArr s As t) = cong suc (map-sty-ext-dim As)

disc-sty-dim : (T : Tree n) → .⦃ _ : is-linear T ⦄ → sty-dim (disc-sty T) ≡ tree-dim T
disc-sty-dim Sing = refl
disc-sty-dim (susp T) = trans (map-sty-ext-dim (disc-sty T)) (cong suc (disc-sty-dim T))

map-sty-ext-to-type : (As : STy (someTree S)) → sty-to-type (map-sty-ext {T = Sing} As) ≃ty susp-ty (sty-to-type As)
map-sty-ext-to-type S⋆ = refl≃ty
map-sty-ext-to-type (SArr s As t) = Arr≃ (id-on-tm (susp-tm (stm-to-term s))) (map-sty-ext-to-type As) (id-on-tm (susp-tm (stm-to-term t)))

disc-sty-to-type : (S : Tree n) → .⦃ _ : is-linear S ⦄ → sty-to-type (disc-sty S) ≃ty lift-ty (sphere-type (tree-dim S))
disc-sty-to-type Sing = refl≃ty
disc-sty-to-type (susp S) = begin
  < sty-to-type (map-sty-ext (disc-sty S)) >ty
    ≈⟨ map-sty-ext-to-type (disc-sty S) ⟩
  < susp-ty (sty-to-type (disc-sty S)) >ty
    ≈⟨ susp-ty-≃ (disc-sty-to-type S) ⟩
  < susp-ty (lift-ty (sphere-type (tree-dim S))) >ty
    ≈⟨ susp-ty-lift (sphere-type (tree-dim S)) ⟩
  < lift-ty (susp-ty (sphere-type (tree-dim S))) >ty
    ≈⟨ lift-ty-≃ (sphere-type-susp (tree-dim S)) ⟩
  < lift-ty (sphere-type (suc (tree-dim S))) >ty ∎
  where
    open Reasoning ty-setoid

identity-stm-to-term : (S : Tree n) → .⦃ _ : is-linear S ⦄ → stm-to-term (identity-stm S) ≃tm identity (tree-dim S) idSub
identity-stm-to-term S = begin
  < Coh (tree-to-ctx S)
        (path-to-term (is-linear-max-path S) ─⟨ sty-to-type (disc-sty S) ⟩⟶ path-to-term (is-linear-max-path S))
        (label-to-sub (id-label-wt S) ● idSub) >tm
    ≈⟨ Coh≃ refl≃c
            (Arr≃ (is-linear-max-path-is-0V S) refl≃ty (is-linear-max-path-is-0V S))
            (trans≃s (id-right-unit (label-to-sub (id-label-wt S))) (id-label-to-sub S)) ⟩
  < Coh (tree-to-ctx S)
        (0V ─⟨ sty-to-type (disc-sty S) ⟩⟶ 0V)
        idSub >tm
    ≈⟨ Coh≃ (linear-tree-compat S)
            (Arr≃ (Var≃ (≃c-preserve-length (linear-tree-compat S)) refl)
                  (disc-sty-to-type S)
                  (Var≃ (≃c-preserve-length (linear-tree-compat S)) refl))
            (idSub-≃ (≃c-preserve-length (linear-tree-compat S))) ⟩
  < identity (tree-dim S) idSub >tm ∎
  where
    open Reasoning tm-setoid

sty-dim-resuspend : (l : ℕ)
                  → (T : Tree n)
                  → .⦃ _ : has-trunk-height l T ⦄
                  → (As : STy (someTree (chop-trunk l T)))
                  → sty-dim (resuspend l As) ≡ l + sty-dim As
sty-dim-resuspend zero T As = refl
sty-dim-resuspend (suc l) (susp T) As = begin
  sty-dim (map-sty-ext (resuspend l As))
    ≡⟨ map-sty-ext-dim (resuspend l As) ⟩
  suc (sty-dim (resuspend l As))
    ≡⟨ cong suc (sty-dim-resuspend l T As) ⟩
  suc (l + sty-dim As)
    ≡⟨ refl ⟩
  suc l + sty-dim As ∎
  where
    open ≡-Reasoning

extend-disc-label-≃ : {L : Label X S}
                    → {M : Label Y S}
                    → L ≃l M
                    → .⦃ _ : is-linear S ⦄
                    → b ≃stm b′
                    → a ≃stm a′
                    → extend-disc-label L b a ≃l extend-disc-label M b′ a′
extend-disc-label-≃ {S = Sing} p q r .get PHere = p .get PHere
extend-disc-label-≃ {S = Sing} p q r .get (PExt PHere) = r
extend-disc-label-≃ {S = Sing} p q r .get (PShift PHere) = q
extend-disc-label-≃ {S = susp S} p q r .get PHere = p .get PHere
extend-disc-label-≃ {S = susp S} p q r .get (PExt Z)
  = extend-disc-label-≃ [ (λ P → p .get (PExt P)) ] q r .get Z
extend-disc-label-≃ {S = susp S} p q r .get (PShift PHere) = p .get (PShift PHere)

stm-to-label-≃ : {X : MaybeTree m}
               → {Y : MaybeTree m′}
               → (S : Tree n)
               → .⦃ _ : is-linear S ⦄
               → {a : STm X}
               → {b : STm Y}
               → a ≃stm b
               → {As : STy X}
               → {Bs : STy Y}
               → (q : As ≃sty Bs)
               → .⦃ _ : tree-dim S ≃n sty-dim As ⦄
               → stm-to-label S a As ≃l stm-to-label S b Bs ⦃ trans≃n it (≡-to-≃n (sty-dim-≃ q)) ⦄
stm-to-label-≃ Sing p q .get Z = p
stm-to-label-≃ (susp S) p {SArr _ _ _} {SArr _ _ _} q
  = extend-disc-label-≃ (stm-to-label-≃ S (SArr≃-proj₁ q) (SArr≃-proj₂ q)) (SArr≃-proj₃ q) p

extend-disc-label-susp : (L : Label X S)
                       → .⦃ _ : is-linear S ⦄
                       → (t : STm X)
                       → (a : STm X)
                       → extend-disc-label (susp-stm ∘ L) (susp-stm t) (susp-stm a)
                         ≃l
                         (susp-stm ∘ extend-disc-label L t a)
extend-disc-label-susp {S = Sing} L t a .get PHere = refl≃stm
extend-disc-label-susp {S = Sing} L t a .get (PExt PHere) = refl≃stm
extend-disc-label-susp {S = Sing} L t a .get (PShift PHere) = refl≃stm
extend-disc-label-susp {S = susp S} L t a .get PHere = refl≃stm
extend-disc-label-susp {S = susp S} L t a .get (PExt Z)
  = extend-disc-label-susp (L ∘ PExt) t a .get Z
extend-disc-label-susp {S = susp S} L t a .get (PShift PHere) = refl≃stm

extend-disc-label-susp-full : (L : Label X S)
                            → .⦃ _ : is-linear S ⦄
                            → (t : STm X)
                            → (a : STm X)
                            → extend-disc-label (susp-label-full L) (susp-stm t) (susp-stm a)
                              ≃l
                              susp-label-full (extend-disc-label L t a)
extend-disc-label-susp-full L t a .get PHere = refl≃stm
extend-disc-label-susp-full L t a .get (PExt Z)
  = extend-disc-label-susp L t a .get Z
extend-disc-label-susp-full L t a .get (PShift PHere) = refl≃stm

stm-to-label-susp : (S : Tree n)
                  → ⦃ _ : is-linear S ⦄
                  → (a : STm X)
                  → (As : STy X)
                  → .⦃ _ : tree-dim S ≃n sty-dim As ⦄
                  → stm-to-label (susp S) (susp-stm a) (susp-sty As)
                    ⦃ trans≃n inst (≡-to-≃n (sym (susp-sty-dim As))) ⦄
                    ≃l
                    susp-label-full (stm-to-label S a As)
stm-to-label-susp Sing a S⋆ .get PHere = refl≃stm
stm-to-label-susp Sing a S⋆ .get (PExt PHere) = refl≃stm
stm-to-label-susp Sing a S⋆ .get (PShift PHere) = refl≃stm
stm-to-label-susp (susp S) a (SArr s As t) = begin
  < extend-disc-label
      (stm-to-label (susp S) (susp-stm s) (susp-sty As) ⦃ _ ⦄)
      (susp-stm t)
      (susp-stm a) >l
    ≈⟨ extend-disc-label-≃ (stm-to-label-susp S s As) refl≃stm refl≃stm ⟩
  < extend-disc-label (susp-label-full (stm-to-label S s As))
                      (susp-stm t)
                      (susp-stm a) >l
    ≈⟨ extend-disc-label-susp-full (stm-to-label S s As) t a ⟩
  < susp-label-full (extend-disc-label (stm-to-label S s As) t a) >l ∎
  where
    open Reasoning (label-setoid (susp (susp S)))
