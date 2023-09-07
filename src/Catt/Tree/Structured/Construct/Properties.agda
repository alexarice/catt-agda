module Catt.Tree.Structured.Construct.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Tree           --
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
                        → (Z : Path T) → .⦃ not-here Z ⦄ → .⦃ is-Maximal Z ⦄ → (ap (connect-tree-inc-right S T) ●l (connect-label L M ,, A)) Z ≃stm M Z
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

unrestrict-label-≃ : (L M : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → ap L ≃l ap M → (q : lty L ≃sty lty M) → unrestrict-label L ≃l unrestrict-label M ⦃ NonZero-subst (sty-dim-≃ q) it ⦄
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get PHere = [ x ]
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get (PExt Z) = p .get Z
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get (PShift PHere) = [ y ]

label-from-linear-tree-dim : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (As : STy X) → sty-dim (label-from-linear-tree-type S As) ≡ sty-dim As ∸ tree-dim S
label-from-linear-tree-dim Sing As = refl
label-from-linear-tree-dim (Join S Sing) As = begin
  sty-dim
      (label-from-linear-tree-type S (sty-base As))
    ≡⟨ label-from-linear-tree-dim S (sty-base As) ⟩
  sty-dim (sty-base As) ∸ tree-dim S
    ≡⟨ cong (_∸ tree-dim S) (sty-base-dim As) ⟩
  sty-dim As ∸ 1 ∸ tree-dim S
    ≡⟨ ∸-+-assoc (sty-dim As) 1 (tree-dim S) ⟩
  sty-dim As ∸ suc (tree-dim S) ∎
  where
    open ≡-Reasoning
