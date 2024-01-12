module Catt.Tree.Structured.Construct where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Globular
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.ToTerm

lift-stm : STm (Other n) → STm (Other (suc n))
lift-sty : STy (Other n) → STy (Other (suc n))
lift-label : Label-WT (Other n) S → Label-WT (Other (suc n)) S

lift-stm (SCoh S A L) = SCoh S A (lift-label L)
lift-stm (SOther t) = SOther (lift-tm t)

lift-sty S⋆ = S⋆
lift-sty (SArr s A t) = SArr (lift-stm s) (lift-sty A) (lift-stm t)

lift-label L = lift-stm ∘ (ap L) ,, lift-sty (lty L)

stm-fst : STm (susp-maybe-tree X)
stm-snd : STm (susp-maybe-tree X)

stm-fst {X = someTree x} = SHere
stm-fst {X = Other _} = SOther get-fst

stm-snd {X = someTree x} = SShift (SPath PHere)
stm-snd {X = Other _} = SOther get-snd

unrestrict-label : (L : Label-WT X S) → .⦃ NonZero (sty-dim (lty L)) ⦄ → Label X (Susp S)
unrestrict-label {X = X} {S = S} (L ,, As) PHere = sty-src As
unrestrict-label {X = X} {S = S} (L ,, As) (PExt P) = L P
unrestrict-label {X = X} {S = S} (L ,, As) (PShift P) = sty-tgt As

susp-stm : STm X → STm (susp-maybe-tree X)
susp-sty : STy X → STy (susp-maybe-tree X)
susp-label : Label-WT X S → Label-WT (susp-maybe-tree X) S
susp-label-full : Label X S → Label (susp-maybe-tree X) (Susp S)

susp-stm {X = someTree x} s = SExt s
susp-stm {X = Other _} (SCoh S A L) = SCoh S A (susp-label L)
susp-stm {X = Other _} (SOther t) = SOther (susp-tm t)

susp-sty S⋆ = SArr stm-fst S⋆ stm-snd
susp-sty (SArr s A t) = SArr (susp-stm s) (susp-sty A) (susp-stm t)

susp-label L = susp-stm ∘ (ap L) ,, susp-sty (lty L)

susp-label-full L = unrestrict-label (susp-label (L ,, S⋆))

susp-sty-n : (n : ℕ) → STy X → STy (susp-maybe-tree-n n X)
susp-sty-n zero As = As
susp-sty-n (suc n) As = susp-sty (susp-sty-n n As)

map-sty-ext : STy (someTree S) → STy (someTree (Join S T))
map-sty-ext S⋆ = SArr SHere S⋆ (SShift (SPath PHere))
map-sty-ext (SArr s A t) = SArr (SExt s) (map-sty-ext A) (SExt t)

map-ext : Label-WT (someTree S) U → Label-WT (someTree (Join S T)) U
map-ext L = SExt ∘ ap L ,, (map-sty-ext (lty L))

map-sty-shift : STy (someTree T) → STy (someTree (Join S T))
map-sty-shift S⋆ = S⋆
map-sty-shift (SArr s A t) = SArr (SShift s) (map-sty-shift A) (SShift t)

map-shift : Label-WT (someTree T) U → Label-WT (someTree (Join S T)) U
map-shift L = SShift ∘ ap L ,, map-sty-shift (lty L)

resuspend-stm : {S : Tree n} → (d : ℕ) → .⦃ _ : has-trunk-height d S ⦄ → STm (someTree (chop-trunk d S)) → STm (someTree S)
resuspend-stm zero s = s
resuspend-stm {S = Susp S} (suc d) s = SExt (resuspend-stm d s)

resuspend : {S : Tree n} → (d : ℕ) → .⦃ _ : has-trunk-height d S ⦄ → STy (someTree (chop-trunk d S)) → STy (someTree S)
resuspend zero As = As
resuspend {S = Susp S} (suc d) As = map-sty-ext (resuspend d As)

replace-label : Label X S → STm X → Label X S
replace-label L P PHere = P
replace-label L P (PExt Z) = L (PExt Z)
replace-label L P (PShift Z) = L (PShift Z)

infixr 6 _++l_ _++l′_
_++l_ : Label X S
      → Label X T
      → Label X (S ++t T)
_++l_ {S = Sing} L M = replace-label M (L PHere)
_++l_ {S = Join S₁ S₂} L M PHere = L PHere
_++l_ {S = Join S₁ S₂} L M (PExt Z) = L (PExt Z)
_++l_ {S = Join S₁ S₂} L M (PShift Z) = (L ∘ PShift ++l M) Z

_++l′_ : Label X S
       → Label X T
       → Label X (S ++t T)
_++l′_ {S = Sing} L M = M
_++l′_ {S = Join S₁ S₂} L M PHere = L PHere
_++l′_ {S = Join S₁ S₂} L M (PExt Z) = L (PExt Z)
_++l′_ {S = Join S₁ S₂} L M (PShift Z) = (L ∘ PShift ++l′ M) Z

++t-inc-left′ : (S : Tree n) → (T : Tree m) → Label′ (S ++t T) S
++t-inc-left′ Sing T P = PHere
++t-inc-left′ (Join S₁ S₂) T PHere = PHere
++t-inc-left′ (Join S₁ S₂) T (PExt P) = PExt P
++t-inc-left′ (Join S₁ S₂) T (PShift P) = PShift (++t-inc-left′ S₂ T P)

++t-inc-right′ : (S : Tree n) → (T : Tree m) → Label′ (S ++t T) T
++t-inc-right′ Sing T P = P
++t-inc-right′ (Join S₁ S₂) T P = PShift (++t-inc-right′ S₂ T P)

++t-inc-left : (S : Tree n) → (T : Tree m) → Label-WT (someTree (S ++t T)) S
++t-inc-left S T = SPath ∘ ++t-inc-left′ S T ,, S⋆

++t-inc-right : (S : Tree n) → (T : Tree m) → Label-WT (someTree (S ++t T)) T
++t-inc-right S T = SPath ∘ ++t-inc-right′ S T ,, S⋆

label-between-++t : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → Label (someTree (S′ ++t T′)) (S ++t T)
label-between-++t {S′ = S′} {T′ = T′} L M = L ●l (++t-inc-left S′ T′) ++l′ M ●l (++t-inc-right S′ T′)

label-between-joins : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → Label (someTree (Join S′ T′)) (Join S T)
label-between-joins L M PHere = SHere
label-between-joins L M (PExt P) = SExt (L P)
label-between-joins L M (PShift P) = SShift (M P)

stm-≃ : (S ≃′ T) → STm (someTree S) → STm (someTree T)
sty-≃ : (S ≃′ T) → STy (someTree S) → STy (someTree T)
≃-label : (S ≃′ T) → Label (someTree S) U → Label (someTree T) U
≃-label-wt : (S ≃′ T) → Label-WT (someTree S) U → Label-WT (someTree T) U

stm-≃ Refl≃′ a = a
stm-≃ (Join≃′ p q) (SExt a) = SExt (stm-≃ p a)
stm-≃ (Join≃′ p q) (SShift a) = SShift (stm-≃ q a)
stm-≃ (Join≃′ p q) (SPath x) = SPath (ppath-≃ (Join≃′ p q) x)
stm-≃ (Join≃′ p q) (SCoh S A L) = SCoh S A (≃-label-wt (Join≃′ p q) L)

sty-≃ p S⋆ = S⋆
sty-≃ p (SArr s A t) = SArr (stm-≃ p s) (sty-≃ p A) (stm-≃ p t)

≃-label p L = stm-≃ p ∘ L

≃-label-wt p L = (≃-label p (ap L)) ,, (sty-≃ p (lty L))

disc-sty : (S : Tree n) → .⦃ is-linear S ⦄ → STy (someTree S)
disc-sty Sing = S⋆
disc-sty (Susp S) = map-sty-ext (disc-sty S)

sty-to-coh : (As : STy (someTree T)) → STm (someTree T)
sty-to-coh {T = T} As = SCoh T As (id-label-wt T)

disc-stm : (S : Tree n) → .⦃ is-linear S ⦄ → STm (someTree S)
disc-stm S = sty-to-coh (disc-sty S)

identity-stm : (S : Tree n) → .⦃ is-linear S ⦄ → STm (someTree S)
identity-stm S = SCoh S (SArr (SPath (is-linear-max-path S)) (disc-sty S) (SPath (is-linear-max-path S))) (id-label-wt S)

extend-disc-label : Label X S
                  → .⦃ is-linear S ⦄
                  → (t : STm X)
                  → (a : STm X)
                  → Label X (Susp S)
extend-disc-label {S = Sing} L t a PHere = L PHere
extend-disc-label {S = Sing} L t a (PExt PHere) = a
extend-disc-label {S = Sing} L t a (PShift PHere) = t
extend-disc-label {S = Susp S} L t a PHere = L PHere
extend-disc-label {S = Susp S} L t a (PExt P) = extend-disc-label (L ∘ PExt) t a P
extend-disc-label {S = Susp S} L t a (PShift PHere) = L (PShift PHere)

stm-to-label : (S : Tree n)
             → .⦃ is-linear S ⦄
             → (a : STm X)
             → (As : STy X)
             → .⦃ has-dim (tree-dim S) As ⦄
             → Label X S
stm-to-label Sing a As P = a
stm-to-label (Susp S) a (SArr s As t) = extend-disc-label (stm-to-label S s As) t a

getPathType : (P : Path S) → STy (someTree S)
getPathType PHere = S⋆
getPathType (PExt P) = map-sty-ext (getPathType P)
getPathType (PShift P) = map-sty-shift (getPathType P)
