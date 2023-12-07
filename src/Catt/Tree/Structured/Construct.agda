module Catt.Tree.Structured.Construct where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular

lift-stm : STm (Other n) → STm (Other (suc n))
lift-sty : STy (Other n) → STy (Other (suc n))
lift-label : Label-WT (Other n) S → Label-WT (Other (suc n)) S

lift-stm (SCoh S A L) = SCoh S A (lift-label L)
lift-stm (SOther t) = SOther (lift-tm t)

lift-sty S⋆ = S⋆
lift-sty (SArr s A t) = SArr (lift-stm s) (lift-sty A) (lift-stm t)

lift-label L = lift-stm ∘ (ap L) ,, lift-sty (lty L)

stm-fst : STm (suspMaybeTree X)
stm-snd : STm (suspMaybeTree X)

stm-fst {X = someTree x} = SHere
stm-fst {X = Other _} = SOther get-fst

stm-snd {X = someTree x} = SShift (SPath PHere)
stm-snd {X = Other _} = SOther get-snd

unrestrict-label : (L : Label-WT X S) → .⦃ NonZero (sty-dim (lty L)) ⦄ → Label X (susp-tree S)
unrestrict-label {X = X} {S = S} (L ,, As) PHere = sty-src As
unrestrict-label {X = X} {S = S} (L ,, As) (PExt P) = L P
unrestrict-label {X = X} {S = S} (L ,, As) (PShift P) = sty-tgt As

susp-stm : STm X → STm (suspMaybeTree X)
susp-sty : STy X → STy (suspMaybeTree X)
susp-label : Label-WT X S → Label-WT (suspMaybeTree X) S
susp-label-full : Label X S → Label (suspMaybeTree X) (susp-tree S)

susp-stm {X = someTree x} s = SExt s
susp-stm {X = Other _} (SCoh S A L) = SCoh S A (susp-label L)
susp-stm {X = Other _} (SOther t) = SOther (susp-tm t)

susp-sty S⋆ = SArr stm-fst S⋆ stm-snd
susp-sty (SArr s A t) = SArr (susp-stm s) (susp-sty A) (susp-stm t)

susp-label L = susp-stm ∘ (ap L) ,, susp-sty (lty L)

susp-label-full L = unrestrict-label (susp-label (L ,, S⋆))

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

replace-label : Label X S → STm X → Label X S
replace-label L P PHere = P
replace-label L P (PExt Z) = L (PExt Z)
replace-label L P (PShift Z) = L (PShift Z)

connect-label : Label X S
              → Label X T
              → Label X (connect-tree S T)
connect-label {S = Sing} L M = replace-label M (L PHere)
connect-label {S = Join S₁ S₂} L M PHere = L PHere
connect-label {S = Join S₁ S₂} L M (PExt Z) = L (PExt Z)
connect-label {S = Join S₁ S₂} L M (PShift Z) = connect-label (λ x → L (PShift x)) M Z

connect-label′ : Label X S
               → Label X T
               → Label X (connect-tree S T)
connect-label′ {S = Sing} L M = M
connect-label′ {S = Join S₁ S₂} L M PHere = L PHere
connect-label′ {S = Join S₁ S₂} L M (PExt Z) = L (PExt Z)
connect-label′ {S = Join S₁ S₂} L M (PShift Z) = connect-label′ (L ∘ PShift) M Z

connect-tree-inc-left′ : (S : Tree n) → (T : Tree m) → Label′ (connect-tree S T) S
connect-tree-inc-left′ Sing T P = PHere
connect-tree-inc-left′ (Join S₁ S₂) T PHere = PHere
connect-tree-inc-left′ (Join S₁ S₂) T (PExt P) = PExt P
connect-tree-inc-left′ (Join S₁ S₂) T (PShift P) = PShift (connect-tree-inc-left′ S₂ T P)

connect-tree-inc-right′ : (S : Tree n) → (T : Tree m) → Label′ (connect-tree S T) T
connect-tree-inc-right′ Sing T P = P
connect-tree-inc-right′ (Join S₁ S₂) T P = PShift (connect-tree-inc-right′ S₂ T P)

connect-tree-inc-left : (S : Tree n) → (T : Tree m) → Label-WT (someTree (connect-tree S T)) S
connect-tree-inc-left S T = SPath ∘ connect-tree-inc-left′ S T ,, S⋆

connect-tree-inc-right : (S : Tree n) → (T : Tree m) → Label-WT (someTree (connect-tree S T)) T
connect-tree-inc-right S T = SPath ∘ connect-tree-inc-right′ S T ,, S⋆

label-between-connect-trees : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → Label (someTree (connect-tree S′ T′)) (connect-tree S T)
label-between-connect-trees {S′ = S′} {T′ = T′} L M = connect-label (L ●l (connect-tree-inc-left S′ T′)) (M ●l (connect-tree-inc-right S′ T′))

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

disc-type : (n : ℕ) → STy (someTree (n-disc n))
disc-type zero = S⋆
disc-type (suc n) = map-sty-ext (disc-type n)

extend-disc-label : Label X (n-disc n) → (t : STm X) → (a : STm X) → Label X (n-disc (1 + n))
extend-disc-label {n = zero} L t a PHere = L PHere
extend-disc-label {n = zero} L t a (PExt P) = a
extend-disc-label {n = zero} L t a (PShift PHere) = t
extend-disc-label {n = suc n} L t a PHere = L PHere
extend-disc-label {n = suc n} L t a (PExt P) = extend-disc-label (L ∘ PExt) t a P
extend-disc-label {n = suc n} L t a (PShift PHere) = L (PShift PHere)

term-to-label : (a : STm X) → (As : STy X) → Label X (n-disc (sty-dim As))
term-to-label a S⋆ x = a
term-to-label a (SArr s As t) = extend-disc-label (term-to-label s As) t a

cast-to-disc : (S : Tree n) → .⦃ is-linear S ⦄ → .⦃ tree-dim S ≃n m ⦄ → Label′ (n-disc m) S
cast-to-disc Sing PHere = PHere
cast-to-disc (Join S Sing) PHere = PHere
cast-to-disc {m = suc m} (Join S Sing) (PExt P) = PExt (cast-to-disc S P)
cast-to-disc (Join S Sing) (PShift PHere) = last-path (n-disc _)

-- label-from-linear-tree : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (a : STm X) → (As : STy X) → .(tree-dim S ≤ sty-dim As) → Label X S
-- label-from-linear-tree-nz : (n : ℕ) → (As : STy X) → .(suc n ≤ sty-dim As) → NonZero (sty-dim (truncate-sty′ n As))

-- label-from-linear-tree Sing a As p P = a
-- label-from-linear-tree (Join S Sing) a As p = unrestrict-label (label-from-linear-tree S a As (≤-step′ p) ,, truncate-sty′ (tree-dim S) As) ⦃ label-from-linear-tree-nz (tree-dim S) As p ⦄

-- sty-base-dim-prop : (As : STy X) → sty-dim As ≤ suc (sty-dim (sty-base As))
-- sty-base-dim-prop S⋆ = z≤n
-- sty-base-dim-prop (SArr s As t) = ≤-refl

-- label-from-linear-tree-nz zero As p = NonZero-≤ p it
-- label-from-linear-tree-nz (suc n) As p = label-from-linear-tree-nz n (sty-base As) (≤-pred (≤-trans p (sty-base-dim-prop As)))
