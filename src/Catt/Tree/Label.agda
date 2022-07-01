module Catt.Tree.Label where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree.Path

data MaybeTree : ℕ → Set where
  someTree : Tree n → MaybeTree (suc n)
  Other : (n : ℕ) → MaybeTree n

variable
  X Y Z : MaybeTree n

maybeTreeSize : (X : MaybeTree n) → ℕ
maybeTreeSize {n} X = n

suspMaybeTree : MaybeTree n → MaybeTree (2 + n)
suspMaybeTree (someTree x) = someTree (suspTree x)
suspMaybeTree (Other _) = Other (2 + _)

data CtxOrTree : ℕ → Set where
  incTree : Tree n → CtxOrTree (suc n)
  incCtx : Ctx n → CtxOrTree n

variable
  ΓS ΔT : CtxOrTree n

COT-to-MT : CtxOrTree n → MaybeTree n
COT-to-MT (incTree x) = someTree x
COT-to-MT (incCtx x) = Other _

COT-to-Ctx : CtxOrTree n → Ctx n
COT-to-Ctx (incTree x) = tree-to-ctx x
COT-to-Ctx (incCtx x) = x

Label′ : (T : Tree m) → (S : Tree n) → Set
Label′ T S = Path S → Path T

Label : (X : MaybeTree m) → (S : Tree n) → Set
Label-WT : (X : MaybeTree m) → (S : Tree n) → Set
Label-WT {m = m} X S = Label X S × Ty m

data STm : MaybeTree n → Set where
  SExt : STm (someTree S) → STm (someTree (Join S T))
  SShift : STm (someTree T) → STm (someTree (Join S T))
  SPath : Path T → STm (someTree T)
  SCoh : (S : Tree m) → (A : Ty (suc m)) → (L : Label-WT X S) → STm X
  SOther : (t : Tm n) → STm (Other n)

SHere : STm (someTree S)
SHere = SPath PHere

Label X S = Path S → STm X

stm-to-term : {X : MaybeTree n} → STm X → Tm n
label-to-sub : {X : MaybeTree n} → (L : Label-WT X S) → Sub (suc (tree-size S)) n (proj₂ L)

compute-stm : STm (someTree S) → STm (someTree S)
compute-stm (SExt a) = SExt a
compute-stm (SShift a) = SShift a
compute-stm (SPath PHere) = SPath PHere
compute-stm (SPath (PExt x)) = SExt (SPath x)
compute-stm (SPath (PShift x)) = SShift (SPath x)
compute-stm (SCoh S A L) = SCoh S A L

ap : Label-WT X S → Path S → STm X
ap = proj₁
{-# INLINE ap #-}

apt : {X : MaybeTree m} → Label-WT X S → Path S → Tm m
apt L P = stm-to-term (ap L P)

lty : {X : MaybeTree m} → Label-WT X S → Ty m
lty = proj₂

variable
  L L′ M M′ : Label-WT X S
  a b c : STm X

label₁ : (L : Label-WT X (Join S T)) → Label-WT X S
label₁ L = ap L ∘ PExt ,, apt L PHere ─⟨ lty L ⟩⟶ apt L (PShift PHere)

label₂ : (L : Label-WT X (Join S T)) → Label-WT X T
label₂ L = proj₁ L ∘ PShift ,, proj₂ L

stm-to-term (SExt s) = suspTm (stm-to-term s) [ connect-susp-inc-left _ _ ]tm
stm-to-term (SShift s) = stm-to-term s [ connect-susp-inc-right _ _ ]tm
stm-to-term (SPath P) = path-to-term P
stm-to-term (SCoh S A L) = Coh (tree-to-ctx S) A idSub [ label-to-sub L ]tm
stm-to-term (SOther t) = t

label-to-sub′ : ((P : Path S) → Tm n) → (A : Ty n) → Sub (suc (tree-size S)) n A
label-to-sub′ {S = Sing} f A = ⟨ ⟨⟩ , f PHere ⟩
label-to-sub′ {S = Join S₁ S₂} f A = sub-from-connect (unrestrict (label-to-sub′ (λ P → f (PExt P)) (f PHere ─⟨ A ⟩⟶ f (PShift PHere)))) (label-to-sub′ (λ P → f (PShift P)) A)

label-to-sub (L ,, A) = label-to-sub′ (λ P → stm-to-term (L P)) A

map-pext : Label-WT (someTree S) U → Label-WT (someTree (Join S T)) U
map-pext L = SExt ∘ ap L ,, (suspTy (lty L) [ connect-susp-inc-left _ _ ]ty)

map-pshift : Label-WT (someTree T) U → Label-WT (someTree (Join S T)) U
map-pshift L = SShift ∘ ap L ,,  (lty L [ connect-susp-inc-right _ _ ]ty)

lift-stm : STm (Other n) → STm (Other (suc n))
lift-label : Label-WT (Other n) S → Label-WT (Other (suc n)) S

lift-stm (SCoh S A L) = SCoh S A (lift-label L)
lift-stm (SOther t) = SOther (liftTerm t)

lift-label (L ,, A) = lift-stm ∘ L ,, liftType A

susp-stm : STm X → STm (suspMaybeTree X)
susp-label : Label-WT X S → Label-WT (suspMaybeTree X) S

susp-stm {X = someTree x} s = SExt s
susp-stm {X = Other _} (SCoh S A L) = SCoh S A (susp-label L)
susp-stm {X = Other _} (SOther t) = SOther (suspTm t)

susp-label (L ,, A) = susp-stm ∘ L ,, suspTy A

label-sub : {X : MaybeTree n} → Label-WT X S → (σ : Sub n m B) → Label-WT (Other m) S
label-sub L σ = SOther ∘ _[ σ ]tm ∘ stm-to-term ∘ ap L ,, lty L [ σ ]ty

id-label : (S : Tree n) → Label (someTree S) S
id-label S = SPath

id-label-wt : (S : Tree n) → Label-WT (someTree S) S
id-label-wt S = id-label S ,, ⋆

to-label : (S : Tree n) → (σ : Sub (suc n) m A) → Label (Other m) S
to-label S σ Z = SOther (path-to-term Z [ σ ]tm)

infixl 1 _>>=_
_>>=_ : STm (someTree S) → Label-WT X S → STm X
label-comp : Label (someTree T) S → Label-WT X T → Label X S

label-wt-comp : Label-WT (someTree T) S → Label-WT X T → Label-WT X S
label-wt-comp L M = label-comp (ap L) M ,, lty L [ label-to-sub M ]ty

SExt s >>= L = s >>= label₁ L
SShift s >>= L = s >>= label₂ L
SPath P >>= L = ap L P
SCoh S A M >>= L = SCoh S A (label-wt-comp M L)

label-comp L M P = L P >>= M

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

connect-tree-inc-left′ : (S : Tree n) → (T : Tree m) → Label′ (connect-tree S T) S
connect-tree-inc-left′ Sing T P = PHere
connect-tree-inc-left′ (Join S₁ S₂) T PHere = PHere
connect-tree-inc-left′ (Join S₁ S₂) T (PExt P) = PExt P
connect-tree-inc-left′ (Join S₁ S₂) T (PShift P) = PShift (connect-tree-inc-left′ S₂ T P)

connect-tree-inc-right′ : (S : Tree n) → (T : Tree m) → Label′ (connect-tree S T) T
connect-tree-inc-right′ Sing T P = P
connect-tree-inc-right′ (Join S₁ S₂) T P = PShift (connect-tree-inc-right′ S₂ T P)

connect-tree-inc-left : (S : Tree n) → (T : Tree m) → Label-WT (someTree (connect-tree S T)) S
connect-tree-inc-left S T = SPath ∘ connect-tree-inc-left′ S T ,, ⋆

connect-tree-inc-right : (S : Tree n) → (T : Tree m) → Label-WT (someTree (connect-tree S T)) T
connect-tree-inc-right S T = SPath ∘ connect-tree-inc-right′ S T ,, ⋆

label-between-connect-trees : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → Label (someTree (connect-tree S′ T′)) (connect-tree S T)
label-between-connect-trees {S′ = S′} {T′ = T′} L M = connect-label (label-comp L (connect-tree-inc-left S′ T′)) (label-comp M (connect-tree-inc-right S′ T′))

label-between-joins : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → Label (someTree (Join S′ T′)) (Join S T)
label-between-joins L M PHere = SHere
label-between-joins L M (PExt P) = SExt (L P)
label-between-joins L M (PShift P) = SShift (M P)
