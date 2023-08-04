module Catt.Tree.Structured where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Path

data MaybeTree : ℕ → Set where
  someTree : Tree n → MaybeTree (suc n)
  Other : (n : ℕ) → MaybeTree n

variable
  X Y Z : MaybeTree n

maybeTreeSize : (X : MaybeTree n) → ℕ
maybeTreeSize {n} X = n

suspMaybeTree : MaybeTree n → MaybeTree (2 + n)
suspMaybeTree (someTree x) = someTree (susp-tree x)
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
data STm : MaybeTree n → Set
data STy : MaybeTree n → Set

data STm where
  SExt : STm (someTree S) → STm (someTree (Join S T))
  SShift : STm (someTree T) → STm (someTree (Join S T))
  SPath : Path T → STm (someTree T)
  SCoh : (S : Tree m) → (A : STy (someTree S)) → (L : Label-WT X S) → STm X
  SOther : (t : Tm n) → STm (Other n)

data STy where
  S⋆ : STy X
  SArr : (s : STm X) → (A : STy X) → (t : STm X) → STy X

Label-WT X S = Label X S × STy X

Label X S = Path S → STm X

SHere : STm (someTree S)
SHere = SPath PHere

compute-stm : STm X → STm X
compute-stm (SExt a) = SExt a
compute-stm (SShift a) = SShift a
compute-stm (SPath PHere) = SPath PHere
compute-stm (SPath (PExt x)) = SExt (SPath x)
compute-stm (SPath (PShift x)) = SShift (SPath x)
compute-stm (SCoh S A L) = SCoh S A L
compute-stm (SOther t) = SOther t

ap : Label-WT X S → Path S → STm X
ap = proj₁
{-# INLINE ap #-}

lty : Label-WT X S → STy X
lty = proj₂
{-# INLINE lty #-}

label₁ : (L : Label-WT X (Join S T)) → Label-WT X S
label₁ L = ap L ∘ PExt ,, SArr (ap L PHere) (lty L) (ap L (PShift PHere))

label₂ : (L : Label-WT X (Join S T)) → Label-WT X T
label₂ L = proj₁ L ∘ PShift ,, proj₂ L

variable
  L L′ M M′ : Label X S
  Lt : Label-WT X S
  a b c a′ b′ c′ : STm X
  As Bs Cs As′ Bs′ Cs′ : STy X

infixl 1 _>>=_
_>>=_ : STm (someTree S) → Label-WT X S → STm X
label-on-sty : STy (someTree S) → Label-WT X S → STy X
label-comp : Label (someTree T) S → Label-WT X T → Label X S

label-wt-comp : Label-WT (someTree T) S → Label-WT X T → Label-WT X S
label-wt-comp L M = label-comp (ap L) M ,, label-on-sty (lty L) M

SExt s >>= L = s >>= label₁ L
SShift s >>= L = s >>= label₂ L
SPath P >>= L = ap L P
SCoh S A M >>= L = SCoh S A (label-wt-comp M L)

label-on-sty S⋆ M = lty M
label-on-sty (SArr s A t) M = SArr (s >>= M) (label-on-sty A M) (t >>= M)

label-comp L M P = L P >>= M

id-label : (S : Tree n) → Label (someTree S) S
id-label S = SPath

id-label-wt : (S : Tree n) → Label-WT (someTree S) S
id-label-wt S = id-label S ,, S⋆
