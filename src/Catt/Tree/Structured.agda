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

maybe-tree-size : (X : MaybeTree n) → ℕ
maybe-tree-size {n} X = n

susp-maybe-tree : MaybeTree n → MaybeTree (2 + n)
susp-maybe-tree (someTree x) = someTree (Susp x)
susp-maybe-tree (Other _) = Other (2 + _)

susp-maybe-tree-n : (d : ℕ) → MaybeTree n → MaybeTree (d * 2 + n)
susp-maybe-tree-n zero X = X
susp-maybe-tree-n (suc d) X = susp-maybe-tree (susp-maybe-tree-n d X)

data CtxOrTree : ℕ → Set where
  incTree : Tree n → CtxOrTree (suc n)
  incCtx : Ctx n → CtxOrTree n

variable
  ΓS ΔT : CtxOrTree n

COT-to-MT : CtxOrTree n → MaybeTree n
COT-to-MT (incTree x) = someTree x
COT-to-MT (incCtx x) = Other _

COT-to-Ctx : CtxOrTree n → Ctx n
COT-to-Ctx (incTree x) = ⌊ x ⌋
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

infixl 25 _>>=_ _>>=′_
_>>=_ : STm (someTree S) → Label-WT X S → STm X
_>>=′_ : STy (someTree S) → Label-WT X S → STy X
infixl 31 _●l_
_●l_ : Label (someTree T) S → Label-WT X T → Label X S

infixl 31 _●lt_
_●lt_ : Label-WT (someTree T) S → Label-WT X T → Label-WT X S
L ●lt M = ap L ●l M ,, lty L >>=′ M

SExt a >>= L = a >>= label₁ L
SShift a >>= L = a >>= label₂ L
SPath x >>= L = ap L x
SCoh S A M >>= L = SCoh S A (M ●lt L)

_>>=′_ S⋆ M = lty M
_>>=′_ (SArr s A t) M = SArr (s >>= M) (A >>=′ M) (t >>= M)

(L ●l M) P = L P >>= M

id-label : (S : Tree n) → Label (someTree S) S
id-label S = SPath

id-label-wt : (S : Tree n) → Label-WT (someTree S) S
id-label-wt S = id-label S ,, S⋆

compute-stm : STm X → STm X
compute-stm (SExt a) = SExt a
compute-stm (SShift a) = SShift a
compute-stm (SPath PHere) = SHere
compute-stm (SPath (PExt x)) = SExt (SPath x)
compute-stm (SPath (PShift x)) = SShift (SPath x)
compute-stm (SCoh S A L) = SCoh S A L
compute-stm (SOther t) = SOther t
