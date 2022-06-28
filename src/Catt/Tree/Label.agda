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

record Label (X : MaybeTree m) (S : Tree n) (A : Ty m) : Set

data STm : MaybeTree n → Set where
  SHere : STm (someTree S)
  SExt : STm (someTree S) → STm (someTree (Join S T))
  SShift : STm (someTree T) → STm (someTree (Join S T))
  SCoh : (S : Tree m) → (A : Ty (suc m)) → (L : Label X S B) → STm X
  SOther : (t : Tm n) → STm (Other n)

path-to-stm : Path S → STm (someTree S)
path-to-stm PHere = SHere
path-to-stm (PExt P) = SExt (path-to-stm P)
path-to-stm (PShift P) = SShift (path-to-stm P)

Label-func : (X : MaybeTree m) → (S : Tree n) → Set
Label-func X S = Path S → STm X

Label-func′ : (T : Tree m) → (S : Tree n) → Set
Label-func′ T S = Path S → Path T

stm-to-term : {X : MaybeTree n} → STm X → Tm n
label-to-sub : {X : MaybeTree n} → Label X S A → Sub (suc (tree-size S)) n A

record Label {m} X S A where
  inductive
  field
    ap : Label-func X S

  apt : Path S → Tm m
  apt P = stm-to-term (ap P)

  lty : Ty m
  lty = A

open Label public

variable
  L L′ M M′ : Label X S A
  a b c : STm X

label₁ : (L : Label X (Join S T) A) → Label X S (apt L PHere ─⟨ A ⟩⟶ apt L (PShift PHere))
label₁ L .ap Z = ap L (PExt Z)

label₂ : (L : Label X (Join S T) A) → Label X T A
label₂ L .ap Z = ap L (PShift Z)

stm-to-term SHere = Var (fromℕ _)
stm-to-term (SExt s) = suspTm (stm-to-term s) [ connect-susp-inc-left _ _ ]tm
stm-to-term (SShift s) = stm-to-term s [ connect-susp-inc-right _ _ ]tm
stm-to-term (SCoh S A L) = Coh (tree-to-ctx S) A idSub [ label-to-sub L ]tm
stm-to-term (SOther t) = t

label-to-sub′ : ((P : Path S) → Tm n) → (A : Ty n) → Sub (suc (tree-size S)) n A
label-to-sub′ {S = Sing} f A = ⟨ ⟨⟩ , f PHere ⟩
label-to-sub′ {S = Join S₁ S₂} f A = sub-from-connect (unrestrict (label-to-sub′ (λ P → f (PExt P)) (f PHere ─⟨ A ⟩⟶ f (PShift PHere)))) (label-to-sub′ (λ P → f (PShift P)) A)

label-to-sub {A = A} L = label-to-sub′ (λ P → stm-to-term (ap L P)) A

path-to-term′ : (P : Path S) → Tm (suc (tree-size S))
path-to-term′ P = stm-to-term (path-to-stm P)

label-func′-to-label : (L : Label-func′ T S) → (A : Ty (suc (tree-size T))) → Label (someTree T) S A
label-func′-to-label L A .ap P = path-to-stm (L P)

convert-type : Label X S A → (B : Ty _) → Label X S B
convert-type L B .ap Z = ap L Z

prepend : Label-func′ S T → Label X S A → Label X T A
prepend L M .ap Z = ap M (L Z)

map-lf : (STm X → STm Y) → Label-func X S → Label-func Y S
map-lf f L Z = f (L Z)

map-pext : Label (someTree S) U A → Label (someTree (Join S T)) U (suspTy A [ connect-susp-inc-left (tree-size S) (tree-size T) ]ty)
map-pext L .ap = map-lf SExt (ap L)

map-pshift : Label (someTree T) U A → Label (someTree (Join S T)) U (A [ connect-susp-inc-right (tree-size S) (tree-size T) ]ty)
map-pshift L .ap = map-lf SShift (ap L)

lift-stm : STm (Other n) → STm (Other (suc n))
lift-label : Label (Other n) S A → Label (Other (suc n)) S (liftType A)

lift-stm (SCoh S A L) = SCoh S A (lift-label L)
lift-stm (SOther t) = SOther (liftTerm t)

lift-label L .ap Z = lift-stm (ap L Z)

susp-stm : STm X → STm (suspMaybeTree X)
susp-label : Label X S A → Label (suspMaybeTree X) S (suspTy A)

susp-stm {X = someTree x} s = SExt s
susp-stm {X = Other _} (SCoh S A L) = SCoh S A (susp-label L)
susp-stm {X = Other _} (SOther t) = SOther (suspTm t)

susp-label L .ap Z = susp-stm (ap L Z)

label-sub : {X : MaybeTree n} → Label X S A → (σ : Sub n m B) → Label (Other m) S (A [ σ ]ty)
label-sub L σ .ap Z = SOther (apt L Z [ σ ]tm)

id-label : (S : Tree n) → Label (someTree S) S ⋆
id-label S .ap P = path-to-stm P

to-label : (S : Tree n) → (σ : Sub (suc n) m A) → Label (Other m) S A
to-label S σ .ap Z = SOther (path-to-term Z [ σ ]tm)

infixl 1 _>>=_
_>>=_ : STm (someTree S) → Label X S A → STm X
label-comp : Label (someTree T) S A → (M : Label X T B) → Label X S (A [ label-to-sub M ]ty)

SHere >>= L = ap L PHere
SExt s >>= L = s >>= label₁ L
SShift s >>= L = s >>= label₂ L
SCoh S A M >>= L = SCoh S A (label-comp M L)

label-comp L M .ap P = ap L P >>= M

replace-label-func : Label-func X S → STm X → Label-func X S
replace-label-func L P PHere = P
replace-label-func L P (PExt Z) = L (PExt Z)
replace-label-func L P (PShift Z) = L (PShift Z)

replace-label : Label X S A → STm X → Label X S A
replace-label L P .ap = replace-label-func (ap L) P

connect-label-func : Label-func X S
                   → Label-func X T
                   → Label-func X (connect-tree S T)
connect-label-func {S = Sing} L M = replace-label-func M (L PHere)
connect-label-func {S = Join S₁ S₂} L M PHere = L PHere
connect-label-func {S = Join S₁ S₂} L M (PExt Z) = L (PExt Z)
connect-label-func {S = Join S₁ S₂} L M (PShift Z) = connect-label-func (λ x → L (PShift x)) M Z

connect-label : Label X S A
              → Label X T A
              → Label X (connect-tree S T) A
connect-label L M .ap = connect-label-func (ap L) (ap M)

connect-tree-inc-left-func : (S : Tree n) → (T : Tree m) → Label-func′ (connect-tree S T) S
connect-tree-inc-left-func Sing T P = PHere
connect-tree-inc-left-func (Join S₁ S₂) T PHere = PHere
connect-tree-inc-left-func (Join S₁ S₂) T (PExt P) = PExt P
connect-tree-inc-left-func (Join S₁ S₂) T (PShift P) = PShift (connect-tree-inc-left-func S₂ T P)

connect-tree-inc-right-func : (S : Tree n) → (T : Tree m) → Label-func′ (connect-tree S T) T
connect-tree-inc-right-func Sing T P = P
connect-tree-inc-right-func (Join S₁ S₂) T P = PShift (connect-tree-inc-right-func S₂ T P)

connect-tree-inc-left : (S : Tree n) → (T : Tree m) → Label (someTree (connect-tree S T)) S ⋆
connect-tree-inc-left S T = label-func′-to-label (connect-tree-inc-left-func S T) ⋆

connect-tree-inc-right : (S : Tree n) → (T : Tree m) → Label (someTree (connect-tree S T)) T ⋆
connect-tree-inc-right S T = label-func′-to-label (connect-tree-inc-right-func S T) ⋆

label-between-connect-trees : (L : Label (someTree S′) S ⋆) → (M : Label (someTree T′) T ⋆) → Label (someTree (connect-tree S′ T′)) (connect-tree S T) ⋆
label-between-connect-trees {S′ = S′} {T′ = T′} L M = connect-label (label-comp L (connect-tree-inc-left S′ T′)) (label-comp M (connect-tree-inc-right S′ T′))

label-between-joins : (L : Label (someTree S′) S ⋆) → (M : Label (someTree T′) T ⋆) → Label (someTree (Join S′ T′)) (Join S T) ⋆
label-between-joins L M .ap PHere = SHere
label-between-joins L M .ap (PExt P) = SExt (ap L P)
label-between-joins L M .ap (PShift P) = SShift (ap M P)
