module Catt.Tree.Label where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Tree.Properties
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

SHere : STm (someTree S)
SHere = SPath PHere

Label X S = Path S → STm X

sty-dim : STy X → ℕ
sty-dim S⋆ = 0
sty-dim (SArr s A t) = suc (sty-dim A)

stm-to-term : {X : MaybeTree n} → STm X → Tm n
sty-to-type : {X : MaybeTree n} → STy X → Ty n
label-to-sub : {X : MaybeTree n} → (L : Label-WT X S) → Sub (suc (tree-size S)) n (sty-to-type (proj₂ L))

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

lty : Label-WT X S → STy X
lty = proj₂
{-# INLINE lty #-}

variable
  L L′ M M′ : Label X S
  Lt : Label-WT X S
  a b c a′ b′ c′ : STm X
  As Bs Cs : STy X

label₁ : (L : Label-WT X (Join S T)) → Label-WT X S
label₁ L = ap L ∘ PExt ,, SArr (ap L PHere) (lty L) (ap L (PShift PHere))

label₂ : (L : Label-WT X (Join S T)) → Label-WT X T
label₂ L = proj₁ L ∘ PShift ,, proj₂ L

stm-to-term (SExt s) = suspTm (stm-to-term s) [ connect-susp-inc-left _ _ ]tm
stm-to-term (SShift s) = stm-to-term s [ connect-susp-inc-right _ _ ]tm
stm-to-term (SPath P) = path-to-term P
stm-to-term (SCoh S A L) = Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm
stm-to-term (SOther t) = t

sty-to-type S⋆ = ⋆
sty-to-type (SArr s A t) = (stm-to-term s) ─⟨ (sty-to-type A) ⟩⟶ (stm-to-term t)

label-to-sub′ : ((P : Path S) → Tm n) → (A : Ty n) → Sub (suc (tree-size S)) n A
label-to-sub′ {S = Sing} f A = ⟨ ⟨⟩ , f PHere ⟩
label-to-sub′ {S = Join S₁ S₂} f A = sub-from-connect (unrestrict (label-to-sub′ (λ P → f (PExt P)) (f PHere ─⟨ A ⟩⟶ f (PShift PHere)))) (label-to-sub′ (λ P → f (PShift P)) A)

label-to-sub (L ,, A) = label-to-sub′ (λ P → stm-to-term (L P)) (sty-to-type A)

map-sty-pext : STy (someTree S) → STy (someTree (Join S T))
map-sty-pext S⋆ = SArr SHere S⋆ (SShift (SPath PHere))
map-sty-pext (SArr s A t) = SArr (SExt s) (map-sty-pext A) (SExt t)

map-pext : Label-WT (someTree S) U → Label-WT (someTree (Join S T)) U
map-pext L = SExt ∘ ap L ,, (map-sty-pext (lty L))

map-sty-pshift : STy (someTree T) → STy (someTree (Join S T))
map-sty-pshift S⋆ = S⋆
map-sty-pshift (SArr s A t) = SArr (SShift s) (map-sty-pshift A) (SShift t)

map-pshift : Label-WT (someTree T) U → Label-WT (someTree (Join S T)) U
map-pshift L = SShift ∘ ap L ,, map-sty-pshift (lty L)

lift-stm : STm (Other n) → STm (Other (suc n))
lift-sty : STy (Other n) → STy (Other (suc n))
lift-label : Label-WT (Other n) S → Label-WT (Other (suc n)) S

lift-stm (SCoh S A L) = SCoh S A (lift-label L)
lift-stm (SOther t) = SOther (liftTerm t)

lift-sty S⋆ = S⋆
lift-sty (SArr s A t) = SArr (lift-stm s) (lift-sty A) (lift-stm t)

lift-label L = lift-stm ∘ (ap L) ,, lift-sty (lty L)

susp-stm : STm X → STm (suspMaybeTree X)
susp-sty : STy X → STy (suspMaybeTree X)
susp-label : Label-WT X S → Label-WT (suspMaybeTree X) S
susp-label-full : Label X S → Label (suspMaybeTree X) (suspTree S)

stm-fst : STm (suspMaybeTree X)
stm-snd : STm (suspMaybeTree X)

stm-fst {X = someTree x} = SHere
stm-fst {X = Other _} = SOther getFst

stm-snd {X = someTree x} = SPath (PShift PHere)
stm-snd {X = Other _} = SOther getSnd

susp-stm {X = someTree x} s = SExt s
susp-stm {X = Other _} (SCoh S A L) = SCoh S A (susp-label L)
susp-stm {X = Other _} (SOther t) = SOther (suspTm t)

susp-sty S⋆ = SArr stm-fst S⋆ stm-snd
susp-sty (SArr s A t) = SArr (susp-stm s) (susp-sty A) (susp-stm t)

susp-label L = susp-stm ∘ (ap L) ,, susp-sty (lty L)

susp-label-full L PHere = stm-fst
susp-label-full L (PShift PHere) = stm-snd
susp-label-full L (PExt P) = susp-stm (L P)

to-sty : Ty n → STy (Other n)
to-sty ⋆ = S⋆
to-sty (s ─⟨ A ⟩⟶ t) = SArr (SOther s) (to-sty A) (SOther t)

sty-sub : {X : MaybeTree n} → STy X → (σ : Sub n m B) → STy (Other m)
sty-sub {B = B} S⋆ σ = to-sty B
sty-sub (SArr s A t) σ = SArr (SOther (stm-to-term s [ σ ]tm)) (sty-sub A σ) (SOther (stm-to-term t [ σ ]tm))

label-sub : {X : MaybeTree n} → Label-WT X S → (σ : Sub n m B) → Label-WT (Other m) S
label-sub L σ = SOther ∘ _[ σ ]tm ∘ stm-to-term ∘ ap L ,, sty-sub (lty L) σ

id-label : (S : Tree n) → Label (someTree S) S
id-label S = SPath

id-label-wt : (S : Tree n) → Label-WT (someTree S) S
id-label-wt S = id-label S ,, S⋆

to-label : (S : Tree n) → (σ : Sub (suc n) m A) → Label (Other m) S
to-label S σ Z = SOther (path-to-term Z [ σ ]tm)

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
label-between-connect-trees {S′ = S′} {T′ = T′} L M = connect-label (label-comp L (connect-tree-inc-left S′ T′)) (label-comp M (connect-tree-inc-right S′ T′))

label-between-joins : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → Label (someTree (Join S′ T′)) (Join S T)
label-between-joins L M PHere = SHere
label-between-joins L M (PExt P) = SExt (L P)
label-between-joins L M (PShift P) = SShift (M P)

stm-≃ : (S ≃′ T) → STm (someTree S) → STm (someTree T)
sty-≃ : (S ≃′ T) → STy (someTree S) → STy (someTree T)
≃-label : (S ≃′ T) → Label (someTree S) U → Label (someTree T) U

stm-≃ Refl≃′ a = a
stm-≃ (Join≃′ p q) (SExt a) = SExt (stm-≃ p a)
stm-≃ (Join≃′ p q) (SShift a) = SShift (stm-≃ q a)
stm-≃ (Join≃′ p q) (SPath x) = SPath (ppath-≃ (Join≃′ p q) x)
stm-≃ (Join≃′ p q) (SCoh S A (L ,, B)) = SCoh S A ((≃-label (Join≃′ p q) L) ,, sty-≃ (Join≃′ p q) B)

sty-≃ p S⋆ = S⋆
sty-≃ p (SArr s A t) = SArr (stm-≃ p s) (sty-≃ p A) (stm-≃ p t)

≃-label p L = stm-≃ p ∘ L
