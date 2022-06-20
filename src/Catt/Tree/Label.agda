module Catt.Tree.Label where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree.Path

data Label (X : MaybeTree m) : Tree n → Set

data Label X where
  LSing : (P : Path X) → Label X Sing
  LJoin : (P : Path X) → (L : Label X S ) → (M : Label X T) → Label X (Join S T)

variable
  L L′ M M′ : Label X S

first-label : Label X S → Path X
first-label (LSing x) = x
first-label (LJoin x L M) = x

first-label-term : {X : MaybeTree m} → Label X S → Tm m
first-label-term L = path-to-term (first-label L)

last-label : Label X S → Path X
last-label (LSing x) = x
last-label (LJoin x L M) = last-label M

last-label-term : {X : MaybeTree m} → Label X S → Tm m
last-label-term L = path-to-term (last-label L)

label-to-tree : {S : Tree n} → (L : Label X S) → Tree n
label-to-tree {S = S} L = S

label-to-sub : {X : MaybeTree m} {S : Tree n} → Label X S → (A : Ty m) → Sub (suc n) m A
label-to-sub (LSing x) A = ⟨ ⟨⟩ , path-to-term x ⟩
label-to-sub (LJoin x L M) A = sub-from-connect (unrestrict (label-to-sub L (path-to-term x ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A)

map-label : (Path X → Path Y) → Label X S → Label Y S
map-label f (LSing P) = LSing (f P)
map-label f (LJoin P L M) = LJoin (f P) (map-label f L) (map-label f M)

map-term-label : {X : MaybeTree n} {Y : MaybeTree m} → (Tm n → Tm m) → Label X S → Label Y S
map-term-label f L = map-label (λ - → POther (f (path-to-term -))) L

suspLabel : Label (Other n) S → Label (Other (2 + n)) S
suspLabel = map-term-label suspTm

infixr 30 _[_]<_>l
_[_]<_>l : {X : MaybeTree m} → Label X S → (σ : Sub m n B) → (Y : MaybeTree n) → Label Y S
L [ σ ]< Y >l = map-term-label (_[ σ ]tm) L

Label-func : (X : MaybeTree m) → Tree n → Set
Label-func X S = PPath S → Path X

label-func₁ : Label-func X (Join S T) → Label-func X S
label-func₁ L P = L (PPExt P)

label-func₂ : Label-func X (Join S T) → Label-func X T
label-func₂ L P = L (PPShift P)

label-func-to-label : Label-func X S → Label X S
label-func-to-label {S = Sing} L = LSing (L PPHere)
label-func-to-label {S = Join S₁ S₂} L = LJoin (L PPHere) (label-func-to-label (label-func₁ L)) (label-func-to-label (label-func₂ L))

map-label-func : (Path X → Path Y) → Label-func X S → Label-func Y S
map-label-func f L P = f (L P)

id-label : (S : Tree n) → Label (someTree S) S
id-label Sing = LSing PHere
id-label (Join S T) = LJoin PHere (map-label PExt (id-label S)) (map-label PShift (id-label T))

id-label-func : (S : Tree n) → Label-func (someTree S) S
id-label-func S ⟦ P ⟧ = P

to-label : (S : Tree n) → (σ : Sub (suc n) m A) → (Y : MaybeTree m) → Label Y S
to-label S σ Y = id-label S [ σ ]< Y >l

to-label-func : (S : Tree n) → (σ : Sub (suc n) m A) → (Y : MaybeTree m) → Label-func Y S
to-label-func S σ Y ⟦ Z ⟧ = POther (path-to-term Z [ σ ]tm)

infix 45 _‼l_
_‼l_ : {X : MaybeTree m} → Label X S → Label-func X S
L ‼l ⟦ PHere ⟧ = first-label L
LJoin x L M ‼l ⟦ PExt P ⟧ = L ‼l ⟦ P ⟧
LJoin x L M ‼l ⟦ PShift P ⟧ = M ‼l ⟦ P ⟧

extend : {X : MaybeTree n} → Label-func X S → Ty n → Path (someTree S) → Path X
extend L A PHere = L PPHere
extend L A (PExt P) = extend (label-func₁ L) (path-to-term (L PPHere) ─⟨ A ⟩⟶ path-to-term (L (PPShift PPHere))) P
extend L A (PShift P) = extend (label-func₂ L) A P
extend L A (POther x) = POther (x [ label-to-sub (label-func-to-label L) A ]tm)

replace-label : Label X S
              → Path X
              → Label X S
replace-label (LSing _) t = LSing t
replace-label (LJoin _ L M) t = LJoin t L M

replace-label-func : Label-func X S
                   → Path X
                   → Label-func X S
replace-label-func L P ⟦ PHere ⟧ = P
replace-label-func L P ⟦ PExt Q ⟧ = L ⟦ PExt Q ⟧
replace-label-func L P ⟦ PShift Q ⟧ = L ⟦ PShift Q ⟧

connect-label : (L : Label X S)
              → (M : Label X T)
              → Label X (connect-tree S T)
connect-label (LSing x) M = replace-label M x
connect-label (LJoin x L L′) M = LJoin x L (connect-label L′ M)

label-func-split : Path X → ((P : PPath S) → .⦃ not-here P ⦄ → Path X) → Label-func X S
label-func-split P f ⟦ PHere ⟧ = P
label-func-split P f ⟦ PExt Z ⟧ = f ⟦ PExt Z ⟧
label-func-split P f ⟦ PShift Z ⟧ = f ⟦ PShift Z ⟧

connect-label-func : Label-func X S
                   → Label-func X T
                   → Label-func X (connect-tree S T)
connect-label-func L M = label-func-split (L PPHere) (helper L M)
  where
    helper : Label-func X S → Label-func X T → (P : PPath (connect-tree S T)) → .⦃ not-here P ⦄ → Path X
    helper {S = Sing} L M ⟦ Z ⟧ = M ⟦ Z ⟧
    helper {S = Join S₁ S₂} L M ⟦ PExt Z ⟧ = L ⟦ PExt Z ⟧
    helper {S = Join S₁ S₂} L M ⟦ PShift Z ⟧ = connect-label-func (label-func₂ L) M ⟦ Z ⟧

liftLabel : Label (Other n)  S → Label (Other (suc n)) S
liftLabel = map-term-label liftTerm

_>>=_ : Label-func (someTree T) S → Label-func X T → Label-func X S
(L >>= M) P = extend M ⋆ (L P)

connect-tree-inc-left : (S : Tree n) → (T : Tree m) → Label (someTree (connect-tree S T)) S
connect-tree-inc-left Sing T = LSing PHere
connect-tree-inc-left (Join S₁ S₂) T = LJoin PHere (map-label PExt (id-label S₁)) (map-label PShift (connect-tree-inc-left S₂ T))

connect-tree-inc-left-func : (S : Tree n) → (T : Tree m) → Label-func (someTree (connect-tree S T)) S
connect-tree-inc-left-func Sing T P = PHere
connect-tree-inc-left-func (Join S₁ S₂) T ⟦ PHere ⟧ = PHere
connect-tree-inc-left-func (Join S₁ S₂) T ⟦ PExt P ⟧ = PExt P
connect-tree-inc-left-func (Join S₁ S₂) T ⟦ PShift P ⟧ = PShift (connect-tree-inc-left-func S₂ T ⟦ P ⟧)

connect-tree-inc-right : (S : Tree n) → (T : Tree m) → Label (someTree (connect-tree S T)) T
connect-tree-inc-right Sing T = id-label T
connect-tree-inc-right (Join S₁ S₂) T = map-label PShift (connect-tree-inc-right S₂ T)

connect-tree-inc-right-func : (S : Tree n) → (T : Tree m) → Label-func (someTree (connect-tree S T)) T
connect-tree-inc-right-func Sing T = id-label-func T
connect-tree-inc-right-func (Join S₁ S₂) T P = PShift (connect-tree-inc-right-func S₂ T P)

label-between-connect-trees-func : (L : Label-func (someTree S′) S) → (M : Label-func (someTree T′) T) → Label-func (someTree (connect-tree S′ T′)) (connect-tree S T)
label-between-connect-trees-func {S′ = S′} {T′ = T′} L M = connect-label-func (L >>= (connect-tree-inc-left-func S′ T′)) (M >>= (connect-tree-inc-right-func S′ T′))

label-between-joins-func : (L : Label-func (someTree S′) S) → (M : Label-func (someTree T′) T) → Label-func (someTree (Join S′ T′)) (Join S T)
label-between-joins-func L M ⟦ PHere ⟧ = PHere
label-between-joins-func L M ⟦ PExt P ⟧ = PExt (L ⟦ P ⟧)
label-between-joins-func L M ⟦ PShift P ⟧ = PShift (M ⟦ P ⟧)
