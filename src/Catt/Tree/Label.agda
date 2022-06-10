module Catt.Tree.Label where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree.Path

data Label (X : MaybeTree m) : Tree n → Set where
  LSing : (P : Path X) → Label X Sing
  LJoin : (P : Path X) → (L : Label X S) → (M : Label X T) → Label X (Join S T)

variable
  L L′ M M′  : Label X S

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

id-label : (S : Tree n) → Label (someTree S) S
id-label Sing = LSing PHere
id-label (Join S T) = LJoin PHere (map-label PExt (id-label S)) (map-label PShift (id-label T))

to-label : (S : Tree n) → (σ : Sub (suc n) m A) → (Y : MaybeTree m) → Label Y S
to-label S σ Y = id-label S [ σ ]< Y >l

infix 45 _‼<_>_
_‼<_>_ : {X : MaybeTree m} → Label X S → Ty m → Path (someTree S) → Path X
L ‼< A > PHere = first-label L
L ‼< A > POther t = POther (t [ label-to-sub L A ]tm)
LJoin x L M ‼< A > PExt P = L ‼< path-to-term x ─⟨ A ⟩⟶ first-label-term M > P
LJoin x L M ‼< A > PShift P = M ‼< A > P

replace-label : Label X S
              → Path X
              → Label X S
replace-label (LSing _) t = LSing t
replace-label (LJoin _ L M) t = LJoin t L M

connect-label : (L : Label X S)
              → (M : Label X T)
              → Label X (connect-tree S T)
connect-label (LSing x) M = replace-label M x
connect-label (LJoin x L L′) M = LJoin x L (connect-label L′ M)

liftLabel : Label (Other n)  S → Label (Other (suc n)) S
liftLabel = map-term-label liftTerm

label-comp : Label (someTree T) S → Label X T → Label X S
label-comp (LSing P) M = LSing (M ‼< ⋆ > P)
label-comp (LJoin P L L′) M = LJoin (M ‼< ⋆ > P) (label-comp L M) (label-comp L′ M)

connect-tree-inc-left : (S : Tree n) → (T : Tree m) → Label (someTree (connect-tree S T)) S
connect-tree-inc-left Sing T = LSing PHere
connect-tree-inc-left (Join S₁ S₂) T = LJoin PHere (map-label PExt (id-label S₁)) (map-label PShift (connect-tree-inc-left S₂ T))

connect-tree-inc-right : (S : Tree n) → (T : Tree m) → Label (someTree (connect-tree S T)) T
connect-tree-inc-right Sing T = id-label T
connect-tree-inc-right (Join S₁ S₂) T = map-label PShift (connect-tree-inc-right S₂ T)

label-between-connect-trees : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → Label (someTree (connect-tree S′ T′)) (connect-tree S T)
label-between-connect-trees {S′ = S′} {T′ = T′} L M = connect-label (label-comp L (connect-tree-inc-left S′ T′)) (label-comp M (connect-tree-inc-right S′ T′))

label-between-joins : (L : Label (someTree S′) S) → (M : Label (someTree T′) T) → Label (someTree (Join S′ T′)) (Join S T)
label-between-joins L M = label-between-connect-trees (LJoin PHere (map-label PExt L) (LSing (PShift PHere))) M
