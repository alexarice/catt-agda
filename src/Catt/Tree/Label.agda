module Catt.Tree.Label where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree.Path

Label : (X : MaybeTree m) → (S : Tree n) → Set
Label X S = PPath S → Path X

Label′ : (T : Tree m) → (S : Tree n) → Set
Label′ T S = PPath S → PPath T

variable
  L L′ M M′ : Label X S

convert-type : Label X S A → (B : Ty _) → Label X S B
convert-type L B .ap Z = ap L Z

prepend : Label-func′ S T → Label X S A → Label X T A
prepend L M .ap Z = ap M (L Z)

label₁ : (L : Label X (Join S T) A) → Label X S (apt L PPHere ─⟨ A ⟩⟶ apt L (PPShift PPHere))
label₁ L .ap Z = ap L (PPExt Z)

label₂ : (L : Label X (Join S T) A) → Label X T A
label₂ L .ap Z = ap L (PPShift Z)

map-lf : (Path X → Path Y) → Label-func X S → Label-func Y S
map-lf f L Z = f (L Z)

map-pext : Label (someTree S) U A → Label (someTree (Join S T)) U (suspTy A [ connect-susp-inc-left (tree-size S) (tree-size T) ]ty)
map-pext L .ap = map-lf PExt (ap L)

map-pshift : Label (someTree T) U A → Label (someTree (Join S T)) U (A [ connect-susp-inc-right (tree-size S) (tree-size T) ]ty)
map-pshift L .ap = map-lf PShift (ap L)

lift-label : Label (Other n) S A → Label (Other (suc n)) S (liftType A)
lift-label L .ap Z = POther (liftTerm (apt L Z))

susp-label : Label X S A → Label (suspMaybeTree X) S (suspTy A)
susp-label L .ap Z = susp-path (ap L Z)

label-sub : {X : MaybeTree n} → Label X S A → (Y : MaybeTree m) → (σ : Sub n m B) → Label Y S (A [ σ ]ty)
label-sub L Y σ .ap Z = POther (apt L Z [ σ ]tm)

label-to-sub : {X : MaybeTree n} → Label X S A → Sub (suc (tree-size S)) n A
label-to-sub {S = Sing} L = ⟨ ⟨⟩ , (apt L PPHere) ⟩
label-to-sub {S = Join S₁ S₂} L = sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))

id-label : (S : Tree n) → Label (someTree S) S ⋆
id-label S .ap P = carrier P

to-label : (S : Tree n) → (σ : Sub (suc n) m A) → (Y : MaybeTree m) → Label Y S A
to-label S σ Y .ap Z = POther (path-to-term (carrier Z) [ σ ]tm)

infixl 1 _>>=_
_>>=_ : Path (someTree S) → Label X S A → Path X
PHere >>= L = ap L PPHere
PExt P >>= L = P >>= label₁ L
PShift P >>= L = P >>= label₂ L
POther x >>= L = POther (x [ label-to-sub L ]tm)

label-comp : Label (someTree T) S A → (M : Label X T B) → Label X S (A [ label-to-sub M ]ty)
label-comp L M .ap P = ap L P >>= M

replace-label-func : Label-func X S → Path X → Label-func X S
replace-label-func L P ⟦ PHere ⟧ = P
replace-label-func L P ⟦ PExt Z ⟧ = L ⟦ PExt Z ⟧
replace-label-func L P ⟦ PShift Z ⟧ = L ⟦ PShift Z ⟧

replace-label : Label X S A → Path X → Label X S A
replace-label L P .ap = replace-label-func (ap L) P

connect-label-func : Label-func X S
                   → Label-func X T
                   → Label-func X (connect-tree S T)
connect-label-func {S = Sing} L M = replace-label-func M (L PPHere)
connect-label-func {S = Join S₁ S₂} L M ⟦ PHere ⟧ = L PPHere
connect-label-func {S = Join S₁ S₂} L M ⟦ PExt Z ⟧ = L ⟦ PExt Z ⟧
connect-label-func {S = Join S₁ S₂} L M ⟦ PShift Z ⟧ = connect-label-func (λ x → L (PPShift x)) M ⟦ Z ⟧

connect-label : Label X S A
              → Label X T A
              → Label X (connect-tree S T) A
connect-label L M .ap = connect-label-func (ap L) (ap M)

connect-tree-inc-left : (S : Tree n) → (T : Tree m) → Label (someTree (connect-tree S T)) S ⋆
connect-tree-inc-left Sing T .ap P = PHere
connect-tree-inc-left (Join S₁ S₂) T .ap ⟦ PHere ⟧ = PHere
connect-tree-inc-left (Join S₁ S₂) T .ap ⟦ PExt P ⟧ = PExt P
connect-tree-inc-left (Join S₁ S₂) T .ap ⟦ PShift P ⟧ = PShift (connect-tree-inc-left S₂ T .ap ⟦ P ⟧)

connect-tree-inc-right : (S : Tree n) → (T : Tree m) → Label (someTree (connect-tree S T)) T ⋆
connect-tree-inc-right Sing T = id-label T
connect-tree-inc-right (Join S₁ S₂) T .ap P = PShift (connect-tree-inc-right S₂ T .ap P)

label-between-connect-trees : (L : Label (someTree S′) S ⋆) → (M : Label (someTree T′) T ⋆) → Label (someTree (connect-tree S′ T′)) (connect-tree S T) ⋆
label-between-connect-trees {S′ = S′} {T′ = T′} L M = connect-label (label-comp L (connect-tree-inc-left S′ T′)) (label-comp M (connect-tree-inc-right S′ T′))

label-between-joins : (L : Label (someTree S′) S ⋆) → (M : Label (someTree T′) T ⋆) → Label (someTree (Join S′ T′)) (Join S T) ⋆
label-between-joins L M .ap ⟦ PHere ⟧ = PHere
label-between-joins L M .ap ⟦ PExt P ⟧ = PExt (ap L ⟦ P ⟧)
label-between-joins L M .ap ⟦ PShift P ⟧ = PShift (ap M ⟦ P ⟧)
