module Catt.Tree.Label where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree.Path


data Label (m : ℕ) : Tree n → Set where
  LSing : (x : Tm m) → Label m Sing
  LJoin : (x : Tm m) → (L : Label m S) → (M : Label m T) → Label m (Join S T)

variable
  L L′ M M′  : Label n S

first-label : Label n S → Tm n
first-label (LSing x) = x
first-label (LJoin x L M) = x

last-label : Label n S → Tm n
last-label (LSing x) = x
last-label (LJoin x L M) = last-label M

label-to-tree : {S : Tree n} → (L : Label m S) → Tree n
label-to-tree {S = S} L = S

label-to-sub : {S : Tree n} → Label m S → (A : Ty m) → Sub (suc n) m A
label-to-sub (LSing x) A = ⟨ ⟨⟩ , x ⟩
label-to-sub (LJoin x L M) A = sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A)

suspLabel : Label m S → Label (2 + m) S
suspLabel (LSing x) = LSing (suspTm x)
suspLabel (LJoin x L M) = LJoin (suspTm x) (suspLabel L) (suspLabel M)

infixr 30 _[_]l
_[_]l : Label m S → (σ : Sub m n B) → Label n S
LSing x [ σ ]l = LSing (x [ σ ]tm)
LJoin x S T [ σ ]l = LJoin (x [ σ ]tm) (S [ σ ]l) (T [ σ ]l)

id-label : (S : Tree n) → Label (suc n) S
id-label Sing = LSing 0V
id-label (Join S T) = LJoin (Var (fromℕ _)) ((suspLabel (id-label S)) [ (connect-susp-inc-left _ _) ]l) ((id-label T) [ (connect-susp-inc-right _ _) ]l)

to-label : (S : Tree n) → (σ : Sub (suc n) m A) → Label m S
to-label S σ = id-label S [ σ ]l

infix 45 _‼l_
_‼l_ : Label m S → Path S → Tm m
L ‼l PHere = first-label L
LJoin x L M ‼l PExt P = L ‼l P
LJoin x L M ‼l PShift P = M ‼l P

replace-label : Label m S
              → Tm m
              → Label m S
replace-label (LSing _) t = LSing t
replace-label (LJoin _ L M) t = LJoin t L M

connect-label : (L : Label m S)
              → (M : Label m T)
              → Label m (connect-tree S T)
connect-label (LSing x) M = replace-label M x
connect-label (LJoin x L L′) M = LJoin x L (connect-label L′ M)

liftLabel : Label m S → Label (suc m) S
liftLabel (LSing x) = LSing (liftTerm x)
liftLabel (LJoin x L M) = LJoin (liftTerm x) (liftLabel L) (liftLabel M)

connect-tree-inc-left : (S : Tree n) → (T : Tree m) → Label (suc (connect-tree-length S T)) S
connect-tree-inc-left Sing T = LSing (Var (fromℕ _))
connect-tree-inc-left (Join S₁ S₂) T = connect-label (to-label (suspTree S₁) (connect-susp-inc-left _ _)) (connect-tree-inc-left S₂ T [ connect-susp-inc-right _ _ ]l)

connect-tree-inc-right : (S : Tree n) → (T : Tree m) → Label (suc (connect-tree-length S T)) T
connect-tree-inc-right Sing T = id-label T
connect-tree-inc-right (Join S₁ S₂) T = connect-tree-inc-right S₂ T [ connect-susp-inc-right _ _ ]l

label-between-connect-trees : (L : Label (suc m) S) → (M : Label (suc n) T) → (S′ : Tree m) → (T′ : Tree n) → Label (suc (connect-tree-length S′ T′)) (connect-tree S T)
label-between-connect-trees L M S′ T′ = connect-label (L [ label-to-sub (connect-tree-inc-left S′ T′) ⋆ ]l) (M [ label-to-sub (connect-tree-inc-right S′ T′) ⋆ ]l)

label-between-joins : (L : Label (suc m) S) → (M : Label (suc n) T) → (S′ : Tree m) → (T′ : Tree n) → Label (suc (n + (2 + m))) (Join S T)
label-between-joins L M S′ T′ = label-between-connect-trees (LJoin getFst (suspLabel L) (LSing getSnd)) M (suspTree S′) T′

Maximal-func : ℕ → (S : Tree n) → Set
Maximal-func m S = ∀ (P : Path S) → .⦃ is-Maximal P ⦄ → Tm m
