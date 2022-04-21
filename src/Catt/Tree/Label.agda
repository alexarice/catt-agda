module Catt.Tree.Label where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection


data Label (m : ℕ) : Tree n → Set where
  LSing : (x : Tm m) → Label m Sing
  LJoin : (x : Tm m) → (L : Label m S) → (M : Label m T) → Label m (Join S T)

variable
  L L′ M M′  : Label n S

first-label : Label n S → Tm n
first-label (LSing x) = x
first-label (LJoin x L M) = x

label-to-sub : {S : Tree n} → Label m S → (A : Ty m) → Sub (suc n) m A
label-to-sub (LSing x) A = ⟨ ⟨⟩ , x ⟩
label-to-sub (LJoin x L M) A = sub-from-connect (unrestrict (label-to-sub L (x ─⟨ A ⟩⟶ first-label M))) (label-to-sub M A)

suspLabel : Label m S → Label (2 + m) S
suspLabel (LSing x) = LSing (suspTm x)
suspLabel (LJoin x L M) = LJoin (suspTm x) (suspLabel L) (suspLabel M)

_[_]l : Label m S → (σ : Sub m n B) → Label n S
LSing x [ σ ]l = LSing (x [ σ ]tm)
LJoin x S T [ σ ]l = LJoin (x [ σ ]tm) (S [ σ ]l) (T [ σ ]l)

id-label : (S : Tree n) → Label (suc n) S
id-label Sing = LSing 0V
id-label (Join S T) = LJoin (Var (fromℕ _)) ((suspLabel (id-label S)) [ (connect-susp-inc-left _ _) ]l) ((id-label T) [ (connect-susp-inc-right _ _) ]l)
