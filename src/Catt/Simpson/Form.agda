{-# OPTIONS --safe --without-K #-}

module Catt.Simpson.Form where

open import Data.Nat
open import Catt.Fin
open import Data.List using (List; []; map)
open import Data.List.NonEmpty hiding (map)
open import Catt.Base
open import Catt.Syntax.Dimension
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    n dim submax dim′ dim″ pdd : ℕ


data Form : ℕ → ℕ → ℕ → Set where
  Base : Term n → Ty n (suc dim) → Form n (suc dim) zero
  Com : List (Form n (suc dim′) dim′) → Form n dim dim′ → List (Form n (suc dim′) dim′) → Form n dim (suc dim′)

TopForm : ℕ → ℕ → Set
TopForm n dim = List⁺ (Form n (suc dim) dim)

liftForm : Form n dim dim′ → Form (suc n) dim dim′
liftForm (Base t A) = Base (liftTerm t) (liftType A)
liftForm (Com before focus after) = Com (map liftForm before) (liftForm focus) (map liftForm after)

liftForm₂ : Form n dim dim′ → Form (2 + n) dim dim′
liftForm₂ f = liftForm (liftForm f)

add-to-tf-end : Form (2 + n) (suc dim) dim → TopForm n dim → TopForm (2 + n) dim
add-to-tf-end f tf = f ∷ map liftForm₂ (toList tf)

get-tgt-of-form : Form n (suc (suc dim)) dim′ → Form n (suc dim) dim′
get-tgt-of-form (Base _ (t ─⟨ A ⟩⟶ u)) = Base u A
get-tgt-of-form (Com before focus after) = Com before (get-tgt-of-form focus) after

to-top-form : Form n (suc dim) (suc dim) → TopForm n dim
to-top-form (Com before focus after) = after ++⁺ focus ∷ before


toFormPd : {Γ : Ctx n} → (Γ ⊢pd₀ (suc pdd)) → TopForm n pdd
toFormPdb : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n) dim} → (Γ ⊢pd x ∷ A [ submax ][ suc pdd ]) → TopForm (suc n) pdd

toFormPd (Finish pdb) = toFormPdb pdb

insert-cell-into-form : Ty (2 + n) (suc dim) → Form n dim dim′ → Form (2 + n) (suc dim) dim′
insert-cell-into-form A (Base i B) = Base (Var (fromℕ (suc _))) A
insert-cell-into-form A (Com before focus after) = Com (map liftForm₂ before) (insert-cell-into-form A focus) (map liftForm₂ after)

insert-cell : Ty (2 + n) (suc (suc dim)) → TopForm n dim → Form (2 + n) (suc (suc dim)) (suc dim)
insert-cell A (f ∷ before) = Com (map liftForm₂ before) (insert-cell-into-form A f) []

toFormPdb (ExtendM Base) = [ Base (Var (fromℕ 2)) ((Var (inject (inject (fromℕ 0)))) ─⟨ ⋆ ⟩⟶ (Var (inject (fromℕ 1)))) ]
toFormPdb {n} {d} {sm} {pd}{Γ = Γ , _ , B} {x} {A} a@(ExtendM pdb@(ExtendM _)) = [ insert-cell (liftType {!!}) (toFormPdb pdb) ]
toFormPdb (ExtendM pdb@(Extend _)) = [ insert-cell {!!} (toFormPdb pdb) ]
toFormPdb {submax = zero} {zero} (Extend pdb) with toFormPdb pdb
... | tf = add-to-tf-end (Base (Var (fromℕ _)) {!!}) tf
toFormPdb {submax = zero} {suc dim} (Extend pdb) with toFormPdb pdb
... | tf = {!!} -- add-to-tf-end (insert-cell {!!} (to-top-form (get-tgt-of-form (head tf)))) ? -- tf
toFormPdb {submax = suc n} (Extend pdb) = {!!}
toFormPdb (Restr pdb) = toFormPdb pdb
