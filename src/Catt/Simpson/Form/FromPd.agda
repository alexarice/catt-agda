{-# OPTIONS --safe --without-K #-}

module Catt.Simpson.Form.FromPd where

open import Catt.Simpson.Form
open import Data.Nat
open import Catt.Base
open import Data.List using (map; []) renaming (_∷_ to _::_)
open import Data.List.NonEmpty renaming (map to maptf)

private
  variable
    n dim dim′ pdd submax : ℕ

liftForm : Form n dim dim′ → Form (suc n) dim dim′
liftForm (Base t A) = Base (liftTerm t) (liftType A)
liftForm (Com before focus after) = Com (map liftForm before) (liftForm focus) (map liftForm after)

liftForm₂ : Form n dim dim′ → Form (2 + n) dim dim′
liftForm₂ f = liftForm (liftForm f)

add-to-tf-end : Form (2 + n) (suc dim) dim → TopForm n (suc dim) → TopForm (2 + n) (suc dim)
add-to-tf-end f tf = f ∷ map liftForm₂ (toList tf)

toFormPd : {Γ : Ctx n} → (Γ ⊢pd₀ (suc pdd)) → TopForm n (suc pdd)
toFormPdb : {Γ : Ctx (suc n)} → {x : Term (suc n)} → {A : Ty (suc n) dim} → (Γ ⊢pd x ∷ A [ submax ][ suc pdd ]) → TopForm (suc n) (suc pdd)

toFormPd (Finish pdb) = toFormPdb pdb

insert-cell-into-form : Ty (2 + n) (suc dim) → Form n dim dim′ → Form (2 + n) (suc dim) dim′
insert-cell-into-form A (Base i B) = Base (Var (fromℕ (suc _))) A
insert-cell-into-form A (Com before focus after) = Com (map liftForm₂ before) (insert-cell-into-form A focus) (map liftForm₂ after)

insert-cell : Ty (2 + n) (suc dim) → TopForm n dim → Form (2 + n) (suc dim) dim
insert-cell {dim = zero} A _ = Base (Var (fromℕ (suc _))) A
insert-cell {dim = suc dim} A (f ∷ before) = Com (map liftForm₂ before) (insert-cell-into-form A f) []

add-to-end : Form n (suc dim′) dim′ → Form n dim (suc dim′) → Form n dim (suc dim′)
add-to-end a (Com before focus after) = Com before focus (a :: after)

append-to-form : ∀ submax {dim} x → Ty (2 + n) (suc dim) → Form n ((suc x) + dim) (suc submax + dim) → Form (2 + n) (suc x + dim) (suc submax + dim)
append-to-form zero x A (Com before focus []) = add-to-end (insert-cell A (to-top-form (get-tgt-full x focus))) (liftForm₂ (Com before focus []))
append-to-form zero x A f@(Com before focus (a :: after)) = add-to-end (insert-cell A (to-top-form (get-tgt-of-form a))) (liftForm₂ f)
append-to-form (suc submax) x A (Com before focus after) = Com (map (append-to-form submax (suc submax) A) before) (append-to-form submax x A focus) (map (append-to-form submax (suc submax) A) after)

toFormPdb (ExtendM Base) = [ Base (Var (fromℕ 2)) ((Var (inject (inject (fromℕ 0)))) ─⟨ ⋆ ⟩⟶ (Var (inject (fromℕ 1)))) ]
toFormPdb {Γ = Γ , B} (ExtendM pdb@(ExtendM _)) = [ insert-cell (liftType B) (toFormPdb pdb) ]
toFormPdb {Γ = Γ , B} (ExtendM pdb@(Extend _))  = [ insert-cell (liftType B) (toFormPdb pdb) ]
toFormPdb {submax = zero} {Γ = Γ , B} (Extend pdb) with toFormPdb pdb
... | tf = add-to-tf-end (insert-cell (liftType B) (to-top-form (get-tgt-of-form (head tf)))) tf
toFormPdb {submax = suc n} {Γ = Γ , B} (Extend pdb) with toFormPdb pdb
... | tf = maptf (append-to-form n (suc n) (liftType B)) tf
toFormPdb (Restr pdb) = toFormPdb pdb
