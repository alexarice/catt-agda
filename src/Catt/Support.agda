{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Support where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec hiding (drop ; [_])
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Catt.Syntax
-- open import Catt.Syntax.Properties
-- open import Catt.Dimension
open import Data.Bool using (true;false;_∨_;Bool;if_then_else_;not)
open import Data.Fin using (Fin;zero;suc;fromℕ)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Unit using (tt; ⊤)
-- open import Catt.Globular
open import Catt.Tree
open import Catt.Tree.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Suspension
-- open import Catt.Dimension
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Connection
open import Catt.Pasting
open import Catt.Tree.Pasting
open import Catt.Connection.Pasting
open import Catt.Variables

-- record VarSet (Γ : Ctx n) : Set where
--   constructor [_]v
--   field
--     get : Vec Bool (ctxLength Γ)

VarSet : ℕ → Set
VarSet = Vec Bool

empty : VarSet n
empty = replicate false

full : VarSet n
full = replicate true

pattern ewt xs = true ∷ xs
pattern ewf xs = false ∷ xs
pattern emp = []

drop : VarSet n → VarSet n
drop emp = emp
drop (ewf xs) = ewf (drop xs)
drop (ewt xs) = ewf xs

trueAt : Fin n → VarSet n
trueAt {n = suc n} zero = ewt empty
trueAt {n = suc n} (suc i) = ewf (trueAt i)

infixl 60 _∪_
_∪_ : VarSet n → VarSet n → VarSet n
emp ∪ emp = emp
(x ∷ xs) ∪ (y ∷ ys) = (x ∨ y) ∷ xs ∪ ys

-- Supp : (x : CtxSyntax n) → VarSet n
-- Supp = ≺-rec (λ {n} _ → VarSet n) r
--   where
--     r : (x : CtxSyntax n) → (∀ {m} → (y : CtxSyntax m) → y ≺ x → VarSet m) → VarSet n
--     r (CtxTm (Var zero) (Γ , A)) rec = ewt (rec (CtxTy A Γ) Tm1)
--     r (CtxTm (Var (suc i)) (Γ , A)) rec = ewf (rec (CtxTm (Var i) Γ) Tm2)
--     r (CtxTm (Coh S A σ) Γ) rec = rec (CtxSub σ Γ) Tm4
--     r (CtxTy ⋆ Γ) rec = empty
--     r (CtxTy (s ─⟨ A ⟩⟶ t) Γ) rec = rec (CtxTy A Γ) Ty2 ∪ rec (CtxTm s Γ) Ty1 ∪ rec (CtxTm t Γ) Ty3
--     r (CtxSub ⟨⟩ Γ) rec = rec (CtxTy _ Γ) Sub1
--     r (CtxSub ⟨ σ , t ⟩ Γ) rec = (rec (CtxSub σ Γ) Sub2) ∪ (rec (CtxTm t Γ) Sub3)

FVCtx : (Γ : Ctx n) → VarSet n
FVTm : (t : Tm n) → VarSet n
FVTy : (A : Ty n) → VarSet n
FVSub : (σ : Sub n m A) → VarSet m

FVCtx Γ = full
FVTm (Var i) = trueAt i
FVTm (Coh Δ A σ) = FVSub σ
FVTy ⋆ = empty
FVTy (s ─⟨ A ⟩⟶ t) = FVTy A ∪ FVTm s ∪ FVTm t
FVSub {A = A} ⟨⟩ = FVTy A
FVSub ⟨ σ , t ⟩ = FVSub σ ∪ FVTm t

TransportVarSet : VarSet n → Sub n m A → VarSet m
TransportVarSet xs ⟨⟩ = empty
TransportVarSet (ewf xs) ⟨ σ , t ⟩ = TransportVarSet xs σ
TransportVarSet (ewt xs) ⟨ σ , t ⟩ = TransportVarSet xs σ ∪ FVTm t

connect-supp : VarSet (suc n) → VarSet (suc m) → VarSet (suc (m + n))
connect-supp {m = zero} xs ys = xs
connect-supp {m = suc m} xs (x ∷ ys) = x ∷ connect-supp xs ys

suspSupp : VarSet n → VarSet (2 + n)
suspSupp [] = full
suspSupp (x ∷ vs) = x ∷ suspSupp vs

_//_ : VarSet n → VarSet n → VarSet n
emp // ys = emp
(x ∷ xs) // ewf ys = x ∷ (xs // ys)
(x ∷ xs) // ewt ys = ewf (xs // ys)

supp-bd′ : (d : ℕ) → (Γ : Ctx n) → (b : Bool) → VarSet n
supp-bd′ d ∅ b = emp
supp-bd′ d (Γ , A) b with d <? ty-dim A
... | yes p = ewf (supp-bd′ d Γ b // FVTm (if b then ty-src< A p else ty-tgt< A p))
... | no p = ewt (supp-bd′ d Γ b)

-- supp-bd′-connect : (d : ℕ) → (Γ : Ctx (suc n)) → (t : Tm (suc n)) → (Δ : Ctx (suc m)) → (b : Bool) → supp-bd′ (suc d) (connect Γ t Δ) b ≡ connect-supp (supp-bd′ (suc d) Γ b) (supp-bd′ (suc d) Δ b)
-- supp-bd′-connect d Γ t (∅ , A) b with (suc d <? ty-dim A)
-- ... | yes p = refl
-- ... | no p = refl
-- supp-bd′-connect d Γ t (Δ , B , A) b with suc d <? ty-dim A | suc d <? ty-dim (A [ connect-inc-right t (ctxLength Δ) ]ty)
-- ... | yes p | yes q = {!!}
-- ... | yes p | no q = ⊥-elim (q (<-transˡ p (≤-reflexive (sub-dim (connect-inc-right t _) A))))
-- ... | no p | yes q = ⊥-elim (p (<-transˡ q (≤-reflexive (sym (sub-dim (connect-inc-right t _) A)))))
-- ... | no p | no q = {!!}

supp-bd : (d : ℕ) → (T : Tree n) → (b : Bool) → VarSet (suc n)
supp-bd zero T false = trueAt (fromℕ _)
supp-bd zero T true = FVTm (tree-last-var T)
supp-bd (suc d) Sing b = full
supp-bd (suc d) (Join S T) b = connect-supp (suspSupp (supp-bd d S b)) (supp-bd (suc d) T b)

supp-condition : (b : Bool) → (A : Ty (suc n)) → (T : Tree n) → Set
supp-condition false A T = FVTy A ≡ full
supp-condition true ⋆ T = ⊥
supp-condition true (s ─⟨ A ⟩⟶ t) T = NonZero′ (tree-dim T) × FVTy A ∪ FVTm s ≡ supp-bd (pred (tree-dim T)) T false × FVTy A ∪ FVTm t ≡ supp-bd (pred (tree-dim T)) T true

suspSuppBd : (d : ℕ) → (T : Tree n) → (b : Bool) → suspSupp (supp-bd d T b) ≡ supp-bd (suc d) (suspTree T) b
suspSuppBd zero T false = refl
suspSuppBd zero T true = refl
suspSuppBd (suc d) Sing b = refl
suspSuppBd (suc d) (Join S T) b = refl

lookup-isVar : (xs : VarSet n) → (t : Tm n) → .⦃ isVar t ⦄ → Bool
lookup-isVar (x ∷ xs) (Var zero) = x
lookup-isVar (x ∷ xs) (Var (suc i)) = lookup-isVar xs (Var i)

_⊆_ : VarSet n → VarSet n → Set
xs ⊆ ys = ys ≡ ys ∪ xs

infix 4 _≡ᵖ_
_≡ᵖ_ : VarSet n → VarSet m → Set
_≡ᵖ_ = Pointwise _≡_

FVTmTy : Ctx n → Tm n → VarSet n
FVTmTy Γ t = FVTy (tm-to-ty Γ t) ∪ FVTm t

DC : (Γ : Ctx n) → VarSet n → VarSet n
DC ∅ xs = emp
DC (Γ , A) (ewf xs) = ewf (DC Γ xs)
DC (Γ , A) (ewt xs) = ewt (DC Γ (xs ∪ FVTy A))

SuppTm : (Γ : Ctx n) → (t : Tm n) → VarSet n
SuppTm Γ t = DC Γ (FVTm t)

SuppTy : (Γ : Ctx n) → (A : Ty n) → VarSet n
SuppTy Γ A = DC Γ (FVTy A)

SuppSub : (Γ : Ctx n) → (σ : Sub m n A) → VarSet n
SuppSub Γ σ = DC Γ (FVSub σ)

⊥-elim′ : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim′ ()

pdb-bd-supp : (n : ℕ) → (Γ : Ctx m) → .(pdb : Γ ⊢pdb) → (b : Bool) → VarSet m
pdb-bd-supp n ∅ pdb b = let
  .x : ⊥
  x = (pdb-odd-length pdb)
  in ⊥-elim′ x
pdb-bd-supp n (∅ , A) pdb b = ewt emp
pdb-bd-supp n (Γ , B , A) pdb b = tri-cases (<-cmp n (ty-dim B))
                                            (ewf (ewf (pdb-bd-supp n Γ (pdb-prefix pdb) b)))
                                            (ewf (if b then ewt (drop (pdb-bd-supp n Γ (pdb-prefix pdb) b)) else (ewf (pdb-bd-supp n Γ (pdb-prefix pdb) b))))
                                            (ewt (ewt (pdb-bd-supp n Γ (pdb-prefix pdb) b)))

pd-bd-supp : (n : ℕ) → (Γ : Ctx m) → (pd : Γ ⊢pd) → (b : Bool) → VarSet m
pd-bd-supp n Γ pd b = pdb-bd-supp n Γ (pd-to-pdb pd) b
