{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Support where

open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec hiding (drop ; [_])
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Catt.Syntax
open import Catt.Syntax.Properties
-- open import Catt.Dimension
open import Data.Bool
open import Data.Fin using (Fin;zero;suc;fromℕ)
open import Data.Empty
open import Data.Unit
open import Catt.Globular
open import Catt.Variables
open import Catt.Tree
open import Catt.Tree.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Suspension
open import Catt.Dimension

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
drop {zero} [] = []
drop {suc n} (x ∷ v) = false ∷ v

trueAt : Fin n → VarSet n
trueAt {n = suc n} zero = ewt empty
trueAt {n = suc n} (suc i) = ewf (trueAt i)

infixl 60 _∪_
_∪_ : VarSet n → VarSet n → VarSet n
(f ∪ g) = zipWith _∨_ f g

Supp : (x : CtxSyntax n) → VarSet n
Supp = ≺-rec (λ {n} _ → VarSet n) r
  where
    r : (x : CtxSyntax n) → (∀ {m} → (y : CtxSyntax m) → y ≺ x → VarSet m) → VarSet n
    r (CtxTm (Var zero) (Γ , A)) rec = ewt (rec (CtxTy A Γ) Tm1)
    r (CtxTm (Var (suc i)) (Γ , A)) rec = ewf (rec (CtxTm (Var i) Γ) Tm2)
    r (CtxTm (Coh S A σ) Γ) rec = rec (CtxSub σ Γ) Tm4
    r (CtxTy ⋆ Γ) rec = empty
    r (CtxTy (s ─⟨ A ⟩⟶ t) Γ) rec = rec (CtxTy A Γ) Ty2 ∪ rec (CtxTm s Γ) Ty1 ∪ rec (CtxTm t Γ) Ty3
    r (CtxSub ⟨⟩ Γ) rec = rec (CtxTy _ Γ) Sub1
    r (CtxSub ⟨ σ , t ⟩ Γ) rec = (rec (CtxSub σ Γ) Sub2) ∪ (rec (CtxTm t Γ) Sub3)

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

TransportVarSet : VarSet n → Sub n m ⋆ → VarSet m
TransportVarSet xs ⟨⟩ = empty
TransportVarSet (ewf xs) ⟨ σ , t ⟩ = TransportVarSet xs σ
TransportVarSet (ewt xs) ⟨ σ , t ⟩ = TransportVarSet xs σ ∪ FVTm t

connect-supp : VarSet (suc n) → VarSet (suc m) → VarSet (suc (m + n))
connect-supp xs (x ∷ emp) = xs
connect-supp xs (x ∷ y ∷ ys) = x ∷ connect-supp xs (y ∷ ys)

suspSupp : VarSet n → VarSet (2 + n)
suspSupp [] = full
suspSupp (x ∷ vs) = x ∷ suspSupp vs

supp-bd : (d : ℕ) → (T : Tree n) → (b : Bool) → VarSet (suc n)
supp-bd zero T false = trueAt (fromℕ _)
supp-bd zero T true = trueAt (getVarFin (tree-last-var T) ⦃ tree-last-var-is-var T ⦄)
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
