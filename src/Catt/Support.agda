module Catt.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Data.Vec hiding (drop ; [_]; _>>=_) public
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Suspension
open import Relation.Nullary
open import Relation.Binary.Definitions
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Connection
open import Catt.Pasting
open import Catt.Tree.Pasting
open import Catt.Connection.Pasting
open import Catt.Variables

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

pdb-bd-supp : (n : ℕ) → (Γ : Ctx m) → .⦃ pdb : Γ ⊢pdb ⦄ → (b : Bool) → VarSet m
pdb-bd-supp n ∅ ⦃ pdb ⦄ b = ⊥-elim (pdb-odd-length pdb)
pdb-bd-supp n (∅ , A) b = ewt emp
pdb-bd-supp n (Γ , B , A) b = tri-cases (<-cmp n (ty-dim B))
                                            (ewf (ewf (pdb-bd-supp n Γ ⦃ pdb-prefix it ⦄ b)))
                                            (ewf (if b then ewt (drop (pdb-bd-supp n Γ ⦃ pdb-prefix it ⦄ b)) else (ewf (pdb-bd-supp n Γ ⦃ pdb-prefix it ⦄ b))))
                                            (ewt (ewt (pdb-bd-supp n Γ ⦃ pdb-prefix it ⦄ b)))

pd-bd-supp : (n : ℕ) → (Γ : Ctx m) → .⦃ pd : Γ ⊢pd ⦄ → (b : Bool) → VarSet m
pd-bd-supp n Γ b = pdb-bd-supp n Γ ⦃ pd-to-pdb it ⦄ b

TransportVarSet : VarSet n → Sub n m A → VarSet m
TransportVarSet xs ⟨⟩ = empty
TransportVarSet (ewf xs) ⟨ σ , t ⟩ = TransportVarSet xs σ
TransportVarSet (ewt xs) ⟨ σ , t ⟩ = TransportVarSet xs σ ∪ FVTm t

-- susp-supp-tree-bd : (d : ℕ) → (T : Tree n) → (b : Bool) → suspSupp (supp-tree-bd d T b) ≡ supp-tree-bd (suc d) (suspTree T) b
-- susp-supp-tree-bd zero T false = refl
-- susp-supp-tree-bd zero T true = refl
-- susp-supp-tree-bd (suc d) Sing b = refl
-- susp-supp-tree-bd (suc d) (Join S T) b = refl

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

is-DC : (Γ : Ctx n) → (xs : VarSet n) → Set
is-DC ∅ emp = ⊤
is-DC (Γ , A) (ewf xs) = is-DC Γ xs
is-DC (Γ , A) (ewt xs) = is-DC Γ xs × (FVTy A ⊆ xs)

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

supp-condition : (b : Bool) → (A : Ty (suc n)) → (Γ : Ctx (suc n)) → .⦃ pd : Γ ⊢pd ⦄ → Set
supp-condition false A Γ = SuppTy Γ A ≡ full
supp-condition true ⋆ Γ = ⊥
supp-condition true (s ─⟨ A ⟩⟶ t) Γ = NonZero (ctx-dim Γ) × SuppTm Γ s ≡ pd-bd-supp (pred (ctx-dim Γ)) Γ false × SuppTm Γ t ≡ pd-bd-supp (pred (ctx-dim Γ)) Γ true
