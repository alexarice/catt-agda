module Deprecated.Tree.Structured.Support where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Pasting
open import Catt.Tree.Structured
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Structured.Globular

open import Catt.Support
open import Catt.Support.Properties
open import Deprecated.Tree.Support

open import Algebra.Bundles
open import Algebra.Definitions

MVarSet : (X : MaybeTree n) → Set
MVarSet (someTree x) = TVarSet x
MVarSet (Other n) = VarSet n

infixl 25 _∪m_
_∪m_ : MVarSet X → MVarSet X → MVarSet X
_∪m_ {X = someTree x} xs ys = xs ∪t ys
_∪m_ {X = Other _} xs ys = xs ∪ ys

mEmp : {X : MaybeTree n} → MVarSet X
mEmp {X = someTree x} = tEmp
mEmp {X = Other _} = empty

mFull : {X : MaybeTree n} → MVarSet X
mFull {X = someTree S} = tFull
mFull {X = Other Γ} = full

∪m-left-unit : {X : MaybeTree n} → LeftIdentity _≡_ mEmp (_∪m_ {X = X})
∪m-left-unit {X = someTree x} = ∪t-left-unit
∪m-left-unit {X = Other _} = ∪-left-unit

∪m-right-unit : {X : MaybeTree n} → RightIdentity _≡_ mEmp (_∪m_ {X = X})
∪m-right-unit {X = someTree x} = ∪t-right-unit
∪m-right-unit {X = Other _} = ∪-right-unit

∪m-assoc : {X : MaybeTree n} → Associative _≡_ (_∪m_ {X = X})
∪m-assoc {X = someTree x} = ∪t-assoc
∪m-assoc {X = Other _} = ∪-assoc

∪m-comm : {X : MaybeTree n} → Commutative _≡_ (_∪m_ {X = X})
∪m-comm {X = someTree x} = ∪t-comm
∪m-comm {X = Other _} = ∪-comm

∪m-idem : {X : MaybeTree n} → Idempotent _≡_ (_∪m_ {X = X})
∪m-idem {X = someTree x} = ∪t-idem
∪m-idem {X = Other _} = ∪-idem

module _ {X : MaybeTree n} where

  open import Algebra.Definitions {A = MVarSet X} _≡_
  open import Algebra.Structures {A = MVarSet X} _≡_

  ∪m-isMagma : IsMagma (_∪m_)
  ∪m-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong = cong₂ _∪m_
    }

  ∪m-isSemigroup : IsSemigroup _∪m_
  ∪m-isSemigroup = record
    { isMagma = ∪m-isMagma
    ; assoc = ∪m-assoc
    }

  ∪m-isMonoid : IsMonoid _∪m_ mEmp
  ∪m-isMonoid = record
    { isSemigroup = ∪m-isSemigroup
    ; identity = ∪m-left-unit ,, ∪m-right-unit
    }

  ∪m-monoid : Monoid _ _
  ∪m-monoid = record
    { isMonoid = ∪m-isMonoid }

  ∪m-isCommutativeMonoid : IsCommutativeMonoid _∪m_ mEmp
  ∪m-isCommutativeMonoid = record
    { isMonoid = ∪m-isMonoid
    ; comm = ∪m-comm
    }

  ∪m-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _∪m_ mEmp
  ∪m-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ∪m-isCommutativeMonoid
    ; idem = ∪m-idem
    }

  ∪m-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  ∪m-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = ∪m-isIdempotentCommutativeMonoid }

DCM : (ΓS : CtxOrTree n) → (xs : MVarSet (COT-to-MT ΓS)) → MVarSet (COT-to-MT ΓS)
DCM (incTree S) xs = DCT xs
DCM (incCtx Γ) xs = DC Γ xs

FVSTm : {X : MaybeTree n} → STm X → MVarSet X
FVLabel : {X : MaybeTree n} → Label X S → MVarSet X
FVLabel′ : {X : MaybeTree n} → ((P : Path S) → MVarSet X) → MVarSet X
FVLabel-WT : {X : MaybeTree n} → Label-WT X S → MVarSet X
FVSTy : {X : MaybeTree n} → STy X → MVarSet X

FVSTm (SExt a) = VSJoin false (FVSTm a) tEmp
FVSTm (SShift a) = VSJoin false tEmp (FVSTm a)
FVSTm (SPath x) = fromPath x
FVSTm (SCoh S A L) = FVLabel-WT L
FVSTm (SOther t) = FVTm t

FVLabel L = FVLabel′ (λ P → FVSTm (L P))

FVLabel′ {S = Sing} f = f PHere
FVLabel′ {S = Join S T} f = f PHere ∪m FVLabel′ (f ∘ PExt) ∪m FVLabel′ (f ∘ PShift)

FVLabel-WT L = FVSTy (lty L) ∪m FVLabel (ap L)

FVSTy S⋆ = mEmp
FVSTy (SArr s A t) = FVSTy A ∪m FVSTm s ∪m FVSTm t

supp-condition-s : (b : Bool) → (S : Tree n) → (As : STy (someTree S)) → Set
supp-condition-s false S As = DCT (FVSTy As) ≡ mFull
supp-condition-s true S S⋆ = ⊥
supp-condition-s true S (SArr s As t) = NonZero (tree-dim S)
                                      × DCT (FVSTm s) ≡ tree-bd-vs (pred (tree-dim S)) S false
                                      × DCT (FVSTm t) ≡ tree-bd-vs (pred (tree-dim S)) S true

MtoVarSet : (ΓS : CtxOrTree n) → MVarSet (COT-to-MT ΓS) → VarSet n
MtoVarSet (incTree _) xs = toVarSet xs
MtoVarSet (incCtx Γ) xs = DC Γ xs


infixr 30 _[_]vl
_[_]vl : {ΓS : CtxOrTree n} → TVarSet S → (L : Label (COT-to-MT ΓS) S) → VarSet n
xs [ L ]vl = toVarSet xs [ label-to-sub (L ,, S⋆) ]vs
