module Catt.Tree.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Boundary
open import Catt.Tree.Properties
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Path
open import Catt.Connection.Support
open import Catt.Suspension.Support
open import Catt.Suspension.Pasting
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Variables
open import Catt.Suspension
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using ()
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Tree.Pasting
open import Relation.Binary.Definitions
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Connection.Support
open import Catt.Connection.Pasting
open import Algebra.Definitions
open import Algebra.Bundles

open ≡-Reasoning

data TVarSet : (T : Tree n) → Set
data TVarSet′ : (T : Tree n) → Set

data TVarSet where
  VSHere : TVarSet′ S → TVarSet S
  VSNotHere : TVarSet T → TVarSet (Join S T)

data TVarSet′ where
  VSEmp : TVarSet′ S
  VSExt : (xs : TVarSet S) → (ys : TVarSet′ T) → TVarSet′ (Join S T)
  VSShift : (ys : TVarSet T) → TVarSet′ (Join S T)

tFull : TVarSet S
tFull′ : TVarSet′ S

tFull {S = S} = VSHere tFull′

tFull′ {S = Sing} = VSEmp
tFull′ {S = Join S T} = VSExt tFull tFull′

strip : TVarSet S → TVarSet′ S
strip (VSHere xs) = xs
strip (VSNotHere xs) = VSShift xs

_∪t_ : TVarSet S → TVarSet S → TVarSet S
_∪t′_ : TVarSet′ S → TVarSet′ S → TVarSet′ S

VSHere xs ∪t ys = VSHere (xs ∪t′ strip ys)
VSNotHere xs ∪t VSHere ys = VSHere (VSShift xs ∪t′ ys)
VSNotHere xs ∪t VSNotHere ys = VSNotHere (xs ∪t ys)

VSEmp ∪t′ ys = ys
VSExt xs ys ∪t′ VSEmp = VSExt xs ys
VSExt xs ys ∪t′ VSExt xs′ ys′ = VSExt (xs ∪t xs′) (ys ∪t′ ys′)
VSExt xs ys ∪t′ VSShift ys′ = VSExt xs (ys ∪t′ strip ys′)
VSShift ys ∪t′ VSEmp = VSShift ys
VSShift ys ∪t′ VSExt xs′ ys′ = VSExt xs′ (strip ys ∪t′ ys′)
VSShift ys ∪t′ VSShift ys′ = VSShift (ys ∪t ys′)

∪t′-left-unit : LeftIdentity _≡_ VSEmp (_∪t′_ {S = S})
∪t′-left-unit xs = refl

∪t′-right-unit : RightIdentity _≡_ VSEmp (_∪t′_ {S = S})
∪t′-right-unit VSEmp = refl
∪t′-right-unit (VSExt xs xs₁) = refl
∪t′-right-unit (VSShift ys) = refl

∪t-left-zero : LeftZero _≡_ tFull (_∪t_ {S = S})
∪t′-left-zero : LeftZero _≡_ tFull′ (_∪t′_ {S = S})

∪t-left-zero (VSHere xs) = cong VSHere (∪t′-left-zero xs)
∪t-left-zero (VSNotHere xs) = cong VSHere (cong (VSExt tFull) (∪t′-left-zero (strip xs)))

∪t′-left-zero VSEmp = ∪t′-right-unit tFull′
∪t′-left-zero (VSExt xs ys) = cong₂ VSExt (∪t-left-zero xs) (∪t′-left-zero ys)
∪t′-left-zero (VSShift ys) = cong (VSExt tFull) (∪t′-left-zero (strip ys))

∪t-right-zero : RightZero _≡_ tFull (_∪t_ {S = S})
∪t′-right-zero : RightZero _≡_ tFull′ (_∪t′_ {S = S})

∪t-right-zero (VSHere xs) = cong VSHere (∪t′-right-zero xs)
∪t-right-zero (VSNotHere xs) = cong VSHere (cong (VSExt tFull) (∪t′-right-zero (strip xs)))

∪t′-right-zero VSEmp = refl
∪t′-right-zero (VSExt xs ys) = cong₂ VSExt (∪t-right-zero xs) (∪t′-right-zero ys)
∪t′-right-zero (VSShift ys) = cong (VSExt tFull) (∪t′-right-zero (strip ys))

strip-lem : (xs ys : TVarSet S) → strip xs ∪t′ strip ys ≡ strip (xs ∪t ys)
strip-lem (VSHere x) ys = refl
strip-lem (VSNotHere xs) (VSHere x) = refl
strip-lem (VSNotHere xs) (VSNotHere ys) = refl

∪t-assoc : Associative _≡_ (_∪t_ {S = S})
∪t′-assoc : Associative _≡_ (_∪t′_ {S = S})

∪t-assoc (VSHere x) ys zs = cong VSHere (begin
  (x ∪t′ strip ys) ∪t′ strip zs
    ≡⟨ ∪t′-assoc x (strip ys) (strip zs) ⟩
  x ∪t′ (strip ys ∪t′ strip zs)
    ≡⟨ cong (x ∪t′_) (strip-lem ys zs) ⟩
  x ∪t′ strip (ys ∪t zs) ∎)
∪t-assoc (VSNotHere xs) (VSHere y) zs = cong VSHere (∪t′-assoc (VSShift xs) y (strip zs))
∪t-assoc (VSNotHere xs) (VSNotHere ys) (VSHere x) = cong VSHere (∪t′-assoc (VSShift xs) (VSShift ys) x)
∪t-assoc (VSNotHere xs) (VSNotHere ys) (VSNotHere zs) = cong VSNotHere (∪t-assoc xs ys zs)

∪t′-assoc VSEmp ys zs = refl
∪t′-assoc (VSExt xs xs′) VSEmp zs = refl
∪t′-assoc (VSExt xs xs′) (VSExt ys ys′) VSEmp = refl
∪t′-assoc (VSExt xs xs′) (VSExt ys ys′) (VSExt zs zs′) = cong₂ VSExt (∪t-assoc xs ys zs) (∪t′-assoc xs′ ys′ zs′)
∪t′-assoc (VSExt xs xs′) (VSExt ys ys′) (VSShift zs) = cong (VSExt (xs ∪t ys)) (∪t′-assoc xs′ ys′ (strip zs))
∪t′-assoc (VSExt xs xs′) (VSShift ys) VSEmp = refl
∪t′-assoc (VSExt xs xs′) (VSShift ys) (VSExt zs zs′) = cong (VSExt (xs ∪t zs)) (∪t′-assoc xs′ (strip ys) zs′)
∪t′-assoc (VSExt xs xs′) (VSShift ys) (VSShift zs) = cong (VSExt xs) (begin
  (xs′ ∪t′ strip ys) ∪t′ strip zs
    ≡⟨ ∪t′-assoc xs′ (strip ys) (strip zs) ⟩
  xs′ ∪t′ (strip ys ∪t′ strip zs)
    ≡⟨ cong (xs′ ∪t′_) (strip-lem ys zs) ⟩
  xs′ ∪t′ strip (ys ∪t zs) ∎)
∪t′-assoc (VSShift xs) VSEmp zs = refl
∪t′-assoc (VSShift xs) (VSExt ys ys′) VSEmp = refl
∪t′-assoc (VSShift xs) (VSExt ys ys′) (VSExt zs zs′) = cong (VSExt (ys ∪t zs)) (∪t′-assoc (strip xs) ys′ zs′)
∪t′-assoc (VSShift xs) (VSExt ys ys′) (VSShift zs) = cong (VSExt ys) (∪t′-assoc (strip xs) ys′ (strip zs))
∪t′-assoc (VSShift xs) (VSShift ys) VSEmp = refl
∪t′-assoc (VSShift xs) (VSShift ys) (VSExt zs zs′) = cong (VSExt zs) (begin
  strip (xs ∪t ys) ∪t′ zs′
    ≡˘⟨ cong (_∪t′ zs′) (strip-lem xs ys) ⟩
  (strip xs ∪t′ strip ys) ∪t′ zs′
    ≡⟨ ∪t′-assoc (strip xs) (strip ys) zs′ ⟩
  strip xs ∪t′ (strip ys ∪t′ zs′) ∎)
∪t′-assoc (VSShift xs) (VSShift ys) (VSShift zs) = cong VSShift (∪t-assoc xs ys zs)

∪t-comm : Commutative _≡_ (_∪t_ {S = S})
∪t′-comm : Commutative _≡_ (_∪t′_ {S = S})

∪t-comm (VSHere x) (VSHere y) = cong VSHere (∪t′-comm x y)
∪t-comm (VSHere x) (VSNotHere ys) = cong VSHere (∪t′-comm x (VSShift ys))
∪t-comm (VSNotHere xs) (VSHere y) = cong VSHere (∪t′-comm (VSShift xs) y)
∪t-comm (VSNotHere xs) (VSNotHere ys) = cong VSNotHere (∪t-comm xs ys)

∪t′-comm VSEmp ys = sym (∪t′-right-unit ys)
∪t′-comm (VSExt xs xs′) VSEmp = refl
∪t′-comm (VSExt xs xs′) (VSExt ys ys′) = cong₂ VSExt (∪t-comm xs ys) (∪t′-comm xs′ ys′)
∪t′-comm (VSExt xs xs′) (VSShift ys) = cong (VSExt xs) (∪t′-comm xs′ (strip ys))
∪t′-comm (VSShift xs) VSEmp = refl
∪t′-comm (VSShift xs) (VSExt ys ys′) = cong (VSExt ys) (∪t′-comm (strip xs) ys′)
∪t′-comm (VSShift xs) (VSShift ys) = cong VSShift (∪t-comm xs ys)

∪t-idem : Idempotent _≡_ (_∪t_ {S = S})
∪t′-idem : Idempotent _≡_ (_∪t′_ {S = S})

∪t-idem (VSHere x) = cong VSHere (∪t′-idem x)
∪t-idem (VSNotHere xs) = cong VSNotHere (∪t-idem xs)

∪t′-idem VSEmp = refl
∪t′-idem (VSExt xs ys) = cong₂ VSExt (∪t-idem xs) (∪t′-idem ys)
∪t′-idem (VSShift ys) = cong VSShift (∪t-idem ys)

{-
data TVarSet : (T : Tree n) → Set where
  VSSing : (b : Bool) → TVarSet Sing
  VSJoin : Maybe (TVarSet S) → TVarSet T → TVarSet (Join S T)

tEmp : TVarSet S
tEmp {S = Sing} = VSSing false
tEmp {S = Join S T} = VSJoin nothing tEmp

tFull : TVarSet S
tFull {S = Sing} = VSSing true
tFull {S = Join S T} = VSJoin (just tFull) tFull

infixl 60 _∪t_
_∪t_ : TVarSet S → TVarSet S → TVarSet S
merge : Maybe (TVarSet S) → Maybe (TVarSet S) → Maybe (TVarSet S)

VSSing b ∪t VSSing b′ = VSSing (b ∨ b′)
VSJoin x xs ∪t VSJoin x′ ys = VSJoin (merge x x′) (xs ∪t ys)

merge (just x) y = just (x ∪t fromMaybe tEmp y)
merge nothing y = y

∪t-left-unit : LeftIdentity _≡_ tEmp (_∪t_ {S = S})
∪t-left-unit (VSSing b) = refl
∪t-left-unit (VSJoin x xs) = cong (VSJoin x) (∪t-left-unit xs)

∪t-right-unit : RightIdentity _≡_ tEmp (_∪t_ {S = S})
merge-right-unit : RightIdentity _≡_ nothing (merge {S = S})

∪t-right-unit (VSSing b) = cong VSSing (∨-identityʳ b)
∪t-right-unit (VSJoin x xs) = cong₂ VSJoin (merge-right-unit x) (∪t-right-unit xs)

merge-right-unit (just x) = cong just (∪t-right-unit x)
merge-right-unit nothing = refl

∪t-left-zero : LeftZero _≡_ tFull (_∪t_ {S = S})
∪t-left-zero (VSSing b) = refl
∪t-left-zero (VSJoin x xs) = cong₂ VSJoin (cong just (∪t-left-zero (fromMaybe tEmp x))) (∪t-left-zero xs)

∪t-right-zero : RightZero _≡_ tFull (_∪t_ {S = S})
merge-right-zero : RightZero _≡_ (just tFull) (merge {S = S})

∪t-right-zero (VSSing b) = cong VSSing (∨-zeroʳ b)
∪t-right-zero (VSJoin x xs) = cong₂ VSJoin (merge-right-zero x) (∪t-right-zero xs)

merge-right-zero (just x) = cong just (∪t-right-zero x)
merge-right-zero nothing = refl

∪t-assoc : Associative _≡_ (_∪t_ {S = S})
merge-assoc : Associative _≡_ (merge {S = S})

∪t-assoc (VSSing b) (VSSing b′) (VSSing b″) = cong VSSing (∨-assoc b b′ b″)
∪t-assoc (VSJoin x xs) (VSJoin x′ ys) (VSJoin x″ zs) = cong₂ VSJoin (merge-assoc x x′ x″) (∪t-assoc xs ys zs)

merge-assoc (just x) (just y) z = cong just (∪t-assoc x (fromMaybe tEmp (just y)) (fromMaybe tEmp z))
merge-assoc (just x) nothing z = cong (λ - → just (- ∪t fromMaybe tEmp z)) (∪t-right-unit x)
merge-assoc nothing y z = refl

∪t-comm : Commutative _≡_ (_∪t_ {S = S})
merge-comm : Commutative _≡_ (merge {S = S})

∪t-comm (VSSing b) (VSSing b′) = cong VSSing (∨-comm b b′)
∪t-comm (VSJoin x xs) (VSJoin x′ ys) = cong₂ VSJoin (merge-comm x x′) (∪t-comm xs ys)

merge-comm (just x) (just y) = cong just (∪t-comm x y)
merge-comm (just x) nothing = cong just (∪t-right-unit x)
merge-comm nothing (just x) = sym (cong just (∪t-right-unit x))
merge-comm nothing nothing = refl

∪t-idem : Idempotent _≡_ (_∪t_ {S = S})
merge-idem : Idempotent _≡_ (merge {S = S})

∪t-idem (VSSing b) = cong VSSing (∨-idem b)
∪t-idem (VSJoin x xs) = cong₂ VSJoin (merge-idem x) (∪t-idem xs)

merge-idem (just x) = cong just (∪t-idem x)
merge-idem nothing = refl

module _ {S : Tree n} where

  open import Algebra.Definitions {A = TVarSet S} _≡_
  open import Algebra.Structures {A = TVarSet S} _≡_

  ∪t-isMagma : IsMagma (_∪t_)
  ∪t-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong = cong₂ _∪t_
    }

  ∪t-isSemigroup : IsSemigroup _∪t_
  ∪t-isSemigroup = record
    { isMagma = ∪t-isMagma
    ; assoc = ∪t-assoc
    }

  ∪t-isMonoid : IsMonoid _∪t_ tEmp
  ∪t-isMonoid = record
    { isSemigroup = ∪t-isSemigroup
    ; identity = ∪t-left-unit ,, ∪t-right-unit
    }

  ∪t-isCommutativeMonoid : IsCommutativeMonoid _∪t_ tEmp
  ∪t-isCommutativeMonoid = record
    { isMonoid = ∪t-isMonoid
    ; comm = ∪t-comm
    }

  ∪t-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _∪t_ tEmp
  ∪t-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ∪t-isCommutativeMonoid
    ; idem = ∪t-idem
    }

  ∪t-monoid : Monoid _ _
  ∪t-monoid = record
    { isMonoid = ∪t-isMonoid }

  ∪t-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  ∪t-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = ∪t-isIdempotentCommutativeMonoid }

-}


fromPath : (P : Path S) → TVarSet S
fromPath PHere = VSHere VSEmp
fromPath (PExt P) = VSHere (VSExt (fromPath P) VSEmp)
fromPath (PShift P) = VSNotHere (fromPath P)

toVarSet : TVarSet S → VarSet (suc (tree-size S))
toVarSet′ : TVarSet′ S → VarSet (suc (tree-size S))

toVarSet (VSHere x) = trueAt (fromℕ _) ∪ toVarSet′ x
toVarSet (VSNotHere xs) = connect-susp-supp empty (toVarSet xs)

toVarSet′ VSEmp = empty
toVarSet′ (VSExt xs ys) = connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet′ ys)
toVarSet′ (VSShift ys) = connect-susp-supp empty (toVarSet ys)
{-
toVarSet-emp : (S : Tree n) → toVarSet (tEmp {S = S}) ≡ empty {n = suc n}
toVarSet-emp Sing = refl
toVarSet-emp (Join S T) = begin
  connect-susp-supp empty (toVarSet (tEmp {S = T}))
    ≡⟨ cong (connect-susp-supp empty) (toVarSet-emp T) ⟩
  connect-susp-supp empty empty
    ≡⟨ connect-supp-empty _ get-snd (tree-size T) ⟩
  empty ∎
  where
    open ≡-Reasoning

toVarSet-full : (S : Tree n) → toVarSet (tFull {S = S}) ≡ full {n = suc n}
toVarSet-full Sing = refl
toVarSet-full (Join S T) = begin
  connect-susp-supp (suspSupp (toVarSet (tFull {S = S}))) (toVarSet (tFull {S = T}))
    ≡⟨ cong₂ connect-susp-supp (cong suspSupp (toVarSet-full S)) (toVarSet-full T) ⟩
  connect-susp-supp (suspSupp full) full
    ≡⟨ cong (λ - → connect-susp-supp - full) suspSuppFull ⟩
  connect-susp-supp full full
    ≡⟨ connect-supp-full (2 + tree-size S) get-snd (tree-size T) ⟩
  full ∎
  where
    open ≡-Reasoning
-}

toVarSet-∪t : (xs ys : TVarSet S) → toVarSet (xs ∪t ys) ≡ toVarSet xs ∪ toVarSet ys
toVarSet-∪t′ : (xs ys : TVarSet′ S) → toVarSet′ (xs ∪t′ ys) ≡ toVarSet′ xs ∪ toVarSet′ ys
toVarSet-strip : (xs : TVarSet S) → trueAt (fromℕ _) ∪ toVarSet′ (strip xs) ≡ trueAt (fromℕ _) ∪ toVarSet xs

toVarSet-∪t (VSHere x) ys = begin
  trueAt (fromℕ _) ∪ toVarSet′ (x ∪t′ strip ys)
    ≡⟨ cong (trueAt (fromℕ _) ∪_) (toVarSet-∪t′ x (strip ys)) ⟩
  trueAt (fromℕ _) ∪ (toVarSet′ x ∪ toVarSet′ (strip ys))
    ≡⟨ prove 3 (var 0F ⊕ (var 1F ⊕ var 2F)) (var 1F ⊕ (var 0F ⊕ var 2F)) (_ ∷ _ ∷ _ ∷ emp) ⟩
  toVarSet′ x ∪ (trueAt (fromℕ _) ∪ toVarSet′ (strip ys))
    ≡⟨ cong (toVarSet′ x ∪_) (toVarSet-strip ys) ⟩
  toVarSet′ x ∪ (trueAt (fromℕ _) ∪ toVarSet ys)
    ≡⟨ prove 3 (var 0F ⊕ (var 1F ⊕ var 2F)) ((var 1F ⊕ var 0F) ⊕ var 2F) (_ ∷ _ ∷ _ ∷ emp) ⟩
  trueAt (fromℕ _) ∪ toVarSet′ x ∪ toVarSet ys ∎
  where
    open Solver ∪-idempotentCommutativeMonoid
toVarSet-∪t (VSNotHere xs) (VSHere x) = begin
  trueAt (fromℕ _) ∪ toVarSet′ (VSShift xs ∪t′ x)
    ≡⟨ cong (trueAt (fromℕ _) ∪_) (toVarSet-∪t′ (VSShift xs) x) ⟩
  trueAt (fromℕ _) ∪ (connect-susp-supp empty (toVarSet xs) ∪ toVarSet′ x)
    ≡⟨ prove 3 (var 0F ⊕ (var 1F ⊕ var 2F)) (var 1F ⊕ (var 0F ⊕ var 2F)) (_ ∷ _ ∷ _ ∷ emp) ⟩
  connect-susp-supp empty (toVarSet xs) ∪ (trueAt (fromℕ _) ∪ toVarSet′ x) ∎
  where
    open Solver ∪-idempotentCommutativeMonoid hiding (empty)
toVarSet-∪t (VSNotHere xs) (VSNotHere ys) = begin
  connect-susp-supp empty (toVarSet (xs ∪t ys))
    ≡⟨ cong₂ connect-susp-supp (sym (∪-idem empty)) (toVarSet-∪t xs ys) ⟩
  connect-susp-supp (empty ∪ empty) (toVarSet xs ∪ toVarSet ys)
    ≡⟨ connect-supp-∪ empty empty (toVarSet xs) (toVarSet ys) get-snd ⟩
  connect-susp-supp empty (toVarSet xs) ∪ connect-susp-supp empty (toVarSet ys) ∎

toVarSet-∪t′ VSEmp ys = sym (∪-left-unit (toVarSet′ ys))
toVarSet-∪t′ (VSExt xs xs′) VSEmp = sym (∪-right-unit (toVarSet′ (VSExt xs xs′)))
toVarSet-∪t′ (VSExt xs xs′) (VSExt ys ys′) = begin
  connect-susp-supp (suspSupp (toVarSet (xs ∪t ys)))
      (toVarSet′ (xs′ ∪t′ ys′))
    ≡⟨ cong₂ connect-susp-supp (cong suspSupp (toVarSet-∪t xs ys)) (toVarSet-∪t′ xs′ ys′) ⟩
  connect-susp-supp (suspSupp (toVarSet xs ∪ toVarSet ys)) (toVarSet′ xs′ ∪ toVarSet′ ys′)
    ≡⟨ cong (λ - → connect-susp-supp - _) (suspSupp-∪ (toVarSet xs) (toVarSet ys)) ⟩
  connect-susp-supp (suspSupp (toVarSet xs) ∪ suspSupp (toVarSet ys)) (toVarSet′ xs′ ∪ toVarSet′ ys′)
    ≡⟨ connect-supp-∪ (suspSupp (toVarSet xs)) (suspSupp (toVarSet ys)) (toVarSet′ xs′) (toVarSet′ ys′) get-snd ⟩
  connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet′ xs′) ∪
      connect-susp-supp (suspSupp (toVarSet ys)) (toVarSet′ ys′) ∎
toVarSet-∪t′ (VSExt xs xs′) (VSShift ys) = begin
  connect-susp-supp (suspSupp (toVarSet xs))
      (toVarSet′ (xs′ ∪t′ strip ys))
    ≡⟨ connect-susp-supp-lem (toVarSet xs) (toVarSet′ (xs′ ∪t′ strip ys)) ⟩
  connect-susp-supp (suspSupp (toVarSet xs))
    (trueAt (fromℕ _) ∪ toVarSet′ (xs′ ∪t′ strip ys))
    ≡⟨ cong (connect-susp-supp (suspSupp (toVarSet xs))) lem ⟩
  connect-susp-supp (suspSupp (toVarSet xs)) (trueAt (fromℕ _) ∪ (toVarSet′ xs′ ∪ toVarSet ys))
    ≡˘⟨ connect-susp-supp-lem (toVarSet xs) (toVarSet′ xs′ ∪ toVarSet ys) ⟩
  connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet′ xs′ ∪ toVarSet ys)
    ≡˘⟨ cong (λ - → connect-susp-supp - _) (∪-right-unit (suspSupp (toVarSet xs))) ⟩
  connect-susp-supp (suspSupp (toVarSet xs) ∪ empty) (toVarSet′ xs′ ∪ toVarSet ys)
    ≡⟨ connect-supp-∪ (suspSupp (toVarSet xs)) empty (toVarSet′ xs′) (toVarSet ys) get-snd ⟩
  connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet′ xs′) ∪
      connect-susp-supp empty (toVarSet ys) ∎
  where
    lem : trueAt (fromℕ _) ∪ toVarSet′ (xs′ ∪t′ strip ys) ≡
            trueAt (fromℕ _) ∪ (toVarSet′ xs′ ∪ toVarSet ys)
    lem = begin
      trueAt (fromℕ _) ∪ toVarSet′ (xs′ ∪t′ strip ys)
        ≡⟨ cong (trueAt (fromℕ _) ∪_) (toVarSet-∪t′ xs′ (strip ys)) ⟩
      trueAt (fromℕ _) ∪ (toVarSet′ xs′ ∪ toVarSet′ (strip ys))
        ≡⟨ prove 3 (var 0F ⊕ (var 1F ⊕ var 2F)) (var 1F ⊕ (var 0F ⊕ var 2F)) (_ ∷ _ ∷ _ ∷ emp) ⟩
      toVarSet′ xs′ ∪ (trueAt (fromℕ _) ∪ toVarSet′ (strip ys))
        ≡⟨ cong (toVarSet′ xs′ ∪_) (toVarSet-strip ys) ⟩
      toVarSet′ xs′ ∪ (trueAt (fromℕ _) ∪ toVarSet ys)
        ≡⟨ prove 3 (var 0F ⊕ (var 1F ⊕ var 2F)) (var 1F ⊕ (var 0F ⊕ var 2F)) (_ ∷ _ ∷ _ ∷ emp) ⟩
      trueAt (fromℕ _) ∪ (toVarSet′ xs′ ∪ toVarSet ys) ∎
      where
        open Solver ∪-idempotentCommutativeMonoid
toVarSet-∪t′ (VSShift xs) VSEmp = sym (∪-right-unit (connect-susp-supp empty (toVarSet xs)))
toVarSet-∪t′ (VSShift xs) (VSExt ys ys′) = begin
  connect-susp-supp (suspSupp (toVarSet ys)) (toVarSet′ (strip xs ∪t′ ys′))
    ≡⟨ connect-susp-supp-lem (toVarSet ys) (toVarSet′ (strip xs ∪t′ ys′)) ⟩
  connect-susp-supp (suspSupp (toVarSet ys)) (trueAt (fromℕ _) ∪ toVarSet′ (strip xs ∪t′ ys′))
    ≡⟨ cong (connect-susp-supp (suspSupp (toVarSet ys))) lem ⟩
  connect-susp-supp (suspSupp (toVarSet ys)) (trueAt (fromℕ _) ∪ (toVarSet xs ∪ toVarSet′ ys′))
    ≡˘⟨ connect-susp-supp-lem (toVarSet ys) (toVarSet xs ∪ toVarSet′ ys′) ⟩
  connect-susp-supp (suspSupp (toVarSet ys)) (toVarSet xs ∪ toVarSet′ ys′)
    ≡˘⟨ cong (λ - → connect-susp-supp - _) (∪-left-unit (suspSupp (toVarSet ys))) ⟩
  connect-susp-supp (empty ∪ suspSupp (toVarSet ys)) (toVarSet xs ∪ toVarSet′ ys′)
    ≡⟨ connect-supp-∪ empty (suspSupp (toVarSet ys)) (toVarSet xs) (toVarSet′ ys′) get-snd ⟩
  connect-susp-supp empty (toVarSet xs) ∪ connect-susp-supp (suspSupp (toVarSet ys)) (toVarSet′ ys′) ∎
  where
    lem : trueAt (fromℕ _) ∪ toVarSet′ (strip xs ∪t′ ys′) ≡
            trueAt (fromℕ _) ∪ (toVarSet xs ∪ toVarSet′ ys′)
    lem = begin
      trueAt (fromℕ _) ∪ toVarSet′ (strip xs ∪t′ ys′)
        ≡⟨ cong (trueAt (fromℕ _) ∪_) (toVarSet-∪t′ (strip xs) ys′) ⟩
      trueAt (fromℕ _) ∪ (toVarSet′ (strip xs) ∪ toVarSet′ ys′)
        ≡˘⟨ ∪-assoc (trueAt (fromℕ _)) (toVarSet′ (strip xs)) (toVarSet′ ys′) ⟩
      trueAt (fromℕ _) ∪ toVarSet′ (strip xs) ∪ toVarSet′ ys′
        ≡⟨ cong (_∪ toVarSet′ ys′) (toVarSet-strip xs) ⟩
      trueAt (fromℕ _) ∪ toVarSet xs ∪ toVarSet′ ys′
        ≡⟨ ∪-assoc (trueAt (fromℕ _)) (toVarSet xs) (toVarSet′ ys′) ⟩
      trueAt (fromℕ _) ∪ (toVarSet xs ∪ toVarSet′ ys′) ∎
toVarSet-∪t′ (VSShift xs) (VSShift ys) = begin
  connect-susp-supp empty (toVarSet (xs ∪t ys))
    ≡⟨ cong₂ connect-susp-supp (sym (∪-idem empty)) (toVarSet-∪t xs ys) ⟩
  connect-susp-supp (empty ∪ empty) (toVarSet xs ∪ toVarSet ys)
    ≡⟨ connect-supp-∪ empty empty (toVarSet xs) (toVarSet ys) get-snd ⟩
  connect-susp-supp empty (toVarSet xs) ∪ connect-susp-supp empty (toVarSet ys) ∎


toVarSet-strip (VSHere x)
  = prove 2 (var 0F ⊕ var 1F) (var 0F ⊕ (var 0F ⊕ var 1F)) (_ ∷ _ ∷ emp)
  where
    open Solver ∪-idempotentCommutativeMonoid
toVarSet-strip (VSNotHere xs) = refl

fromPath-PHere : (S : Tree n) → toVarSet (fromPath (PHere {S = S})) ≡ trueAt (fromℕ _)
fromPath-PHere T = ∪-right-unit (trueAt (fromℕ _))

fromPath-last-path : (S : Tree n) → toVarSet (fromPath (last-path S)) ≡ FVTm (tree-last-var S)
fromPath-last-path Sing = refl
fromPath-last-path (Join S T) = begin
  connect-susp-supp empty (toVarSet (fromPath (last-path T)))
    ≡˘⟨ connect-supp-inc-right get-snd (toVarSet (fromPath (last-path T))) ⟩
  TransportVarSet (toVarSet (fromPath (last-path T))) (connect-susp-inc-right _ _)
    ≡⟨ cong (λ - → TransportVarSet - (connect-susp-inc-right _ _)) (fromPath-last-path T) ⟩
  TransportVarSet (FVTm (tree-last-var T)) (connect-susp-inc-right _ _)
    ≡⟨ TransportVarSet-tm (tree-last-var T) (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
  FVTm (tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm) ∎
  where
    open ≡-Reasoning

supp-tree-bd : (d : ℕ) → (T : Tree n) → (b : Bool) → TVarSet T
supp-tree-bd′ : (d : ℕ) → .⦃ NonZero d ⦄ → (T : Tree n) → (b : Bool) → TVarSet′ T

supp-tree-bd zero T false = fromPath PHere
supp-tree-bd zero T true = fromPath (last-path T)
supp-tree-bd (suc d) T b = VSHere (supp-tree-bd′ (suc d) T b)

supp-tree-bd′ (suc d) Sing b = VSEmp
supp-tree-bd′ (suc d) (Join S T) b = VSExt (supp-tree-bd d S b) (supp-tree-bd′ (suc d) T b)
{-
fromPath-non-empty : (P : Path S) → Truth (tvarset-non-empty (fromPath P))
fromPath-non-empty {S = Sing} PHere = tt
fromPath-non-empty {S = Join S T} PHere = tt
fromPath-non-empty {S = Join S T} (PExt P) = Truth-left (tvarset-non-empty (fromPath P)) (tvarset-non-empty (tEmp {S = T})) (fromPath-non-empty P)
fromPath-non-empty {S = Join S T} (PShift P) = Truth-right (tvarset-non-empty (tEmp {S = S})) (tvarset-non-empty (fromPath P)) (fromPath-non-empty P)

supp-tree-bd-non-empty : (d : ℕ) → (T : Tree n) → (b : Bool) → Truth (tvarset-non-empty (supp-tree-bd d T b))
supp-tree-bd-non-empty zero T false = fromPath-non-empty (PHere {S = T})
supp-tree-bd-non-empty zero T true = fromPath-non-empty (last-path T)
supp-tree-bd-non-empty (suc d) Sing b = tt
supp-tree-bd-non-empty (suc d) (Join S T) b = tt
-}

supp-compat : (d : ℕ) → (T : Tree n) → (b : Bool) → toVarSet (supp-tree-bd d T b) ≡ pd-bd-supp d (tree-to-ctx T) ⦃ tree-to-pd T ⦄ b
supp-compat′ : (d : ℕ) → .⦃ _ : NonZero d ⦄ → (T : Tree n) → (b : Bool) → trueAt (fromℕ _) ∪ toVarSet′ (supp-tree-bd′ d T b) ≡ pd-bd-supp d (tree-to-ctx T) ⦃ tree-to-pd T ⦄ b

supp-compat zero T false = begin
  toVarSet (supp-tree-bd zero T false)
    ≡⟨ fromPath-PHere T ⟩
  trueAt (fromℕ _)
    ≡⟨ lem (tree-to-ctx T) ⦃ pd-to-pdb (tree-to-pd T) ⦄ ⟩
  pd-bd-supp zero (tree-to-ctx T) ⦃ tree-to-pd T ⦄ false ∎
  where
    lem : (Γ : Ctx (suc m)) → .⦃ pdb : Γ ⊢pdb ⦄ → trueAt (fromℕ m) ≡ pdb-bd-supp zero Γ false
    lem (∅ , A) = refl
    lem (∅ , B , A) = ⊥-elim (pdb-odd-length it)
    lem (Γ , C , B , A) with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = cong ewf (cong ewf (lem (Γ , C) ⦃ pdb-prefix it ⦄))
    ... | tri≈ ¬a b ¬c = cong ewf (cong ewf (lem (Γ , C) ⦃ pdb-prefix it ⦄))
supp-compat zero T true = let
  instance _ = tree-to-pd T
  in begin
  toVarSet (fromPath (last-path T))
    ≡⟨ fromPath-last-path T ⟩
  FVTm (tree-last-var T)
    ≡˘⟨ FVTm-≃ (tree-to-pd-focus-tm T) ⟩
  FVTm (pd-focus-tm (tree-to-pd T))
    ≡˘⟨ FVTm-≃ (pd-right-base it) ⟩
  FVTm (pdb-right-base (pd-to-pdb it))
    ≡⟨ lem (tree-to-ctx T) (pd-to-pdb it) ⟩
  pd-bd-supp zero (tree-to-ctx T) true ∎
  where
    lem : (Γ : Ctx (suc m)) → (pdb : Γ ⊢pdb) → FVTm (pdb-right-base pdb) ≡ pdb-bd-supp zero Γ ⦃ pdb ⦄ true
    lem (∅ , .⋆) Base = refl
    lem (∅ , A) (Restr pdb) = ⊥-elim (NonZero-⊥ (≤-trans (pdb-dim-lem pdb) (≤-reflexive (ty-dim-≃ (pdb-singleton-lem pdb)))))
    lem (∅ , B , A) pdb = ⊥-elim (pdb-odd-length pdb)
    lem (Γ , C , B , A) pdb with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = begin
      FVTm (pdb-right-base pdb)
        ≡⟨ FVTm-≃ (pdb-right-base-prefix pdb a) ⟩
      FVTm (lift-tm (lift-tm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ supp-lift-tm (lift-tm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (FVTm (lift-tm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ cong ewf (supp-lift-tm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (ewf (FVTm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ cong ewf (cong ewf (lem (Γ , C) (pdb-prefix pdb))) ⟩
      ewf (ewf (pdb-bd-supp 0 (Γ , C) ⦃ pdb-prefix pdb ⦄ true)) ∎
    ... | tri≈ ¬a b ¬c = begin
      FVTm (pdb-right-base pdb)
        ≡⟨ FVTm-≃ (pdb-right-base-0-dim pdb (sym b)) ⟩
      FVTm 1V
        ≡˘⟨ cong ewf (cong ewt (drop-var (pdb-right-base (pdb-prefix pdb)) ⦃ pdb-right-base-isVar (pdb-prefix pdb) ⦄)) ⟩
      ewf (ewt (drop (FVTm (pdb-right-base (pdb-prefix pdb)))))
        ≡⟨ cong ewf (cong ewt (cong drop (lem (Γ , C) (pdb-prefix pdb)))) ⟩
      ewf (ewt (drop (pdb-bd-supp 0 (Γ , C) ⦃ pdb-prefix pdb ⦄ true))) ∎
supp-compat (suc d) T b = supp-compat′ (suc d) T b

supp-compat′ (suc d) Sing b = refl
supp-compat′ (suc d) (Join S T) b = begin
  trueAt (fromℕ _) ∪
      connect-susp-supp (suspSupp (toVarSet (supp-tree-bd d S b)))
      (toVarSet′ (supp-tree-bd′ (suc d) T b))
    ≡⟨ connect-susp-supp-trueAt-lem (toVarSet (supp-tree-bd d S b)) (toVarSet′ (supp-tree-bd′ (suc d) T b)) ⟩
  connect-susp-supp (suspSupp (toVarSet (supp-tree-bd d S b))) (toVarSet′ (supp-tree-bd′ (suc d) T b))
    ≡⟨ connect-susp-supp-lem (toVarSet (supp-tree-bd d S b)) (toVarSet′ (supp-tree-bd′ (suc d) T b)) ⟩
  connect-susp-supp (suspSupp (toVarSet (supp-tree-bd d S b))) (trueAt (fromℕ _) ∪ toVarSet′ (supp-tree-bd′ (suc d) T b))
    ≡⟨ cong₂ connect-susp-supp (cong suspSupp (supp-compat d S b)) (supp-compat′ (suc d) T b) ⟩
  connect-susp-supp
    (suspSupp (pd-bd-supp d (tree-to-ctx S) b))
    (pd-bd-supp (suc d) (tree-to-ctx T) b)
    ≡⟨ connect-susp-pdb-bd-compat d (tree-to-ctx S) (tree-to-ctx T) ⦃ pd-to-pdb it ⦄ b ⟩
  pd-bd-supp (suc d) (connect-susp (tree-to-ctx S) (tree-to-ctx T)) b ∎
  where
    instance _ = tree-to-pd (Join S T)
    instance _ = tree-to-pd S
    instance _ = tree-to-pd T

{-
set-fst-true : TVarSet S → TVarSet S
set-fst-true (VSSing b) = VSSing true
set-fst-true (VSJoin b xs ys) = VSJoin true xs ys

set-fst-true-prop : (xs : TVarSet S) → set-fst-true xs ≡ set-fst-true tEmp ∪t xs
set-fst-true-prop (VSSing b) = refl
set-fst-true-prop (VSJoin b xs ys) = sym (cong₂ (VSJoin true) (∪t-left-unit xs) (∪t-left-unit ys))

DCT : TVarSet S → TVarSet S
DCT (VSSing b) = VSSing b
DCT (VSJoin b xs ys) = VSJoin (b ∨ tvarset-non-empty xs) (DCT xs) (if tvarset-non-empty xs then set-fst-true (DCT ys) else DCT ys)

DCT-non-empty : (xs : TVarSet S) → tvarset-non-empty (DCT xs) ≡ tvarset-non-empty xs
DCT-non-empty (VSSing b) = refl
DCT-non-empty (VSJoin b xs ys) rewrite DCT-non-empty xs with tvarset-non-empty xs
... | false = cong₂ _∨_ (∨-identityʳ b) (DCT-non-empty ys)
... | true = trans (∨-zeroʳ (b ∨ true)) (sym (∨-zeroʳ b))

DCT-set-fst-true : (xs : TVarSet S) → set-fst-true (DCT xs) ≡ DCT (set-fst-true xs)
DCT-set-fst-true (VSSing b) = refl
DCT-set-fst-true (VSJoin b xs ys) = refl

DCT-∪ : (xs ys : TVarSet S) → DCT (xs ∪t ys) ≡ DCT xs ∪t DCT ys
DCT-∪ (VSSing b) (VSSing b′) = refl
DCT-∪ (VSJoin b xs xs′) (VSJoin b′ ys ys′) = cong₃ VSJoin l1 (DCT-∪ xs ys) l2
  where
    open ≡-Reasoning

    l1 : (b ∨ b′) ∨ tvarset-non-empty (xs ∪t ys) ≡
           (b ∨ tvarset-non-empty xs) ∨ b′ ∨ tvarset-non-empty ys
    l1 = begin
      (b ∨ b′) ∨ tvarset-non-empty (xs ∪t ys)
        ≡⟨ cong ((b ∨ b′) ∨_) (tvarset-non-empty-∪t xs ys) ⟩
      (b ∨ b′) ∨ tvarset-non-empty xs ∨ tvarset-non-empty ys
        ≡⟨ prove 4 ((var 0F ⊕ var 1F) ⊕ var 2F ⊕ var 3F) ((var 0F ⊕ var 2F) ⊕ var 1F ⊕ var 3F) (b ∷ b′ ∷ tvarset-non-empty xs ∷ tvarset-non-empty ys ∷ emp) ⟩
      (b ∨ tvarset-non-empty xs) ∨ b′ ∨ tvarset-non-empty ys ∎
      where
        open Solver ∨-idempotentCommutativeMonoid

    open Solver ∪t-idempotentCommutativeMonoid

    l2 : (if tvarset-non-empty (xs ∪t ys) then
            set-fst-true (DCT (xs′ ∪t ys′)) else DCT (xs′ ∪t ys′))
           ≡
           (if tvarset-non-empty xs then set-fst-true (DCT xs′) else DCT xs′)
           ∪t
           (if tvarset-non-empty ys then set-fst-true (DCT ys′) else DCT ys′)
    l2 rewrite DCT-∪ xs′ ys′
       rewrite tvarset-non-empty-∪t xs ys
       rewrite set-fst-true-prop (DCT xs′ ∪t DCT ys′)
       rewrite set-fst-true-prop (DCT xs′)
       rewrite set-fst-true-prop (DCT ys′)
       with tvarset-non-empty xs | tvarset-non-empty ys
    ... | false | false = refl
    ... | false | true = prove 3 (var 0F ⊕ (var 1F ⊕ var 2F)) (var 1F ⊕ (var 0F ⊕ var 2F)) (set-fst-true tEmp ∷ DCT xs′ ∷ DCT ys′ ∷ emp)
    ... | true | false = sym (∪t-assoc (set-fst-true tEmp) (DCT xs′) (if false then set-fst-true tEmp ∪t DCT ys′ else DCT ys′))
    ... | true | true = prove 3 (var 0F ⊕ (var 1F ⊕ var 2F)) ((var 0F ⊕ var 1F) ⊕ (var 0F ⊕ var 2F)) (set-fst-true tEmp ∷ DCT xs′ ∷ DCT ys′ ∷ emp)

set-fst-true-toVarSet : (xs : TVarSet S) → toVarSet (set-fst-true xs) ≡ trueAt (fromℕ _) ∪ toVarSet xs
set-fst-true-toVarSet (VSSing b) = refl
set-fst-true-toVarSet (VSJoin {T = T} b xs ys) with tvarset-non-empty xs
... | false = begin
  connect-susp-supp (trueAt (fromℕ _)) (toVarSet ys)
    ≡˘⟨ cong₂ connect-susp-supp (lem b) (∪-left-unit (toVarSet ys)) ⟩
  connect-susp-supp
    (trueAt (fromℕ (suc (suc _))) ∪
     (if b then trueAt (fromℕ (suc (suc _))) else empty))
    (empty ∪ toVarSet ys)
    ≡˘⟨ connect-supp-∪ (trueAt (fromℕ (suc (suc _)))) (if b then trueAt (fromℕ (suc (suc _))) else empty) empty (toVarSet ys) get-snd ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc _)))) empty
  ∪ connect-susp-supp (if b then trueAt (fromℕ (suc (suc _))) else empty) (toVarSet ys)
    ≡⟨ cong (_∪ connect-susp-supp (if b then trueAt (fromℕ _) else empty) (toVarSet ys)) (connect-supp-fst get-snd (tree-size T)) ⟩
  trueAt (fromℕ (_ + suc (suc _)))
  ∪ connect-susp-supp (if b then trueAt (fromℕ _) else empty) (toVarSet ys) ∎
  where
    open ≡-Reasoning
    lem : (b : Bool)
        → trueAt (fromℕ (suc (suc _))) ∪ (if b then trueAt (fromℕ (suc (suc _))) else empty)
        ≡ trueAt (fromℕ (suc (suc _)))
    lem false = ∪-right-unit (trueAt (fromℕ _))
    lem true = ∪-idem (trueAt (fromℕ _))
... | true = begin
  connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet ys)
    ≡˘⟨ cong₂ connect-susp-supp (trans (∪-comm _ _) (sym (lookup-isVar-⊆ (suspSupp (toVarSet xs)) get-fst (suspSuppFstTruth (toVarSet xs))))) (∪-left-unit (toVarSet ys)) ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc _))) ∪ suspSupp (toVarSet xs)) (empty ∪ toVarSet ys)
    ≡˘⟨ connect-supp-∪ (trueAt (fromℕ (suc (suc _)))) (suspSupp (toVarSet xs)) empty (toVarSet ys) get-snd ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc _)))) empty ∪
    connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet ys)
    ≡⟨ cong (_∪ connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet ys)) (connect-supp-fst get-snd (tree-size T)) ⟩
  trueAt (fromℕ (_ + suc (suc _))) ∪
      connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet ys) ∎
  where
    open ≡-Reasoning

DCT-toVarSet : (xs : TVarSet S) → toVarSet (DCT xs) ≡ toVarSet xs
DCT-toVarSet (VSSing b) = refl
DCT-toVarSet (VSJoin b xs ys) rewrite DCT-non-empty xs with tvarset-non-empty xs
... | false = cong₂ connect-susp-supp (cong (λ - → if - then trueAt (fromℕ _) else empty) (∨-identityʳ b)) (DCT-toVarSet ys)
... | true = begin
  connect-susp-supp (suspSupp (toVarSet (DCT xs))) (toVarSet (set-fst-true (DCT ys)))
    ≡⟨ cong₂ connect-susp-supp (cong suspSupp (DCT-toVarSet xs)) (trans (set-fst-true-toVarSet (DCT ys)) (cong (trueAt (fromℕ _) ∪_) (DCT-toVarSet ys))) ⟩
  connect-susp-supp (suspSupp (toVarSet xs)) (trueAt (fromℕ _) ∪ toVarSet ys)
    ≡˘⟨ connect-susp-supp-lem (toVarSet xs) (toVarSet ys) ⟩
  connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet ys) ∎
  where
    open ≡-Reasoning

DCT-emp : {S : Tree n} → DCT (tEmp {S = S}) ≡ tEmp {S = S}
DCT-emp {S = Sing} = refl
DCT-emp {S = Join S T} rewrite tEmp-empty S
  = cong₂ (VSJoin false) DCT-emp DCT-emp

set-fst-true-full : {S : Tree n} → set-fst-true (tFull {S = S}) ≡ tFull {S = S}
set-fst-true-full {S = Sing} = refl
set-fst-true-full {S = Join S T} = refl

DCT-full : {S : Tree n} → DCT (tFull {S = S}) ≡ tFull {S = S}
DCT-full {S = Sing} = refl
DCT-full {S = Join S T} rewrite tFull-non-empty S
  = cong₂ (VSJoin true) DCT-full (trans (cong set-fst-true DCT-full) set-fst-true-full)

DCT-fst : (S : Tree n) → DCT (fromPath (PHere {S = S})) ≡ fromPath (PHere {S = S})
DCT-fst Sing = refl
DCT-fst (Join S T) rewrite tEmp-empty S = cong₂ (VSJoin true) DCT-emp DCT-emp

DCT-last-path : (T : Tree n) → DCT (fromPath (last-path T)) ≡ fromPath (last-path T)
DCT-last-path Sing = refl
DCT-last-path (Join S T) rewrite tEmp-empty S = cong₂ (VSJoin false) DCT-emp (DCT-last-path T)

tvarset-fst : TVarSet S → Bool
tvarset-fst (VSSing b) = b
tvarset-fst (VSJoin b _ _) = b

tvarset-fst-prop : (xs ys : TVarSet S) → set-fst-true xs ≡ set-fst-true ys → tvarset-fst xs ≡ tvarset-fst ys → xs ≡ ys
tvarset-fst-prop (VSSing b) (VSSing .(tvarset-fst (VSSing b))) p refl = refl
tvarset-fst-prop (VSJoin b xs xs′) (VSJoin .(tvarset-fst (VSJoin b xs xs′)) .xs .xs′) refl refl = refl

tvarset-fst-set-fst : (xs : TVarSet S) → Truth (tvarset-fst xs) → set-fst-true xs ≡ xs
tvarset-fst-set-fst (VSSing true) p = refl
tvarset-fst-set-fst (VSJoin true _ _) p = refl

tvarset-fst-toVarSet : (xs : TVarSet S) → tvarset-fst (DCT xs) ≡ lookup (toVarSet xs) (fromℕ _)
tvarset-fst-toVarSet (VSSing b) = refl
tvarset-fst-toVarSet (VSJoin {n} b xs ys) = begin
  b ∨ tvarset-non-empty xs
    ≡⟨ lem (tvarset-non-empty xs) b ⟩
  (if tvarset-non-empty xs then
    lookup (suspSupp (toVarSet xs)) (fromℕ (suc (suc _))) else
    lookup (if b then ewf (ewf (trueAt (fromℕ _))) else empty) (fromℕ (suc (suc _))))
    ≡˘⟨ push-function-into-if (λ a → lookup a (fromℕ _)) (tvarset-non-empty xs) ⟩
  lookup
    (if tvarset-non-empty xs then suspSupp (toVarSet xs) else
     (if b then ewf (ewf (trueAt (fromℕ _))) else empty))
    (fromℕ _)
    ≡˘⟨ connect-susp-supp-fst-var (if tvarset-non-empty xs then suspSupp (toVarSet xs) else
        (if b then ewf (ewf (trueAt (fromℕ _))) else empty)) (toVarSet ys) ⟩
  lookup
      (connect-susp-supp
       (if tvarset-non-empty xs then suspSupp (toVarSet xs) else
        (if b then ewf (ewf (trueAt (fromℕ _))) else empty))
       (toVarSet ys))
      (fromℕ _) ∎
  where
    open ≡-Reasoning
    lem : (b′ b : Bool) → b ∨ b′ ≡
      (if b′ then
       lookup (suspSupp (toVarSet xs)) (suc (suc (fromℕ _))) else
       lookup (if b then ewf (ewf (trueAt (fromℕ _))) else empty)
       (suc (suc (fromℕ _))))
    lem false false = sym (lookup-empty (fromℕ n))
    lem false true = sym (lookup-trueAt (fromℕ n))
    lem true b = begin
      b ∨ true
        ≡⟨ ∨-zeroʳ b ⟩
      true
        ≡˘⟨ suspSupp-fst-var (toVarSet xs) ⟩
      lookup (suspSupp (toVarSet xs)) (fromℕ _) ∎
-}

TVarSet-fst : TVarSet S → Bool
TVarSet-fst (VSHere x) = true
TVarSet-fst (VSNotHere xs) = false

TVarSet-fst-toVarSet : (xs : TVarSet S) → lookup (toVarSet xs) (fromℕ _) ≡ TVarSet-fst xs
TVarSet-fst-toVarSet {S = S} (VSHere x) = begin
  lookup (trueAt (fromℕ _) ∪ toVarSet′ x) (fromℕ _)
    ≡⟨ lookup-∪ (trueAt (fromℕ (tree-size S))) (toVarSet′ x) (fromℕ (tree-size S)) ⟩
  lookup (trueAt (fromℕ (tree-size S))) (fromℕ _) ∨
    lookup (toVarSet′ x) (fromℕ _)
    ≡⟨ cong (_∨ lookup (toVarSet′ x) (fromℕ _)) (lookup-trueAt (fromℕ (tree-size S))) ⟩
  true ∎
TVarSet-fst-toVarSet (VSNotHere {S = S} xs) = begin
  lookup (connect-susp-supp empty (toVarSet xs)) (fromℕ _)
    ≡⟨ connect-susp-supp-fst-var empty (toVarSet xs) ⟩
  lookup empty (fromℕ (2 + tree-size S))
    ≡⟨ lookup-empty (fromℕ (2 + tree-size S)) ⟩
  false ∎

Here≢NotHere : (xs : TVarSet′ (Join S T)) → (ys : TVarSet T) → toVarSet (VSHere xs) ≡ toVarSet (VSNotHere {S = S} ys) → ⊥
Here≢NotHere {S = S} xs ys p = absurd (begin
  true
    ≡˘⟨ TVarSet-fst-toVarSet (VSHere xs) ⟩
  lookup (toVarSet (VSHere xs)) (fromℕ _)
    ≡⟨ cong (λ - → lookup - (fromℕ _)) p ⟩
  lookup (toVarSet (VSNotHere {S = S} ys)) (fromℕ _)
    ≡⟨ TVarSet-fst-toVarSet (VSNotHere {S = S} ys) ⟩
  false ∎)

toVarSet-non-empty : (xs : TVarSet S) → Truth (varset-non-empty (toVarSet xs))
toVarSet-non-empty {S = S} (VSHere x) = ∪-non-empty-left (trueAt (fromℕ _)) (toVarSet′ x) (trueAt-non-empty (fromℕ (tree-size S)))
toVarSet-non-empty (VSNotHere xs) = connect-susp-supp-non-empty-right empty (toVarSet xs) (toVarSet-non-empty xs)


toVarSet-reflect : {xs ys : TVarSet S} → toVarSet xs ≡ toVarSet ys → xs ≡ ys
toVarSet′-reflect : {xs ys : TVarSet′ S} → trueAt (fromℕ _) ∪ toVarSet′ xs ≡ trueAt (fromℕ _) ∪ toVarSet′ ys → xs ≡ ys

toVarSet-reflect {xs = VSHere x} {ys = VSHere y} p = cong VSHere (toVarSet′-reflect p)
toVarSet-reflect {xs = VSHere x} {ys = VSNotHere ys} p = ⊥-elim (Here≢NotHere x ys p)
toVarSet-reflect {xs = VSNotHere xs} {ys = VSHere x} p = ⊥-elim (Here≢NotHere x xs (sym p))
toVarSet-reflect {xs = VSNotHere {S = S} xs} {ys = VSNotHere ys} p
  = cong VSNotHere
         (toVarSet-reflect (connect-supp-proj-right-emp
                             _
                             empty
                             empty
                             (Truth-not-prop′ (lookup-empty (inject₁ (fromℕ (tree-size S)))))
                             (Truth-not-prop′ (lookup-empty (inject₁ (fromℕ (tree-size S)))))
                             (toVarSet xs)
                             (toVarSet ys)
                             p))



Emp≢Ext : (ys : VarSet (suc m)) → (xs : VarSet (suc n)) → trueAt (fromℕ _) ∪ empty ≡ trueAt (fromℕ _) ∪ connect-susp-supp (suspSupp xs) ys → ⊥
Emp≢Ext {m = zero} {n = zero} (ewf ys) (x ∷ emp) ()
Emp≢Ext {m = zero} {n = suc n} (ewf ys) (x ∷ xs) p = Emp≢Ext (ewf ys) xs (cong tail p)
Emp≢Ext {m = zero} {n = zero} (ewt ys) (x ∷ emp) ()
Emp≢Ext {m = zero} {n = suc n} (ewt ys) (x ∷ xs) p = Emp≢Ext (ewt ys) xs (cong tail p)
Emp≢Ext {m = suc m} (y ∷ ys) xs p = Emp≢Ext ys xs (cong tail p)

Emp≢Shift : (n : ℕ) → (xs : VarSet (suc m)) → Truth (varset-non-empty xs) → trueAt (fromℕ _) ∪ empty ≡ trueAt (fromℕ _) ∪ connect-susp-supp (empty {n = 3 + n}) xs → ⊥
Emp≢Shift {m = zero} (suc n) (ewt emp) ne p = Emp≢Shift n (ewt emp) ne (cong tail p)
Emp≢Shift {m = suc m} n (ewf xs) ne p = Emp≢Shift n xs ne (cong tail p)

Ext≢Shift : (xs : VarSet (suc n)) → Truth (varset-non-empty xs) → (xs′ ys : VarSet (suc m)) →
  trueAt (fromℕ _) ∪ connect-susp-supp (suspSupp xs) xs′
  ≡ trueAt (fromℕ _) ∪ connect-susp-supp empty ys
  → ⊥
Ext≢Shift {n = n} xs ne xs′ ys p = absurd (begin
  true
    ≡˘⟨ Truth-prop ne ⟩
  varset-non-empty xs
    ≡⟨ cong varset-non-empty (connect-susp-supp-proj-left xs empty xs′ ys lem) ⟩
  varset-non-empty (empty {n = suc n})
    ≡⟨ empty-is-empty {n = suc n} ⟩
  false ∎)
  where
    lem : connect-susp-supp (suspSupp xs) xs′ ≡
            connect-susp-supp (suspSupp empty) ys
    lem = begin
      connect-susp-supp (suspSupp xs) xs′
        ≡⟨ cong (λ - → connect-susp-supp - xs′) (suspSuppEmpRight xs) ⟩
      connect-susp-supp (suspSupp xs ∪ suspSupp empty) xs′
        ≡˘⟨ connect-susp-supp-susp-lem xs′ (suspSupp xs) ⟩
      trueAt (raise (suc _) (inject₁ (fromℕ _))) ∪
        (trueAt (fromℕ (_ + (2 + _))) ∪
         connect-susp-supp (suspSupp xs) xs′)
        ≡⟨ cong (trueAt (raise (suc _) (inject₁ (fromℕ _))) ∪_) p ⟩
      trueAt (raise (suc _) (inject₁ (fromℕ _))) ∪ (trueAt (fromℕ (_ + (2 + _))) ∪ connect-susp-supp empty ys)
        ≡⟨ connect-susp-supp-susp-lem ys empty ⟩
      connect-susp-supp (empty ∪ suspSupp empty) ys
        ≡⟨ cong (λ - → connect-susp-supp - ys) (∪-left-unit (suspSupp empty)) ⟩
      connect-susp-supp (suspSupp empty) ys ∎

toVarSet′-reflect {xs = VSEmp} {ys = VSEmp} p = refl
toVarSet′-reflect {xs = VSEmp} {ys = VSExt xs ys} p = ⊥-elim (Emp≢Ext (toVarSet′ ys) (toVarSet xs) p)
toVarSet′-reflect {xs = VSEmp} {ys = VSShift ys} p = ⊥-elim (Emp≢Shift _ (toVarSet ys) (toVarSet-non-empty ys) p)
toVarSet′-reflect {xs = VSExt xs xs′} {ys = VSEmp} p = ⊥-elim (Emp≢Ext (toVarSet′ xs′) (toVarSet xs) (sym p))
toVarSet′-reflect {xs = VSExt xs xs′} {ys = VSExt ys ys′} p = cong₂ VSExt (toVarSet-reflect (connect-susp-supp-proj-left (toVarSet xs) (toVarSet ys) (toVarSet′ xs′) (toVarSet′ ys′) lem)) (toVarSet′-reflect (connect-susp-supp-proj-right (suspSupp (toVarSet xs)) (suspSupp (toVarSet ys)) (toVarSet′ xs′) (toVarSet′ ys′) lem))
  where
    lem : connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet′ xs′) ≡ connect-susp-supp (suspSupp (toVarSet ys)) (toVarSet′ ys′)
    lem = begin
      connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet′ xs′)
        ≡˘⟨ connect-susp-supp-trueAt-lem (toVarSet xs) (toVarSet′ xs′) ⟩
      trueAt (fromℕ _) ∪ connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet′ xs′)
        ≡⟨ p ⟩
      trueAt (fromℕ _) ∪ connect-susp-supp (suspSupp (toVarSet ys)) (toVarSet′ ys′)
        ≡⟨ connect-susp-supp-trueAt-lem (toVarSet ys) (toVarSet′ ys′) ⟩
      connect-susp-supp (suspSupp (toVarSet ys)) (toVarSet′ ys′) ∎
toVarSet′-reflect {xs = VSExt xs xs′} {ys = VSShift ys} p = ⊥-elim (Ext≢Shift (toVarSet xs) (toVarSet-non-empty xs) (toVarSet′ xs′) (toVarSet ys) p)
toVarSet′-reflect {xs = VSShift xs} {ys = VSEmp} p = ⊥-elim (Emp≢Shift _ (toVarSet xs) (toVarSet-non-empty xs) (sym p))
toVarSet′-reflect {xs = VSShift xs} {ys = VSExt ys ys′} p = ⊥-elim (Ext≢Shift (toVarSet ys) (toVarSet-non-empty ys) (toVarSet′ ys′) (toVarSet xs) (sym p))
toVarSet′-reflect {xs = VSShift {S = S} xs} {ys = VSShift ys} p = cong VSShift (toVarSet-reflect (connect-supp-proj-right-emp _ (trueAt (fromℕ _)) (trueAt (fromℕ _)) (Truth-not-prop′ (lookup-snd-var-fst (tree-size S))) (Truth-not-prop′ (lookup-snd-var-fst (tree-size S))) (toVarSet xs) (toVarSet ys) (begin
  connect-susp-supp (trueAt (fromℕ (suc (suc _)))) (toVarSet xs)
    ≡˘⟨ connect-susp-supp-trueAt-lem′ _ (toVarSet xs) ⟩
  trueAt (fromℕ _) ∪ connect-susp-supp empty (toVarSet xs)
    ≡⟨ p ⟩
  trueAt (fromℕ _) ∪ connect-susp-supp empty (toVarSet ys)
    ≡⟨ connect-susp-supp-trueAt-lem′ _ (toVarSet ys) ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc _)))) (toVarSet ys) ∎)))

{-
DCT-reflect : {xs ys : TVarSet S} → toVarSet xs ≡ toVarSet ys → DCT xs ≡ DCT ys
DCT-reflect {xs = VSSing b} {ys = VSSing .b} refl = refl
DCT-reflect {xs = VSJoin b xs xs′} {ys = VSJoin b′ ys ys′} p = final
  where
    open ≡-Reasoning
    import Algebra.Solver.IdempotentCommutativeMonoid as Solver
    connect-prop : ∀ (xs xs′ : VarSet (3 + n)) (ys ys′ : VarSet 1) → connect-susp-supp xs ys ≡ connect-susp-supp xs′ ys′ → xs ∪ FVTm get-snd ≡ xs′ ∪ FVTm get-snd
    connect-prop xs xs′ (ewf emp) (ewf emp) p = cong (_∪ trueAt (inject₁ (fromℕ _))) p
    connect-prop xs xs′ (ewf emp) (ewt emp) p = begin
      xs ∪ FVTm get-snd
        ≡⟨ cong (_∪ FVTm get-snd) p ⟩
      xs′ ∪ FVTm get-snd ∪ FVTm get-snd
        ≡⟨ prove 2 ((var 0F ⊕ var 1F) ⊕ var 1F) (var 0F ⊕ var 1F) (_ ∷ _ ∷ emp) ⟩
      xs′ ∪ FVTm get-snd ∎
      where
        open Solver (∪-idempotentCommutativeMonoid)
    connect-prop xs xs′ (ewt emp) (ewf emp) p = begin
      xs ∪ FVTm get-snd
        ≡⟨ prove 2 (var 0F ⊕ var 1F) ((var 0F ⊕ var 1F) ⊕ var 1F) (_ ∷ _ ∷ emp) ⟩
      xs ∪ FVTm get-snd ∪ FVTm get-snd
        ≡⟨ cong (_∪ FVTm get-snd) p ⟩
      xs′ ∪ FVTm get-snd ∎
      where
        open Solver (∪-idempotentCommutativeMonoid)
    connect-prop xs xs′ (ewt emp) (ewt emp) p = p

    absurd : {A : Set} → (true ≡ false) → A
    absurd ()

    suspSupp-reflect : (xs ys : VarSet n) → suspSupp xs ∪ FVTm get-snd ≡ suspSupp ys ∪ FVTm get-snd → xs ≡ ys
    suspSupp-reflect emp emp p = refl
    suspSupp-reflect (x ∷ xs) (y ∷ ys) p = cong₂ _∷_ lem (suspSupp-reflect xs ys (cong tail p))
      where
        lem : x ≡ y
        lem = begin
          x
            ≡˘⟨ ∨-identityʳ x ⟩
          x ∨ false
            ≡⟨ cong head p ⟩
          y ∨ false
            ≡⟨ ∨-identityʳ y ⟩
          y ∎

    susp-prop : ∀ (xs ys : VarSet n) (b b′ : Bool) → (if varset-non-empty xs then suspSupp xs else (if b then FVTm get-fst else empty)) ∪ FVTm get-snd ≡ (if varset-non-empty ys then suspSupp ys else (if b′ then FVTm get-fst else empty)) ∪ FVTm get-snd → xs ≡ ys
    susp-prop emp emp b b′ p = refl
    susp-prop (ewf xs) (ewf ys) b b′ p = cong ewf (susp-prop xs ys b b′ lem)
      where
        lem : (if varset-non-empty xs then suspSupp xs else
                 (if b then FVTm get-fst else empty)) ∪ FVTm get-snd
                ≡
                (if varset-non-empty ys then suspSupp ys else
                 (if b′ then FVTm get-fst else empty)) ∪ FVTm get-snd
        lem = cong tail (begin
          ewf ((if varset-non-empty xs then suspSupp xs else (if b then trueAt (fromℕ (suc _)) else replicate false)) ∪ FVTm get-snd)
            ≡⟨ cong (_∪ FVTm get-snd) (push-function-into-if ewf (varset-non-empty xs)) ⟩
          (if varset-non-empty xs then ewf (suspSupp xs) else ewf (if b then trueAt (fromℕ (suc _)) else replicate false)) ∪ FVTm get-snd
            ≡⟨ cong (λ a → (if varset-non-empty xs then ewf (suspSupp xs) else a) ∪ FVTm get-snd) (push-function-into-if ewf b) ⟩
          (if varset-non-empty xs then ewf (suspSupp xs) else (if b then FVTm get-fst else empty)) ∪ FVTm get-snd
            ≡⟨ p ⟩
          (if varset-non-empty ys then ewf (suspSupp ys) else (if b′ then FVTm get-fst else empty)) ∪ FVTm get-snd
            ≡˘⟨ cong (λ a → (if varset-non-empty ys then ewf (suspSupp ys) else a) ∪ FVTm get-snd) (push-function-into-if ewf b′) ⟩
          (if varset-non-empty ys then ewf (suspSupp ys) else ewf (if b′ then trueAt (fromℕ (suc _)) else replicate false)) ∪ FVTm get-snd
            ≡˘⟨ cong (_∪ FVTm get-snd) (push-function-into-if ewf (varset-non-empty ys)) ⟩
          ewf ((if varset-non-empty ys then suspSupp ys else (if b′ then FVTm get-fst else empty)) ∪ (FVTm get-snd)) ∎)
    susp-prop (ewf xs) (ewt ys) b b′ p = absurd (sym lem)
      where
        lem : false ≡ true
        lem = begin
          false
            ≡˘⟨ if-lem-const (varset-non-empty (ewf xs)) false ⟩
          (if varset-non-empty (ewf xs) then false else false)
            ≡˘⟨ cong (if varset-non-empty (ewf xs) then false else_) (if-lem-const b false) ⟩
          (if varset-non-empty (ewf xs) then false else
            (if b then false else false))
            ≡˘⟨ cong (if varset-non-empty (ewf xs) then false else_) (push-function-into-if (λ a → lookup a 0F) b) ⟩
          (if varset-non-empty (ewf xs) then false else lookup (if b then FVTm get-fst else empty) 0F)
            ≡˘⟨ push-function-into-if (λ a → lookup a 0F) (varset-non-empty (ewf xs)) ⟩
          lookup (if varset-non-empty (ewf xs) then suspSupp (ewf xs) else (if b then FVTm get-fst else empty)) 0F
            ≡˘⟨ ∨-identityʳ _ ⟩
          lookup
            (if varset-non-empty (ewf xs) then suspSupp (ewf xs) else
             (if b then FVTm get-fst else empty))
            0F
            ∨ false
            ≡˘⟨ lookup-∪ (if varset-non-empty (ewf xs) then suspSupp (ewf xs) else (if b then FVTm get-fst else empty)) (FVTm get-snd) 0F ⟩
          lookup ((if varset-non-empty (ewf xs) then suspSupp (ewf xs) else (if b then FVTm get-fst else empty)) ∪ FVTm get-snd) 0F
            ≡⟨ cong (λ a → lookup a 0F) p ⟩
          true ∎
    susp-prop (ewt xs) (ewf ys) b b′ p = absurd lem
      where
        lem : true ≡ false
        lem = begin
          true
            ≡⟨ cong (λ a → lookup a 0F) p ⟩
          lookup
            ((if varset-non-empty (ewf ys) then suspSupp (ewf ys) else
              (if b′ then FVTm get-fst else empty))
             ∪ FVTm get-snd)
            0F
            ≡⟨ lookup-∪ (if varset-non-empty (ewf ys) then suspSupp (ewf ys) else
              (if b′ then FVTm get-fst else empty)) (FVTm get-snd) 0F ⟩
          lookup
            (if varset-non-empty (ewf ys) then suspSupp (ewf ys) else
             (if b′ then FVTm get-fst else empty))
            0F
            ∨ false
            ≡⟨ ∨-identityʳ _ ⟩
          lookup (if varset-non-empty (ewf ys) then suspSupp (ewf ys) else (if b′ then FVTm get-fst else empty)) 0F
            ≡⟨ push-function-into-if (λ a → lookup a 0F) (varset-non-empty ys) ⟩
          (if varset-non-empty ys then false else lookup (if b′ then FVTm get-fst else empty) 0F)
            ≡⟨ cong (if varset-non-empty ys then false else_) (push-function-into-if (λ a → lookup a 0F) b′) ⟩
          (if varset-non-empty ys then false else (if b′ then false else false))
            ≡⟨ cong (if varset-non-empty ys then false else_) (if-lem-const b′ false) ⟩
          (if varset-non-empty ys then false else false)
            ≡⟨ if-lem-const (varset-non-empty ys) false ⟩
          false ∎
    susp-prop (ewt xs) (ewt ys) b b′ p = suspSupp-reflect (ewt xs) (ewt ys) p

    lem : ∀ b (xs ys : VarSet (suc n)) b′ (xs′ ys′ : VarSet (suc m))
        → connect-susp-supp (if varset-non-empty xs then suspSupp xs else (if b then ewf (ewf (trueAt (fromℕ _))) else empty)) xs′
        ≡ connect-susp-supp (if varset-non-empty ys then suspSupp ys else (if b′ then ewf (ewf (trueAt (fromℕ _))) else empty)) ys′
        → xs ≡ ys
    lem {m = zero} b xs ys b′ xs′ ys′ p = susp-prop xs ys b b′ (connect-prop (if varset-non-empty xs then suspSupp xs else
                                                                                           (if b then FVTm get-fst else empty)) (if varset-non-empty ys then suspSupp ys else
                                                                                                                                 (if b′ then FVTm get-fst else empty)) xs′ ys′ p)
    lem {m = suc m} b xs ys b′ (x ∷ xs′) (y ∷ ys′) p = lem b xs ys b′ xs′ ys′ (cong tail p)

    lem2 : DCT xs ≡ DCT ys
    lem2 = DCT-reflect (lem b (toVarSet xs) (toVarSet ys) b′ (toVarSet xs′) (toVarSet ys′) (begin
      connect-susp-supp
        (if varset-non-empty (toVarSet xs) then suspSupp (toVarSet xs) else
         (if b then ewf (ewf (trueAt (fromℕ _))) else empty))
        (toVarSet xs′)
        ≡˘⟨ cong
             (λ a →
                connect-susp-supp
                (if a then suspSupp (toVarSet xs) else
                 (if b then ewf (ewf (trueAt (fromℕ _))) else empty))
                (toVarSet xs′))
             (tvarset-non-empty-compat xs) ⟩
      toVarSet (VSJoin b xs xs′)
        ≡⟨ p ⟩
      toVarSet (VSJoin b′ ys ys′)
        ≡⟨ cong
             (λ a →
                connect-susp-supp
                (if a then suspSupp (toVarSet ys) else
                 (if b′ then ewf (ewf (trueAt (fromℕ _))) else empty))
                (toVarSet ys′))
             (tvarset-non-empty-compat ys) ⟩
      connect-susp-supp
        (if varset-non-empty (toVarSet ys) then suspSupp (toVarSet ys) else
         (if b′ then ewf (ewf (trueAt (fromℕ _))) else empty))
        (toVarSet ys′) ∎))

    lem3 : (xs ys : TVarSet S) → xs ≡ ys → (xs′ ys′ : TVarSet T) → (b b′ : Bool)
         → toVarSet (VSJoin b xs xs′) ≡ toVarSet (VSJoin b′ ys ys′)
         → VSJoin (b ∨ tvarset-non-empty xs) xs (if tvarset-non-empty xs then set-fst-true (DCT xs′) else DCT xs′)
         ≡ VSJoin (b′ ∨ tvarset-non-empty ys) ys (if tvarset-non-empty ys then set-fst-true (DCT ys′) else DCT ys′)
    lem3 {n} {_} {m} xs .xs refl xs′ ys′ b b′ p = final
      where
        lem4 : set-fst-true (DCT xs′) ≡ set-fst-true (DCT ys′)
        lem4 = begin
          set-fst-true (DCT xs′)
            ≡⟨ DCT-set-fst-true xs′ ⟩
          DCT (set-fst-true xs′)
            ≡⟨ DCT-reflect l1 ⟩
          DCT (set-fst-true ys′)
            ≡˘⟨ DCT-set-fst-true ys′ ⟩
          set-fst-true (DCT ys′) ∎
          where
            l1 : toVarSet (set-fst-true xs′) ≡ toVarSet (set-fst-true ys′)
            l1 = begin
              toVarSet (set-fst-true xs′)
                ≡⟨ set-fst-true-toVarSet xs′ ⟩
              trueAt (fromℕ _) ∪ toVarSet xs′
                ≡⟨ connect-susp-supp-proj-right _ _ _ _ p ⟩
              trueAt (fromℕ _) ∪ toVarSet ys′
                ≡˘⟨ set-fst-true-toVarSet ys′ ⟩
              toVarSet (set-fst-true ys′) ∎
        final : VSJoin (b ∨ tvarset-non-empty xs) xs (if tvarset-non-empty xs then set-fst-true (DCT xs′) else DCT xs′)
              ≡ VSJoin (b′ ∨ tvarset-non-empty xs) xs (if tvarset-non-empty xs then set-fst-true (DCT ys′) else DCT ys′)
        final with tvarset-non-empty xs
        ... | false = cong₂ (λ a → VSJoin a xs) l2 (tvarset-fst-prop (DCT xs′) (DCT ys′) lem4 l4)
          where
            l1 : b ≡ b′
            l1 = begin
              b
                ≡˘⟨ if-lem b ⟩
              (if b then true else false)
                ≡˘⟨ cong₂ (if b then_else_) (lookup-trueAt (fromℕ (2 + n))) (lookup-empty (fromℕ (3 + n))) ⟩
              (if b then lookup (trueAt (fromℕ (suc (suc n)))) (fromℕ (2 + n)) else lookup empty (fromℕ (2 + n)))
                ≡˘⟨ push-function-into-if (λ a → lookup a (fromℕ (suc (suc n)))) b {y = trueAt (fromℕ (suc (suc n)))} {z = empty {n = 3 + n}} ⟩
              lookup (if b then trueAt (fromℕ (suc (suc n))) else empty) (fromℕ (suc (suc n)))
                ≡˘⟨ connect-susp-supp-fst-var (if b then trueAt (fromℕ _) else empty) (toVarSet xs′) ⟩
              lookup (connect-susp-supp (if b then trueAt (fromℕ _) else empty) (toVarSet xs′)) (fromℕ _)
                ≡⟨ cong (λ a → lookup a (fromℕ _)) p ⟩
              lookup (connect-susp-supp (if b′ then trueAt (fromℕ _) else empty) (toVarSet ys′)) (fromℕ _)
                ≡⟨ connect-susp-supp-fst-var (if b′ then trueAt (fromℕ _) else empty) (toVarSet ys′) ⟩
              lookup (if b′ then trueAt (fromℕ (suc (suc n))) else empty) (fromℕ (suc (suc n)))
                ≡⟨ push-function-into-if (λ a → lookup a (fromℕ (2 + n))) b′ ⟩
              (if b′ then lookup (trueAt (fromℕ (suc (suc n)))) (fromℕ (2 + n)) else lookup empty (fromℕ (2 + n)))
                ≡⟨ cong₂ (if b′ then_else_) (lookup-trueAt (fromℕ (2 + n))) (lookup-empty (fromℕ (2 + n))) ⟩
              (if b′ then true else false)
                ≡⟨ if-lem b′ ⟩
              b′ ∎
            l2 : b ∨ false ≡ b′ ∨ false
            l2 = begin
              b ∨ false
                ≡⟨ ∨-identityʳ b ⟩
              b
                ≡⟨ l1 ⟩
              b′
                ≡˘⟨ ∨-identityʳ b′ ⟩
              b′ ∨ false ∎

            l3 : (b : Bool) → (n : ℕ) → lookup (if b then trueAt (fromℕ (suc n)) else empty) (inject₁ (fromℕ n)) ≡ false
            l3 false n = lookup-empty (inject₁ (fromℕ n))
            l3 true zero = refl
            l3 true (suc n) = l3 true n

            l4 : tvarset-fst (DCT xs′) ≡ tvarset-fst (DCT ys′)
            l4 = begin
              tvarset-fst (DCT xs′)
                ≡⟨ cong₂ _∨_ (sym (l3 b (suc n))) (tvarset-fst-toVarSet xs′) ⟩
              lookup (if b then ewf (ewf (trueAt (fromℕ n))) else empty) (inject₁ (fromℕ (suc n)))
                ∨ lookup (toVarSet xs′) (fromℕ _)
                ≡˘⟨ connect-susp-supp-snd-var (if b then ewf (ewf (trueAt (fromℕ n))) else empty) (toVarSet xs′) ⟩
              lookup (connect-susp-supp (if b then ewf (ewf (trueAt (fromℕ n))) else empty) (toVarSet xs′))
                (raise (suc m) (inject₁ (fromℕ n)))
                ≡⟨ cong (λ a → lookup a (raise (suc m) (inject₁ (fromℕ n)))) p ⟩
              lookup (connect-susp-supp (if b′ then ewf (ewf (trueAt (fromℕ n))) else empty) (toVarSet ys′))
                (raise (suc m) (inject₁ (fromℕ n)))
                ≡⟨ connect-susp-supp-snd-var (if b′ then ewf (ewf (trueAt (fromℕ n))) else empty) (toVarSet ys′) ⟩
              lookup (if b′ then ewf (ewf (trueAt (fromℕ n))) else empty)
                (inject₁ (fromℕ (suc n)))
                ∨ lookup (toVarSet ys′) (fromℕ _)
                ≡⟨ cong₂ _∨_ (l3 b′ (suc n)) (sym (tvarset-fst-toVarSet ys′)) ⟩
              tvarset-fst (DCT ys′) ∎

        ... | true = cong₂ (λ a → VSJoin a xs) (trans (∨-zeroʳ b) (sym (∨-zeroʳ b′))) lem4

    final : VSJoin (b ∨ tvarset-non-empty xs) (DCT xs) (if tvarset-non-empty xs then set-fst-true (DCT xs′) else DCT xs′)
          ≡ VSJoin (b′ ∨ tvarset-non-empty ys) (DCT ys) (if tvarset-non-empty ys then set-fst-true (DCT ys′) else DCT ys′)
    final rewrite sym (DCT-non-empty xs)
          rewrite sym (DCT-non-empty ys) = lem3 (DCT xs) (DCT ys) lem2 xs′ ys′ b b′ last-lem
          where
            last-lem : toVarSet (VSJoin b (DCT xs) xs′) ≡
                         toVarSet (VSJoin b′ (DCT ys) ys′)
            last-lem rewrite DCT-toVarSet xs
                     rewrite DCT-toVarSet ys = p

supp-tvarset : TVarSet S → TVarSet (suspTree S)
supp-tvarset xs = VSJoin true xs (VSSing true)

supp-tvarset-DCT : (xs : TVarSet S) → DCT (supp-tvarset xs) ≡ supp-tvarset (DCT xs)
supp-tvarset-DCT xs = cong (VSJoin true (DCT xs)) (if-lem-const (tvarset-non-empty xs) (set-fst-true (DCT (VSSing true))))
-}
