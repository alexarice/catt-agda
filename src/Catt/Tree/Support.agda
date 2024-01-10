module Catt.Tree.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Pasting
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Connection.Support
open import Catt.Connection.Support
open import Catt.Suspension.Support

open import Algebra.Bundles
open import Algebra.Definitions
import Algebra.Solver.IdempotentCommutativeMonoid as Solver
open import Data.Vec.Relation.Binary.Pointwise.Inductive as P using ()

data TVarSet : (T : Tree n) → Set where
  VSSing : (b : Bool) → TVarSet Sing
  VSJoin : (b : Bool) → TVarSet S → TVarSet T → TVarSet (Join S T)

tEmp : TVarSet S
tEmp {S = Sing} = VSSing false
tEmp {S = Join S T} = VSJoin false tEmp tEmp

tFull : TVarSet S
tFull {S = Sing} = VSSing true
tFull {S = Join S T} = VSJoin true tFull tFull

infixl 60 _∪t_
_∪t_ : TVarSet S → TVarSet S → TVarSet S
VSSing b ∪t VSSing b′ = VSSing (b ∨ b′)
VSJoin b xs xs′ ∪t VSJoin b′ ys ys′ = VSJoin (b ∨ b′) (xs ∪t ys) (xs′ ∪t ys′)

∪t-left-unit : LeftIdentity _≡_ tEmp (_∪t_ {S = S})
∪t-left-unit (VSSing b) = refl
∪t-left-unit (VSJoin b xs ys) = cong₂ (VSJoin b) (∪t-left-unit xs) (∪t-left-unit ys)

∪t-right-unit : RightIdentity _≡_ tEmp (_∪t_ {S = S})
∪t-right-unit (VSSing b) = cong VSSing (∨-identityʳ b)
∪t-right-unit (VSJoin b xs ys) = cong₃ VSJoin (∨-identityʳ b) (∪t-right-unit xs) (∪t-right-unit ys)

∪t-left-zero : LeftZero _≡_ tFull (_∪t_ {S = S})
∪t-left-zero (VSSing b) = refl
∪t-left-zero (VSJoin b xs ys) = cong₂ (VSJoin true) (∪t-left-zero xs) (∪t-left-zero ys)

∪t-right-zero : RightZero _≡_ tFull (_∪t_ {S = S})
∪t-right-zero (VSSing b) = cong VSSing (∨-zeroʳ b)
∪t-right-zero (VSJoin b xs ys) = cong₃ VSJoin (∨-zeroʳ b) (∪t-right-zero xs) (∪t-right-zero ys)

∪t-assoc : Associative _≡_ (_∪t_ {S = S})
∪t-assoc (VSSing b) (VSSing b′) (VSSing b″) = cong VSSing (∨-assoc b b′ b″)
∪t-assoc (VSJoin b xs xs′) (VSJoin b′ ys ys′) (VSJoin b″ zs zs′) = cong₃ VSJoin (∨-assoc b b′ b″) (∪t-assoc xs ys zs) (∪t-assoc xs′ ys′ zs′)

∪t-comm : Commutative _≡_ (_∪t_ {S = S})
∪t-comm (VSSing b) (VSSing b′) = cong VSSing (∨-comm b b′)
∪t-comm (VSJoin b xs xs′) (VSJoin b′ ys ys′) = cong₃ VSJoin (∨-comm b b′) (∪t-comm xs ys) (∪t-comm xs′ ys′)

∪t-idem : Idempotent _≡_ (_∪t_ {S = S})
∪t-idem (VSSing b) = cong VSSing (∨-idem b)
∪t-idem (VSJoin b xs xs′) = cong₃ VSJoin (∨-idem b) (∪t-idem xs) (∪t-idem xs′)

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

tvarset-non-empty : TVarSet S → Bool
tvarset-non-empty (VSSing b) = b
tvarset-non-empty (VSJoin b xs ys) = b ∨ tvarset-non-empty xs ∨ tvarset-non-empty ys

tvarset-non-empty-∪t : (xs ys : TVarSet S) → tvarset-non-empty (xs ∪t ys) ≡ tvarset-non-empty xs ∨ tvarset-non-empty ys
tvarset-non-empty-∪t (VSSing b) (VSSing b′) = refl
tvarset-non-empty-∪t (VSJoin b xs xs′) (VSJoin b′ ys ys′)
  rewrite tvarset-non-empty-∪t xs ys
  rewrite tvarset-non-empty-∪t xs′ ys′
  = prove 6 ((var 0F ⊕ var 1F) ⊕ (var 2F ⊕ var 3F) ⊕ var 4F ⊕ var 5F)
            ((var 0F ⊕ var 2F ⊕ var 4F) ⊕ (var 1F ⊕ var 3F ⊕ var 5F))
            (b ∷ b′ ∷ tvarset-non-empty xs ∷ tvarset-non-empty ys ∷ tvarset-non-empty xs′ ∷ (tvarset-non-empty ys′) ∷ emp)
  where
    open Solver (∨-idempotentCommutativeMonoid)

tvarset-non-empty-∪t-left : (xs ys : TVarSet S) → Truth (tvarset-non-empty xs) → Truth (tvarset-non-empty (xs ∪t ys))
tvarset-non-empty-∪t-left xs ys p rewrite tvarset-non-empty-∪t xs ys = Truth-left (tvarset-non-empty xs) (tvarset-non-empty ys) p

tvarset-non-empty-∪t-right : (xs ys : TVarSet S) → Truth (tvarset-non-empty ys) → Truth (tvarset-non-empty (xs ∪t ys))
tvarset-non-empty-∪t-right xs ys p rewrite tvarset-non-empty-∪t xs ys = Truth-right (tvarset-non-empty xs) (tvarset-non-empty ys) p

tvarset-empty : (S : Tree n) → Truth (not (tvarset-non-empty (tEmp {S = S})))
tvarset-empty Sing = tt
tvarset-empty (Join S T) with tvarset-non-empty (tEmp {S = S}) | tvarset-empty S
... | false | p = tvarset-empty T

fromPath : (P : Path S) → TVarSet S
fromPath {S = Sing} PHere = VSSing true
fromPath {S = Join S T} PHere = VSJoin true tEmp tEmp
fromPath (PExt P) = VSJoin false (fromPath P) tEmp
fromPath (PShift P) = VSJoin false tEmp (fromPath P)

toVarSet : TVarSet S → VarSet (suc (tree-size S))
toVarSet (VSSing b) = b ∷ emp
toVarSet (VSJoin b vs xs) = connect-susp-supp (if tvarset-non-empty vs then suspSupp (toVarSet vs) else if b then trueAt (fromℕ _) else empty ) (toVarSet xs)

tEmp-empty : (S : Tree n) → tvarset-non-empty (tEmp {S = S}) ≡ false
tEmp-empty Sing = refl
tEmp-empty (Join S T) = cong₂ _∨_ (tEmp-empty S) (tEmp-empty T)

toVarSet-emp : (S : Tree n) → toVarSet (tEmp {S = S}) ≡ empty {n = suc n}
toVarSet-emp Sing = refl
toVarSet-emp (Join S T) rewrite tEmp-empty S = trans (cong (connect-susp-supp empty) (toVarSet-emp T)) (connect-supp-empty (suc (suc _)) get-snd _)

tFull-non-empty : (S : Tree n) → tvarset-non-empty (tFull {S = S}) ≡ true
tFull-non-empty Sing = refl
tFull-non-empty (Join S T) = refl

toVarSet-full : (S : Tree n) → toVarSet (tFull {S = S}) ≡ full {n = suc n}
toVarSet-full Sing = refl
toVarSet-full (Join S T)
  rewrite tFull-non-empty S = begin
  connect-susp-supp (suspSupp (toVarSet (tFull {S = S}))) (toVarSet (tFull {S = T}))
    ≡⟨ cong₂ connect-susp-supp (cong suspSupp (toVarSet-full S)) (toVarSet-full T) ⟩
  connect-susp-supp (suspSupp full) full
    ≡⟨ cong (λ - → connect-susp-supp - full) suspSuppFull ⟩
  connect-susp-supp full full
    ≡⟨ connect-supp-full (2 + tree-size S) get-snd (tree-size T) ⟩
  full ∎
  where
    open ≡-Reasoning

tvarset-truth-empty : (xs : TVarSet S) → Truth (not (tvarset-non-empty xs)) → xs ≡ tEmp
tvarset-truth-empty (VSSing false) p = refl
tvarset-truth-empty (VSJoin false xs xs′) p = cong₂ (VSJoin false) (tvarset-truth-empty xs (Truth-not-left _ _ p)) (tvarset-truth-empty xs′ (Truth-not-right _ _ p))

tvarset-maybe-empty : (xs : TVarSet S) → if (tvarset-non-empty xs) then ⊤ else xs ≡ tEmp
tvarset-maybe-empty xs with tvarset-non-empty xs | inspect tvarset-non-empty xs
... | true | y = tt
... | false | y = tvarset-truth-empty xs (Truth-prop′ (cong not (y .eq)))

tvarset-compat-1 : (xs : TVarSet S) → Truth (tvarset-non-empty xs) → Truth (varset-non-empty (toVarSet xs))
tvarset-compat-1 (VSSing true) t = tt
tvarset-compat-1 (VSJoin {n} b xs xs′) t with tvarset-non-empty xs | tvarset-maybe-empty xs | b
... | false | p | false = connect-susp-supp-non-empty-right empty (toVarSet xs′) (tvarset-compat-1 xs′ t)
... | false | p | true = connect-susp-supp-non-empty-left (FVTm get-fst) (toVarSet xs′) (trueAt-non-empty (fromℕ n))
... | true | p | b = connect-susp-supp-non-empty-left (suspSupp (toVarSet xs)) (toVarSet xs′) (suspSupp-non-empty (toVarSet xs))

tvarset-non-empty-compat : (xs : TVarSet S) → tvarset-non-empty xs ≡ varset-non-empty (toVarSet xs)
tvarset-non-empty-compat {n} {S = S} xs with tvarset-non-empty xs | tvarset-maybe-empty xs | tvarset-compat-1 xs
... | false | refl | x = begin
  false
    ≡˘⟨ empty-is-empty {n = suc n} ⟩
  varset-non-empty (empty {n = suc n})
    ≡˘⟨ cong varset-non-empty (toVarSet-emp S) ⟩
  varset-non-empty (toVarSet (tEmp {S = S})) ∎
  where open ≡-Reasoning
... | true | p | x with varset-non-empty (toVarSet xs) | x tt
... | true | x = refl

toVarSet-∪t : (xs ys : TVarSet S) → toVarSet (xs ∪t ys) ≡ toVarSet xs ∪ toVarSet ys
toVarSet-∪t (VSSing b) (VSSing b′) = refl
toVarSet-∪t {S = Join S T} (VSJoin b xs xs′) (VSJoin b′ ys ys′) = begin
  connect-susp-supp
      (if tvarset-non-empty (xs ∪t ys) then
       suspSupp (toVarSet (xs ∪t ys)) else
       (if b ∨ b′ then trueAt (fromℕ _) else empty))
      (toVarSet (xs′ ∪t ys′))
    ≡⟨ cong₂ (λ x y → connect-susp-supp (if x then suspSupp y else (if b ∨ b′ then trueAt (fromℕ _) else empty)) (toVarSet (xs′ ∪t ys′))) (tvarset-non-empty-∪t xs ys) (toVarSet-∪t xs ys) ⟩
  connect-susp-supp
    (if tvarset-non-empty xs ∨ tvarset-non-empty ys then
     suspSupp (toVarSet xs ∪ toVarSet ys) else
     (if b ∨ b′ then trueAt (fromℕ (suc (suc _))) else empty))
    (toVarSet (xs′ ∪t ys′))
    ≡⟨ cong₂ connect-susp-supp (lem b b′) (toVarSet-∪t xs′ ys′) ⟩
  connect-susp-supp
    ((if tvarset-non-empty xs then suspSupp (toVarSet xs) else
      (if b then trueAt (fromℕ (suc (suc _))) else empty))
     ∪
     (if tvarset-non-empty ys then suspSupp (toVarSet ys) else
      (if b′ then trueAt (fromℕ (suc (suc _))) else empty)))
    (toVarSet xs′ ∪ toVarSet ys′)
    ≡˘⟨ connect-supp-∪ _ _ (toVarSet xs′) (toVarSet ys′) get-snd ⟩
  connect-susp-supp
      (if tvarset-non-empty xs then suspSupp (toVarSet xs) else
       (if b then trueAt (fromℕ _) else empty))
      (toVarSet xs′)
      ∪
      connect-susp-supp
      (if tvarset-non-empty ys then suspSupp (toVarSet ys) else
       (if b′ then trueAt (fromℕ _) else empty))
      (toVarSet ys′) ∎
  where
    open ≡-Reasoning

    l1 : (b : Bool) → (zs : VarSet n) → (if b then trueAt (fromℕ _) else empty) ⊆ suspSupp zs
    l1 false zs = ⊆-bot (suspSupp zs)
    l1 true zs = lookup-isVar-⊆ (suspSupp zs) (Var (fromℕ _)) (suspSuppFstTruth zs)

    lem : (b b′ : Bool) → (if tvarset-non-empty xs ∨ tvarset-non-empty ys then
             suspSupp (toVarSet xs ∪ toVarSet ys) else
             (if b ∨ b′ then trueAt (fromℕ (suc (suc _))) else empty))
            ≡
            (if tvarset-non-empty xs then suspSupp (toVarSet xs) else
             (if b then trueAt (fromℕ (suc (suc _))) else empty))
            ∪
            (if tvarset-non-empty ys then suspSupp (toVarSet ys) else
             (if b′ then trueAt (fromℕ (suc (suc _))) else empty))
    lem b b′ with tvarset-non-empty xs | tvarset-maybe-empty xs | tvarset-non-empty ys | tvarset-maybe-empty ys | b | b′
    ... | false | q | false | s | false | b′ = sym (∪-left-unit _)
    ... | false | q | false | s | true | false = sym (∪-right-unit (trueAt (fromℕ _)))
    ... | false | q | false | s | true | true = sym (∪-idem (trueAt (fromℕ _)))
    ... | false | refl | true | s | b | b′ = begin
      suspSupp (toVarSet (tEmp {S = S}) ∪ toVarSet ys)
        ≡⟨ cong (λ - → suspSupp (- ∪ toVarSet ys)) (toVarSet-emp S) ⟩
      suspSupp (empty ∪ toVarSet ys)
        ≡⟨ cong suspSupp (∪-left-unit (toVarSet ys)) ⟩
      suspSupp (toVarSet ys)
        ≡⟨ l1 b (toVarSet ys) ⟩
      suspSupp (toVarSet ys) ∪ (if b then trueAt (fromℕ (suc (suc (tree-size S)))) else empty)
        ≡⟨ ∪-comm (suspSupp (toVarSet ys)) (if b then trueAt (fromℕ (suc (suc (tree-size S)))) else empty) ⟩
      (if b then trueAt (fromℕ _) else empty) ∪ suspSupp (toVarSet ys) ∎
    ... | true | q | false | refl | b | b′ = begin
      suspSupp (toVarSet xs ∪ toVarSet (tEmp {S = S}))
        ≡⟨ cong (λ - → suspSupp (toVarSet xs ∪ -)) (toVarSet-emp S) ⟩
      suspSupp (toVarSet xs ∪ empty)
        ≡⟨ cong suspSupp (∪-right-unit (toVarSet xs)) ⟩
      suspSupp (toVarSet xs)
        ≡⟨ l1 b′ (toVarSet xs) ⟩
      suspSupp (toVarSet xs) ∪ (if b′ then trueAt (fromℕ _) else empty) ∎
    ... | true | q | true | s | b | b′ = sym (suspSupp∪ (toVarSet xs) (toVarSet ys))

fromPath-PHere : (S : Tree n) → toVarSet (fromPath (PHere {S = S})) ≡ trueAt (fromℕ _)
fromPath-PHere Sing = refl
fromPath-PHere (Join S T) rewrite tEmp-empty S = begin
  connect-susp-supp (trueAt (fromℕ _)) (toVarSet (tEmp {S = T}))
    ≡⟨ cong (connect-susp-supp (trueAt (fromℕ _))) (toVarSet-emp T) ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc _)))) empty
    ≡⟨ connect-supp-fst get-snd (tree-size T) ⟩
  trueAt (fromℕ ((tree-size T) + suc (suc (tree-size S)))) ∎
  where
    open ≡-Reasoning

fromPath-last-path : (S : Tree n) → toVarSet (fromPath (last-path S)) ≡ FVTm (tree-last-var S)
fromPath-last-path Sing = refl
fromPath-last-path (Join S T) rewrite tEmp-empty S = begin
  connect-susp-supp empty (toVarSet (fromPath (last-path T)))
    ≡⟨ cong (connect-susp-supp empty) (fromPath-last-path T) ⟩
  connect-susp-supp empty (FVTm (tree-last-var T))
    ≡˘⟨ connect-supp-inc-right get-snd (FVTm (tree-last-var T)) ⟩
  TransportVarSet (FVTm (tree-last-var T))
    (connect-susp-inc-right _ _)
    ≡⟨ TransportVarSet-tm (tree-last-var T) (connect-susp-inc-right _ _) ⟩
  FVTm (tree-last-var T [ connect-susp-inc-right (tree-size S) (tree-size T) ]tm) ∎
  where
    open ≡-Reasoning

supp-tree-bd : (d : ℕ) → (T : Tree n) → (b : Bool) → TVarSet T
supp-tree-bd zero T false = fromPath PHere
supp-tree-bd zero T true = fromPath (last-path T)
supp-tree-bd (suc d) Sing b = tFull
supp-tree-bd (suc d) (Join S T) b = VSJoin true (supp-tree-bd d S b) (supp-tree-bd (suc d) T b)

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

supp-compat′ : (d : ℕ) → (T : Tree n) → (b : Bool) → toVarSet (supp-tree-bd d T b) ≡ pd-bd-supp d ⌊ T ⌋ ⦃ tree-to-pd T ⦄ b
supp-compat′ zero T false = trans (fromPath-PHere T) (lem ⌊ T ⌋ ⦃ pd-to-pdb (tree-to-pd T) ⦄)
  where
    lem : (Γ : Ctx (suc m)) → .⦃ pdb : Γ ⊢pdb ⦄ → trueAt (fromℕ m) ≡ pdb-bd-supp zero Γ false
    lem (∅ , A) = refl
    lem (∅ , B , A) = ⊥-elim (pdb-odd-length it)
    lem (Γ , C , B , A) with <-cmp zero (ty-dim B)
    ... | tri< a ¬b ¬c = cong ewf (cong ewf (lem (Γ , C) ⦃ pdb-prefix it ⦄))
    ... | tri≈ ¬a b ¬c = cong ewf (cong ewf (lem (Γ , C) ⦃ pdb-prefix it ⦄))
supp-compat′ zero T true = let
  instance _ = tree-to-pd T
  in begin
  toVarSet (fromPath (last-path T))
    ≡⟨ fromPath-last-path T ⟩
  FVTm (tree-last-var T)
    ≡˘⟨ FVTm-≃ (tree-to-pd-focus-tm T) ⟩
  FVTm (pd-focus-tm (tree-to-pd T))
    ≡˘⟨ FVTm-≃ (pd-right-base it) ⟩
  FVTm (pdb-right-base (pd-to-pdb it))
    ≡⟨ lem ⌊ T ⌋ (pd-to-pdb it) ⟩
  pd-bd-supp zero ⌊ T ⌋ true ∎
   where
    open ≡-Reasoning

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
supp-compat′ (suc d) Sing b = refl
supp-compat′ (suc d) (Join S T) b rewrite Truth-prop (supp-tree-bd-non-empty d S b) = let
  instance _ = tree-to-pd S
  instance _ = susp-pd (tree-to-pd S)
  instance _ = tree-to-pd T
  instance _ = tree-to-pd (Join S T)
  in begin
  connect-susp-supp (suspSupp (toVarSet (supp-tree-bd d S b))) (toVarSet (supp-tree-bd (suc d) T b))
    ≡⟨ cong₂ connect-susp-supp (cong suspSupp (supp-compat′ d S b)) (supp-compat′ (suc d) T b) ⟩
  connect-susp-supp (suspSupp (pd-bd-supp d ⌊ S ⌋ b)) (pd-bd-supp (suc d) ⌊ T ⌋ b)
    ≡⟨ connect-susp-pdb-bd-compat d ⌊ S ⌋ ⌊ T ⌋ ⦃ pd-to-pdb it ⦄ b ⟩
  pd-bd-supp (suc d) (connect-susp ⌊ S ⌋ ⌊ T ⌋) b ∎
  where
    open ≡-Reasoning

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
    ≡˘⟨ if-float (λ a → lookup a (fromℕ _)) (tvarset-non-empty xs) ⟩
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
          ewf ((if varset-non-empty xs then suspSupp xs else (if b then trueAt (fromℕ (suc _)) else replicate _ false)) ∪ FVTm get-snd)
            ≡⟨ cong (_∪ FVTm get-snd) (if-float ewf (varset-non-empty xs)) ⟩
          (if varset-non-empty xs then ewf (suspSupp xs) else ewf (if b then trueAt (fromℕ (suc _)) else replicate _ false)) ∪ FVTm get-snd
            ≡⟨ cong (λ a → (if varset-non-empty xs then ewf (suspSupp xs) else a) ∪ FVTm get-snd) (if-float ewf b) ⟩
          (if varset-non-empty xs then ewf (suspSupp xs) else (if b then FVTm get-fst else empty)) ∪ FVTm get-snd
            ≡⟨ p ⟩
          (if varset-non-empty ys then ewf (suspSupp ys) else (if b′ then FVTm get-fst else empty)) ∪ FVTm get-snd
            ≡˘⟨ cong (λ a → (if varset-non-empty ys then ewf (suspSupp ys) else a) ∪ FVTm get-snd) (if-float ewf b′) ⟩
          (if varset-non-empty ys then ewf (suspSupp ys) else ewf (if b′ then trueAt (fromℕ (suc _)) else replicate _ false)) ∪ FVTm get-snd
            ≡˘⟨ cong (_∪ FVTm get-snd) (if-float ewf (varset-non-empty ys)) ⟩
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
            ≡˘⟨ cong (if varset-non-empty (ewf xs) then false else_) (if-float (λ a → lookup a 0F) b) ⟩
          (if varset-non-empty (ewf xs) then false else lookup (if b then FVTm get-fst else empty) 0F)
            ≡˘⟨ if-float (λ a → lookup a 0F) (varset-non-empty (ewf xs)) ⟩
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
            ≡⟨ if-float (λ a → lookup a 0F) (varset-non-empty ys) ⟩
          (if varset-non-empty ys then false else lookup (if b′ then FVTm get-fst else empty) 0F)
            ≡⟨ cong (if varset-non-empty ys then false else_) (if-float (λ a → lookup a 0F) b′) ⟩
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
                ≡˘⟨ if-float (λ a → lookup a (fromℕ (2 + n))) b ⟩
              lookup (if b then trueAt (fromℕ (suc (suc n))) else empty) (fromℕ (suc (suc n)))
                ≡˘⟨ connect-susp-supp-fst-var (if b then trueAt (fromℕ _) else empty) (toVarSet xs′) ⟩
              lookup (connect-susp-supp (if b then trueAt (fromℕ _) else empty) (toVarSet xs′)) (fromℕ _)
                ≡⟨ cong (λ a → lookup a (fromℕ _)) p ⟩
              lookup (connect-susp-supp (if b′ then trueAt (fromℕ _) else empty) (toVarSet ys′)) (fromℕ _)
                ≡⟨ connect-susp-supp-fst-var (if b′ then trueAt (fromℕ _) else empty) (toVarSet ys′) ⟩
              lookup (if b′ then trueAt (fromℕ (suc (suc n))) else empty) (fromℕ (suc (suc n)))
                ≡⟨ if-float (λ a → lookup a (fromℕ (2 + n))) b′ ⟩
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
                (suc m ↑ʳ inject₁ (fromℕ n))
                ≡⟨ cong (λ a → lookup a (suc m ↑ʳ inject₁ (fromℕ n))) p ⟩
              lookup (connect-susp-supp (if b′ then ewf (ewf (trueAt (fromℕ n))) else empty) (toVarSet ys′))
                (suc m ↑ʳ inject₁ (fromℕ n))
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

supp-tvarset : TVarSet S → TVarSet (Susp S)
supp-tvarset xs = VSJoin true xs (VSSing true)

supp-tvarset-DCT : (xs : TVarSet S) → DCT (supp-tvarset xs) ≡ supp-tvarset (DCT xs)
supp-tvarset-DCT xs = cong (VSJoin true (DCT xs)) (if-lem-const (tvarset-non-empty xs) (set-fst-true (DCT (VSSing true))))
