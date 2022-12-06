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
import Algebra.Solver.IdempotentCommutativeMonoid as Solver

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

  ∪t-monoid : Monoid _ _
  ∪t-monoid = record
    { isMonoid = ∪t-isMonoid }

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
toVarSet-emp (Join S T) rewrite tEmp-empty S = trans (cong (connect-susp-supp empty) (toVarSet-emp T)) (connect-supp-empty (suc (suc _)) getSnd _)

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
    ≡⟨ connect-supp-full (2 + tree-size S) getSnd (tree-size T) ⟩
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
    ≡˘⟨ connect-supp-∪ _ _ (toVarSet xs′) (toVarSet ys′) getSnd ⟩
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
    ≡⟨ connect-supp-fst getSnd (tree-size T) ⟩
  trueAt (fromℕ ((tree-size T) + suc (suc (tree-size S)))) ∎
  where
    open ≡-Reasoning

fromPath-last-path : (S : Tree n) → toVarSet (fromPath (last-path S)) ≡ FVTm (tree-last-var S)
fromPath-last-path Sing = refl
fromPath-last-path (Join S T) rewrite tEmp-empty S = begin
  connect-susp-supp empty (toVarSet (fromPath (last-path T)))
    ≡⟨ cong (connect-susp-supp empty) (fromPath-last-path T) ⟩
  connect-susp-supp empty (FVTm (tree-last-var T))
    ≡˘⟨ connect-supp-inc-right getSnd (FVTm (tree-last-var T)) ⟩
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

supp-compat′ : (d : ℕ) → (T : Tree n) → (b : Bool) → toVarSet (supp-tree-bd d T b) ≡ pd-bd-supp d (tree-to-ctx T) ⦃ tree-to-pd T ⦄ b
supp-compat′ zero T false = trans (fromPath-PHere T) (lem (tree-to-ctx T) ⦃ pd-to-pdb (tree-to-pd T) ⦄)
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
    ≡⟨ lem (tree-to-ctx T) (pd-to-pdb it) ⟩
  pd-bd-supp zero (tree-to-ctx T) true ∎
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
      FVTm (liftTerm (liftTerm (pdb-right-base (pdb-prefix pdb))))
        ≡⟨ supp-lift-tm (liftTerm (pdb-right-base (pdb-prefix pdb))) ⟩
      ewf (FVTm (liftTerm (pdb-right-base (pdb-prefix pdb))))
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
  connect-susp-supp (suspSupp (pd-bd-supp d (tree-to-ctx S) b)) (pd-bd-supp (suc d) (tree-to-ctx T) b)
    ≡⟨ connect-susp-pdb-bd-compat d (tree-to-ctx S) (tree-to-ctx T) ⦃ pd-to-pdb it ⦄ b ⟩
  pd-bd-supp (suc d) (connect-susp (tree-to-ctx S) (tree-to-ctx T)) b ∎
  where
    open ≡-Reasoning

set-fst-true : TVarSet S → TVarSet S
set-fst-true (VSSing b) = VSSing true
set-fst-true (VSJoin b xs ys) = VSJoin true xs ys

DCT : TVarSet S → TVarSet S
DCT (VSSing b) = VSSing b
DCT (VSJoin b xs ys) = VSJoin (b ∨ tvarset-non-empty xs) (DCT xs) (if tvarset-non-empty xs then set-fst-true (DCT ys) else DCT ys)

DCT-non-empty : (xs : TVarSet S) → tvarset-non-empty (DCT xs) ≡ tvarset-non-empty xs
DCT-non-empty (VSSing b) = refl
DCT-non-empty (VSJoin b xs ys) rewrite DCT-non-empty xs with tvarset-non-empty xs
... | false = cong₂ _∨_ (∨-identityʳ b) (DCT-non-empty ys)
... | true = trans (∨-zeroʳ (b ∨ true)) (sym (∨-zeroʳ b))

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
    ≡˘⟨ connect-supp-∪ (trueAt (fromℕ (suc (suc _)))) (if b then trueAt (fromℕ (suc (suc _))) else empty) empty (toVarSet ys) getSnd ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc _)))) empty
  ∪ connect-susp-supp (if b then trueAt (fromℕ (suc (suc _))) else empty) (toVarSet ys)
    ≡⟨ cong (_∪ connect-susp-supp (if b then trueAt (fromℕ _) else empty) (toVarSet ys)) (connect-supp-fst getSnd (tree-size T)) ⟩
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
    ≡˘⟨ cong₂ connect-susp-supp (trans (∪-comm _ _) (sym (lookup-isVar-⊆ (suspSupp (toVarSet xs)) getFst (suspSuppFstTruth (toVarSet xs))))) (∪-left-unit (toVarSet ys)) ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc _))) ∪ suspSupp (toVarSet xs)) (empty ∪ toVarSet ys)
    ≡˘⟨ connect-supp-∪ (trueAt (fromℕ (suc (suc _)))) (suspSupp (toVarSet xs)) empty (toVarSet ys) getSnd ⟩
  connect-susp-supp (trueAt (fromℕ (suc (suc _)))) empty ∪
    connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet ys)
    ≡⟨ cong (_∪ connect-susp-supp (suspSupp (toVarSet xs)) (toVarSet ys)) (connect-supp-fst getSnd (tree-size T)) ⟩
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
