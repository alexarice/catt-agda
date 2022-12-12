module Catt.Tree.Label.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Path
open import Catt.Tree.Pasting
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Connection.Support
open import Catt.Tree.Support
open import Catt.Tree
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Catt.Connection
open import Algebra.Definitions
open import Algebra.Bundles
open import Tactic.MonoidSolver

MVarSet : (X : MaybeTree n) → Set
MVarSet (someTree x) = TVarSet x
MVarSet (Other n) = VarSet n

infixl 60 _∪m_
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

FVLabel′-map : {X : MaybeTree n}
             → {Y : MaybeTree m}
             → (f : (P : Path S) → MVarSet X)
             → (g : MVarSet X → MVarSet Y)
             → (∀ xs ys → g (xs ∪m ys) ≡ g xs ∪m g ys)
             → FVLabel′ (g ∘ f) ≡ g (FVLabel′ f)
FVLabel′-map {S = Sing} f g p = refl
FVLabel′-map {S = Join S T} f g p = begin
  g (f PHere) ∪m FVLabel′ (g ∘ f ∘ PExt) ∪m FVLabel′ (g ∘ f ∘ PShift)
    ≡⟨ cong₂ (λ a b → g (f PHere) ∪m a ∪m b) (FVLabel′-map (f ∘ PExt) g p) (FVLabel′-map (f ∘ PShift) g p) ⟩
  g (f PHere) ∪m g (FVLabel′ (f ∘ PExt)) ∪m g (FVLabel′ (f ∘ PShift))
    ≡˘⟨ cong (_∪m g (FVLabel′ (f ∘ PShift))) (p (f PHere) (FVLabel′ (f ∘ PExt))) ⟩
  g (f PHere ∪m FVLabel′ (f ∘ PExt)) ∪m g (FVLabel′ (f ∘ PShift))
    ≡˘⟨ p (f PHere ∪m FVLabel′ (f ∘ PExt)) (FVLabel′ (f ∘ PShift)) ⟩
  g (f PHere ∪m FVLabel′ (f ∘ PExt) ∪m FVLabel′ (f ∘ PShift)) ∎
  where
    open ≡-Reasoning

supp-condition-s : (b : Bool) → (S : Tree n) → (As : STy (someTree S)) → Set
supp-condition-s false S As = FVSTy As ≡ mFull
supp-condition-s true S S⋆ = ⊥
supp-condition-s true S (SArr s As t) = NonZero (tree-dim S)
                                      × DCT (FVSTm s) ≡ supp-tree-bd (pred (tree-dim S)) S false
                                      × DCT (FVSTm t) ≡ supp-tree-bd (pred (tree-dim S)) S true

label-ap-⊆ : {X : MaybeTree n} → (L : Label X S) → (P : Path S) → FVLabel L ≡ FVLabel L ∪m FVSTm (L P)
label-ap-⊆ {S = Sing} L PHere = sym (∪m-idem (FVSTm (L PHere)))
label-ap-⊆ {S = Join S T} {X = X} L PHere = begin
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)
    ≡˘⟨ cong (λ - → - ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)) (∪m-idem (FVSTm (L PHere))) ⟩
  (FVSTm (L PHere) ∪m FVSTm (L PHere)) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  FVSTm (L PHere) ∪m (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift))
    ≡⟨ ∪m-comm (FVSTm (L PHere)) _ ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift) ∪m FVSTm (L PHere) ∎
  where
    open ≡-Reasoning
label-ap-⊆ {S = Join S T} {X = X} L (PExt P) = begin
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)
    ≡⟨ cong (λ x → FVSTm (L PHere) ∪m x ∪m FVLabel (L ∘ PShift)) (label-ap-⊆ (L ∘ PExt) P) ⟩
  FVSTm (L PHere) ∪m (FVLabel (L ∘ PExt) ∪m FVSTm (L (PExt P))) ∪m FVLabel (L ∘ PShift)
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m (FVSTm (L (PExt P)) ∪m FVLabel (L ∘ PShift))
    ≡⟨ cong (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m_) (∪m-comm _ _) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m (FVLabel (L ∘ PShift) ∪m FVSTm (L (PExt P)))
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift) ∪m FVSTm (L (PExt P)) ∎
  where
    open ≡-Reasoning
label-ap-⊆ {S = Join S T} {X = X} L (PShift P) = begin
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift)
    ≡⟨ cong (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m_) (label-ap-⊆ (L ∘ PShift) P) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m (FVLabel (L ∘ PShift) ∪m FVSTm (L (PShift P)))
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift) ∪m FVSTm (L (PShift P)) ∎
  where
    open ≡-Reasoning

MtoVarSet : (ΓS : CtxOrTree n) → MVarSet (COT-to-MT ΓS) → VarSet n
MtoVarSet (incTree _) xs = toVarSet xs
MtoVarSet (incCtx Γ) xs = DC Γ xs

FVLabel-non-empty : (L : Label (someTree T) S) → Truth (tvarset-non-empty (FVLabel L))
FVSTm-non-empty : (a : STm (someTree S)) → Truth (tvarset-non-empty (FVSTm a))

FVLabel-non-empty {S = Sing} L = FVSTm-non-empty (L PHere)
FVLabel-non-empty {S = Join S T} L = tvarset-non-empty-∪t-left (FVSTm (L PHere) ∪t FVLabel (L ∘ PExt)) (FVLabel (L ∘ PShift))
                                       (tvarset-non-empty-∪t-left (FVSTm (L PHere)) (FVLabel (L ∘ PExt)) (FVSTm-non-empty (L PHere)))

FVSTm-non-empty (SCoh S A L) = tvarset-non-empty-∪t-right (FVSTy (lty L)) (FVLabel (ap L)) (FVLabel-non-empty (ap L))
FVSTm-non-empty {S = Join S T} (SExt a) = Truth-left (tvarset-non-empty (FVSTm a)) (tvarset-non-empty (tEmp {S = T})) (FVSTm-non-empty a)
FVSTm-non-empty {S = Join S T} (SShift a) = Truth-right (tvarset-non-empty (tEmp {S = S})) (tvarset-non-empty (FVSTm a))
                                              (FVSTm-non-empty a)
FVSTm-non-empty (SPath P) = fromPath-non-empty P

MtoVarSet-∪m : {ΓS : CtxOrTree n} (xs ys : MVarSet (COT-to-MT ΓS)) → MtoVarSet ΓS (xs ∪m ys) ≡ MtoVarSet ΓS xs ∪ MtoVarSet ΓS ys
MtoVarSet-∪m {ΓS = incTree x} xs ys = toVarSet-∪t xs ys
MtoVarSet-∪m {ΓS = incCtx Γ} xs ys = DC-∪ Γ xs ys

MtoVarSet-emp : (ΓS : CtxOrTree n) → MtoVarSet ΓS mEmp ≡ empty
MtoVarSet-emp (incTree S) = toVarSet-emp S
MtoVarSet-emp (incCtx Γ) = DC-empty Γ

open ≡-Reasoning

fromPath-to-term : (P : Path S) → toVarSet (fromPath P) ≡ SuppTm (tree-to-ctx S) (path-to-term P)
fromPath-to-term {S = S} PHere = begin
  toVarSet (fromPath (PHere {S = S}))
    ≡⟨ fromPath-PHere S ⟩
  trueAt (fromℕ _)
    ≡˘⟨ DC-fromℕ (tree-to-ctx S) ⟩
  SuppTm (tree-to-ctx S) (Var (fromℕ _)) ∎
fromPath-to-term {S = Join S T} (PExt P) rewrite Truth-prop (fromPath-non-empty P) = begin
  connect-susp-supp (suspSupp (toVarSet (fromPath P))) (toVarSet (tEmp {S = T}))
    ≡⟨ cong₂ (λ x y → connect-susp-supp (suspSupp x) y) (fromPath-to-term P) (toVarSet-emp T) ⟩
  connect-susp-supp (suspSupp (SuppTm (tree-to-ctx S) (path-to-term P))) empty
    ≡⟨ connect-susp-supp-ext (tree-to-ctx S) (path-to-term P) (tree-to-ctx T) ⟩
  SuppTm (tree-to-ctx (Join S T)) (suspTm (path-to-term P) [ connect-susp-inc-left _ _ ]tm) ∎
fromPath-to-term {S = Join S T} (PShift P) rewrite Truth-not-prop (tvarset-empty S) = begin
  connect-susp-supp empty (toVarSet (fromPath P))
    ≡⟨ cong (connect-susp-supp empty) (fromPath-to-term P) ⟩
  connect-susp-supp empty (SuppTm (tree-to-ctx T) (path-to-term P))
    ≡⟨ connect-susp-supp-shift (tree-to-ctx S) (tree-to-ctx T) (path-to-term P) ⟩
  SuppTm (connect-susp (tree-to-ctx S) (tree-to-ctx T)) (path-to-term P [ connect-susp-inc-right _ _ ]tm) ∎

FVSTm-to-term : {ΓS : CtxOrTree n} → (a : STm (COT-to-MT ΓS)) → MtoVarSet ΓS (FVSTm a) ≡ SuppTm (COT-to-Ctx ΓS) (stm-to-term a)
FVSTy-to-type : {ΓS : CtxOrTree n} → (A : STy (COT-to-MT ΓS)) → MtoVarSet ΓS (FVSTy A) ≡ SuppTy (COT-to-Ctx ΓS) (sty-to-type A)
FVLabel-to-sub : {ΓS : CtxOrTree n} → (L : Label-WT (COT-to-MT ΓS) S) → MtoVarSet ΓS (FVLabel-WT L) ≡ SuppSub (COT-to-Ctx ΓS) (label-to-sub L)
FVLabel-to-sub′ : {ΓS : CtxOrTree n}
                → (L : Label-WT (COT-to-MT ΓS) S)
                → ((P : Path S)
                → MtoVarSet ΓS (FVSTm (ap L P)) ≡ SuppTm (COT-to-Ctx ΓS) (stm-to-term (ap L P)))
                → (MtoVarSet ΓS (FVSTy (lty L)) ≡ SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty L)))
                → MtoVarSet ΓS (FVLabel-WT L) ≡ SuppSub (COT-to-Ctx ΓS) (label-to-sub L)

FVSTm-to-term {ΓS = incTree x} (SPath P) = fromPath-to-term P
FVSTm-to-term {ΓS = incTree x} (SCoh S A L) = begin
  toVarSet (FVLabel-WT L)
    ≡⟨ FVLabel-to-sub L ⟩
  SuppSub (tree-to-ctx x) (label-to-sub L)
    ≡˘⟨ cong (DC (tree-to-ctx x)) (coh-sub-fv (tree-to-ctx S) (sty-to-type A) (label-to-sub L)) ⟩
  SuppTm (tree-to-ctx x) (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) ∎
FVSTm-to-term {ΓS = incCtx Γ} (SCoh S A L) = begin
  DC Γ (FVLabel-WT L)
    ≡⟨ FVLabel-to-sub L ⟩
  SuppSub Γ (label-to-sub L)
    ≡˘⟨ cong (DC Γ) (coh-sub-fv (tree-to-ctx S) (sty-to-type A) (label-to-sub L)) ⟩
  SuppTm Γ (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) ∎
FVSTm-to-term {ΓS = incCtx _} (SOther t) = refl
FVSTm-to-term {ΓS = incTree (Join S T)} (SExt a) rewrite Truth-prop (FVSTm-non-empty a) = begin
  connect-susp-supp (suspSupp (toVarSet (FVSTm a))) (toVarSet (tEmp {S = T}))
    ≡⟨ cong₂ (λ x y → connect-susp-supp (suspSupp x) y) (FVSTm-to-term a) (toVarSet-emp T) ⟩
  connect-susp-supp (suspSupp (SuppTm (tree-to-ctx S) (stm-to-term a))) empty
    ≡⟨ connect-susp-supp-ext (tree-to-ctx S) (stm-to-term a) (tree-to-ctx T) ⟩
  SuppTm (tree-to-ctx (Join S T)) (suspTm (stm-to-term a) [ connect-susp-inc-left _ _ ]tm) ∎
FVSTm-to-term {ΓS = incTree (Join S T)} (SShift a) rewrite Truth-not-prop (tvarset-empty S) = begin
  connect-susp-supp empty (toVarSet (FVSTm a))
    ≡⟨ cong (connect-susp-supp empty) (FVSTm-to-term a) ⟩
  connect-susp-supp empty (SuppTm (tree-to-ctx T) (stm-to-term a))
    ≡⟨ connect-susp-supp-shift (tree-to-ctx S) (tree-to-ctx T) (stm-to-term a)  ⟩
  SuppTm (tree-to-ctx (Join S T)) (stm-to-term a [ connect-susp-inc-right _ _ ]tm) ∎

FVSTy-to-type {ΓS = ΓS} S⋆ = trans (MtoVarSet-emp ΓS) (sym (DC-empty (COT-to-Ctx ΓS)))
FVSTy-to-type {ΓS = ΓS} (SArr s A t) = begin
  MtoVarSet ΓS (FVSTy A ∪m FVSTm s ∪m FVSTm t)
    ≡⟨ MtoVarSet-∪m (FVSTy A ∪m FVSTm s) (FVSTm t) ⟩
  MtoVarSet ΓS (FVSTy A ∪m FVSTm s) ∪ MtoVarSet ΓS (FVSTm t)
    ≡⟨ cong₂ _∪_ (MtoVarSet-∪m (FVSTy A) (FVSTm s)) (FVSTm-to-term t) ⟩
  MtoVarSet ΓS (FVSTy A) ∪ MtoVarSet ΓS (FVSTm s) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)
    ≡⟨ cong₂ (λ x y → x ∪ y ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)) (FVSTy-to-type A) (FVSTm-to-term s) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type A) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term s) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)
    ≡˘⟨ cong (_∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)) (DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type A)) (FVTm (stm-to-term s))) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type A) ∪ FVTm (stm-to-term s)) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term t)
    ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type A) ∪ FVTm (stm-to-term s)) (FVTm (stm-to-term t)) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type A) ∪ FVTm (stm-to-term s) ∪ FVTm (stm-to-term t)) ∎

FVLabel-to-sub L = FVLabel-to-sub′ L (λ P → FVSTm-to-term (ap L P)) (FVSTy-to-type (lty L))

FVLabel-to-sub′ {S = Sing} {ΓS = ΓS} L f g = begin
   MtoVarSet ΓS (FVSTy (lty L) ∪m FVSTm (ap L PHere))
    ≡⟨ MtoVarSet-∪m (FVSTy (lty L)) (FVSTm (ap L PHere)) ⟩
  MtoVarSet ΓS (FVSTy (lty L)) ∪ MtoVarSet ΓS (FVSTm (ap L PHere))
    ≡⟨ cong₂ _∪_ g (f PHere) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type (proj₂ L))) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (proj₁ L PHere))
    ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L))) (FVTm (stm-to-term (ap L PHere))) ⟩
  DC (COT-to-Ctx ΓS) (FVTy (sty-to-type (lty L)) ∪ FVTm (stm-to-term (ap L PHere))) ∎
FVLabel-to-sub′ {S = Join S T} {ΓS = ΓS} L f g = begin
  MtoVarSet ΓS (FVSTy (lty L) ∪m ((FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt)) ∪m FVLabel (ap L ∘ PShift)))
    ≡⟨ cong (MtoVarSet ΓS) l1 ⟩
  MtoVarSet ΓS
    (FVSTy (lty L)
    ∪m FVSTm (ap L PHere)
    ∪m FVSTm (ap L (PShift PHere))
    ∪m FVLabel (ap L ∘ PExt)
    ∪m (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift)))
    ≡⟨ MtoVarSet-∪m (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
               ∪m FVLabel (ap L ∘ PExt)) (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift)) ⟩
  MtoVarSet ΓS (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
               ∪m FVLabel (ap L ∘ PExt))
  ∪ MtoVarSet ΓS (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift))
    ≡⟨⟩
  MtoVarSet ΓS (FVLabel-WT (label₁ L)) ∪ MtoVarSet ΓS (FVLabel-WT (label₂ L))
    ≡⟨ cong₂ _∪_ (FVLabel-to-sub′ (label₁ L) (f ∘ PExt) l2) (FVLabel-to-sub′ (label₂ L) (f ∘ PShift) g) ⟩
  SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₁ L)) ∪ SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₂ L))
    ≡˘⟨ cong (λ x → DC (COT-to-Ctx ΓS) x ∪ SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₂ L))) (unrestrict-supp (label-to-sub (label₁ L))) ⟩
  SuppSub (COT-to-Ctx ΓS) (unrestrict (label-to-sub (label₁ L))) ∪ SuppSub (COT-to-Ctx ΓS) (label-to-sub (label₂ L))
    ≡˘⟨ sub-from-connect-supp′ (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) l3 ⟩
  SuppSub (COT-to-Ctx ΓS)
          (sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                            (label-to-sub (label₂ L))) ∎
  where
    l1 : FVSTy (lty L) ∪m ((FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt)) ∪m FVLabel (ap L ∘ PShift))
       ≡ FVSTy (lty L)
       ∪m FVSTm (ap L PHere)
       ∪m FVSTm (ap L (PShift PHere))
       ∪m FVLabel (ap L ∘ PExt)
       ∪m (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift))
    l1 = begin
      FVSTy (lty L) ∪m (FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt) ∪m FVLabel (ap L ∘ PShift))
        ≡⟨ cong (λ - → FVSTy (lty L) ∪m (FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt) ∪m -)) (label-ap-⊆ (ap L ∘ PShift) PHere) ⟩
      FVSTy (lty L) ∪m (FVSTm (ap L PHere) ∪m FVLabel (ap L ∘ PExt) ∪m (FVLabel (ap L ∘ PShift) ∪m FVSTm (ap L (PShift PHere))))
        ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
      FVSTy (lty L)
      ∪m FVSTm (ap L PHere)
      ∪m ((FVLabel (ap L ∘ PExt) ∪m FVLabel (ap L ∘ PShift) )∪m FVSTm (ap L (PShift PHere)))
        ≡˘⟨ cong₂ (λ x y → x ∪m FVSTm (ap L PHere) ∪m y)
                 (∪m-idem (FVSTy (lty L)))
                 (∪m-comm _ _) ⟩
      (FVSTy (lty L) ∪m FVSTy (lty L))
      ∪m FVSTm (ap L PHere)
      ∪m (FVSTm (ap L (PShift PHere)) ∪m (FVLabel (ap L ∘ PExt) ∪m FVLabel (ap L ∘ PShift)))
        ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
      FVSTy (lty L) ∪m (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
      ∪m FVLabel (ap L ∘ PExt)) ∪m FVLabel (ap L ∘ PShift)
        ≡⟨ cong (_∪m FVLabel (ap L ∘ PShift)) (∪m-comm (FVSTy (lty L)) _) ⟩
      (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
      ∪m FVLabel (ap L ∘ PExt))
      ∪m FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift)
        ≡⟨ solve (∪m-monoid {X = COT-to-MT ΓS}) ⟩
      FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere))
      ∪m FVLabel (ap L ∘ PExt)
      ∪m (FVSTy (lty L) ∪m FVLabel (ap L ∘ PShift)) ∎

    l2 : MtoVarSet ΓS (FVSTy (lty (label₁ L))) ≡ SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty (label₁ L)))
    l2 = begin
      MtoVarSet ΓS (FVSTy (lty L) ∪m FVSTm (ap L PHere) ∪m FVSTm (ap L (PShift PHere)))
        ≡⟨ MtoVarSet-∪m (FVSTy (lty L) ∪m FVSTm (ap L PHere)) (FVSTm (ap L (PShift PHere))) ⟩
      MtoVarSet ΓS (FVSTy (lty L) ∪m FVSTm (ap L PHere)) ∪ MtoVarSet ΓS (FVSTm (ap L (PShift PHere)))
        ≡⟨ cong (_∪m MtoVarSet ΓS (FVSTm (ap L (PShift PHere)))) (MtoVarSet-∪m (FVSTy (lty L)) (FVSTm (ap L PHere))) ⟩
      MtoVarSet ΓS (FVSTy (lty L)) ∪ MtoVarSet ΓS (FVSTm (ap L PHere)) ∪m MtoVarSet ΓS (FVSTm (ap L (PShift PHere)))
        ≡⟨ cong₃ (λ x y z → x ∪ y ∪ z) g (f PHere) (f (PShift PHere)) ⟩
      SuppTy (COT-to-Ctx ΓS) (sty-to-type (lty L))
      ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (ap L PHere))
      ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (ap L (PShift PHere)))
        ≡˘⟨ cong (_∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (proj₁ L (PShift PHere))))
              (DC-∪ (COT-to-Ctx ΓS) _ _) ⟩
      DC (COT-to-Ctx ΓS) (FVTy (sty-to-type (proj₂ L)) ∪ FVTm (stm-to-term (proj₁ L PHere))) ∪ SuppTm (COT-to-Ctx ΓS) (stm-to-term (proj₁ L (PShift PHere)))
        ≡˘⟨ DC-∪ (COT-to-Ctx ΓS) _ _ ⟩
      SuppTy (COT-to-Ctx ΓS)
      (stm-to-term (ap L PHere) ─⟨ sty-to-type (lty L) ⟩⟶
       stm-to-term (ap L (PShift PHere))) ∎

    l3 : SuppTm (COT-to-Ctx ΓS) (Var (fromℕ _) [ label-to-sub (label₂ L) ]tm) ⊆ SuppSub (COT-to-Ctx ΓS) (unrestrict (label-to-sub (label₁ L)))
    l3 = PR.begin
      SuppTm (COT-to-Ctx ΓS) (Var (fromℕ _) [ label-to-sub (label₂ L) ]tm)
        ≈˘⟨ cong (DC (COT-to-Ctx ΓS)) (FVTm-≃ (label-to-sub-lem L)) ⟩
      SuppTm (COT-to-Ctx ΓS) (getSnd [ unrestrict (label-to-sub (label₁ L)) ]tm)
        ≤⟨ DC-cong-⊆ (COT-to-Ctx ΓS) (FVTm-comp-⊆ getSnd (unrestrict (label-to-sub (label₁ L)))) ⟩
      SuppSub (COT-to-Ctx ΓS) (unrestrict (label-to-sub (label₁ L))) PR.∎
      where
        module PR = PReasoning (⊆-poset _)
        open PR

supp-condition-compat : (b : Bool) → (S : Tree n) → (As : STy (someTree S)) → supp-condition-s b S As → supp-condition b (sty-to-type As) (tree-to-ctx S) ⦃ tree-to-pd S ⦄
supp-condition-compat false S As sc = begin
  SuppTy (tree-to-ctx S) (sty-to-type As)
    ≡˘⟨ FVSTy-to-type As ⟩
  toVarSet (FVSTy As)
    ≡⟨ cong toVarSet sc ⟩
  toVarSet (tFull {S = S})
    ≡⟨ toVarSet-full S ⟩
  full ∎
supp-condition-compat true S (SArr s As t) (nz ,, sc1 ,, sc2) = NonZero-subst lem nz ,, lem1 ,, lem2
  where
    lem : tree-dim S ≡ ctx-dim (tree-to-ctx S)
    lem = sym (tree-dim-ctx-dim S)

    instance _ = tree-to-pd S
    lem1 : SuppTm (tree-to-ctx S) (stm-to-term s)
         ≡ pd-bd-supp (pred (ctx-dim (tree-to-ctx S))) (tree-to-ctx S) false
    lem1 = begin
      SuppTm (tree-to-ctx S) (stm-to-term s)
        ≡˘⟨ FVSTm-to-term s ⟩
      toVarSet (FVSTm s)
        ≡˘⟨ DCT-toVarSet (FVSTm s) ⟩
      toVarSet (DCT (FVSTm s))
        ≡⟨ cong toVarSet sc1 ⟩
      toVarSet (supp-tree-bd (pred (tree-dim S)) S false)
        ≡⟨ cong (λ - → toVarSet (supp-tree-bd (pred -) S false)) lem  ⟩
      toVarSet (supp-tree-bd (pred (ctx-dim (tree-to-ctx S))) S false)
        ≡⟨ supp-compat′ (pred (ctx-dim (tree-to-ctx S))) S false ⟩
      pd-bd-supp (pred (ctx-dim (tree-to-ctx S))) (tree-to-ctx S) false ∎

    lem2 : SuppTm (tree-to-ctx S) (stm-to-term t)
         ≡ pd-bd-supp (pred (ctx-dim (tree-to-ctx S))) (tree-to-ctx S) true
    lem2 = begin
      SuppTm (tree-to-ctx S) (stm-to-term t)
        ≡˘⟨ FVSTm-to-term t ⟩
      toVarSet (FVSTm t)
        ≡˘⟨ DCT-toVarSet (FVSTm t) ⟩
      toVarSet (DCT (FVSTm t))
        ≡⟨ cong toVarSet sc2 ⟩
      toVarSet (supp-tree-bd (pred (tree-dim S)) S true)
        ≡⟨ cong (λ - → toVarSet (supp-tree-bd (pred -) S true)) lem  ⟩
      toVarSet (supp-tree-bd (pred (ctx-dim (tree-to-ctx S))) S true)
        ≡⟨ supp-compat′ (pred (ctx-dim (tree-to-ctx S))) S true ⟩
      pd-bd-supp (pred (ctx-dim (tree-to-ctx S))) (tree-to-ctx S) true ∎

DCM-reflect : {xs ys : MVarSet (COT-to-MT ΓS)} → MtoVarSet ΓS xs ≡ MtoVarSet ΓS ys → DCM ΓS xs ≡ DCM ΓS ys
DCM-reflect {ΓS = incTree x} p = DCT-reflect p
DCM-reflect {ΓS = incCtx x} p = p

DCM-∪ : (ΓS : CtxOrTree n) → (xs ys : MVarSet (COT-to-MT ΓS)) → DCM ΓS (xs ∪m ys) ≡ DCM ΓS xs ∪m DCM ΓS ys
DCM-∪ (incTree x) xs ys = DCT-∪ xs ys
DCM-∪ (incCtx x) xs ys = DC-∪ x xs ys

FVSTm-≃ : {a b : STm (COT-to-MT ΓS)} → a ≃stm b → DCM ΓS (FVSTm a) ≡ DCM ΓS (FVSTm b)
FVSTm-≃ {ΓS = ΓS} {a = a} {b = b} [ p ] = DCM-reflect (begin
  MtoVarSet ΓS (FVSTm a)
    ≡⟨ FVSTm-to-term a ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term a)
    ≡⟨ cong (SuppTm (COT-to-Ctx ΓS)) (≃tm-to-≡ p) ⟩
  SuppTm (COT-to-Ctx ΓS) (stm-to-term b)
    ≡˘⟨ FVSTm-to-term b ⟩
  MtoVarSet ΓS (FVSTm b) ∎)

FVSTy-≃ : {As Bs : STy (COT-to-MT ΓS)} → As ≃sty Bs → DCM ΓS (FVSTy As) ≡ DCM ΓS (FVSTy Bs)
FVSTy-≃ {ΓS = ΓS} {As = As} {Bs = Bs} [ p ] = DCM-reflect (begin
  MtoVarSet ΓS (FVSTy As)
    ≡⟨ FVSTy-to-type As ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type As)
    ≡⟨ cong (SuppTy (COT-to-Ctx ΓS)) (≃ty-to-≡ p) ⟩
  SuppTy (COT-to-Ctx ΓS) (sty-to-type Bs)
    ≡˘⟨ FVSTy-to-type Bs ⟩
  MtoVarSet ΓS (FVSTy Bs) ∎)

FVLabel-≃ : {L M : Label (COT-to-MT ΓS) S} → L ≃l M → DCM ΓS (FVLabel L) ≡ DCM ΓS (FVLabel M)
FVLabel-≃ {S = Sing} {L = L} {M = M} [ p ] = FVSTm-≃ (p PHere)
FVLabel-≃ {ΓS = ΓS} {S = Join S T} {L = L} {M = M} [ p ] = begin
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt) ∪m FVLabel (L ∘ PShift))
    ≡⟨ DCM-∪ ΓS (FVSTm (L PHere) ∪m FVLabel (λ x → L (PExt x))) (FVLabel (λ x → L (PShift x))) ⟩
  DCM ΓS (FVSTm (L PHere) ∪m FVLabel (L ∘ PExt)) ∪m DCM ΓS (FVLabel (L ∘ PShift))
    ≡⟨ cong₂ _∪m_ (DCM-∪ ΓS (FVSTm (L PHere)) (FVLabel (L ∘ PExt))) (FVLabel-≃ [ p ∘ PShift ]) ⟩
  DCM ΓS (FVSTm (L PHere)) ∪m DCM ΓS (FVLabel (L ∘ PExt)) ∪m DCM ΓS (FVLabel (M ∘ PShift))
    ≡⟨ cong₂ (λ a b → a ∪m b ∪m DCM ΓS (FVLabel (M ∘ PShift))) (FVSTm-≃ (p PHere)) (FVLabel-≃ [ p ∘ PExt ]) ⟩
  DCM ΓS (FVSTm (M PHere)) ∪m DCM ΓS (FVLabel (M ∘ PExt)) ∪m DCM ΓS (FVLabel (M ∘ PShift))
    ≡˘⟨ cong (_∪m DCM ΓS (FVLabel (M ∘ PShift))) (DCM-∪ ΓS (FVSTm (M PHere)) (FVLabel (M ∘ PExt))) ⟩
  DCM ΓS (FVSTm (M PHere) ∪m FVLabel (M ∘ PExt)) ∪m DCM ΓS (FVLabel (M ∘ PShift))
    ≡˘⟨ DCM-∪ ΓS (FVSTm (M PHere) ∪m FVLabel (M ∘ PExt)) (FVLabel (M ∘ PShift)) ⟩
  DCM ΓS (FVSTm (M PHere) ∪m FVLabel (M ∘ PExt) ∪m FVLabel (M ∘ PShift)) ∎

FVLabel-WT-≃ : {L M : Label-WT (COT-to-MT ΓS) S} → ap L ≃l ap M → lty L ≃sty lty M → DCM ΓS (FVLabel-WT L) ≡ DCM ΓS (FVLabel-WT M)
FVLabel-WT-≃ {ΓS = ΓS} {L = L} {M = M} p q = begin
  DCM ΓS (FVSTy (lty L) ∪m FVLabel (ap L))
    ≡⟨ DCM-∪ ΓS (FVSTy (lty L)) (FVLabel (ap L)) ⟩
  DCM ΓS (FVSTy (lty L)) ∪m DCM ΓS (FVLabel (ap L))
    ≡⟨ cong₂ _∪m_ (FVSTy-≃ q) (FVLabel-≃ p) ⟩
  DCM ΓS (FVSTy (lty M)) ∪m DCM ΓS (FVLabel (ap M))
    ≡˘⟨ DCM-∪ ΓS (FVSTy (lty M)) (FVLabel (ap M)) ⟩
  DCM ΓS (FVSTy (lty M) ∪m FVLabel (ap M)) ∎

{-
TransportMVarSet : TVarSet S → Label X S → MVarSet X
TransportMVarSet (VSSing false) L = mEmp
TransportMVarSet (VSSing true) L = FVSTm (L PHere)
TransportMVarSet (VSJoin b xs ys) L = (if b then FVSTm (L PHere) else mEmp) ∪m TransportMVarSet xs (L ∘ PExt) ∪m TransportMVarSet ys (L ∘ PShift)

TransportMVarSet-Emp : {X : MaybeTree n} → (L : Label X S) → TransportMVarSet tEmp L ≡ mEmp
TransportMVarSet-Emp {S = Sing} L = refl
TransportMVarSet-Emp {S = Join S T} {X = X} L = begin
  mEmp ∪m TransportMVarSet tEmp (L ∘ PExt) ∪m TransportMVarSet tEmp (L ∘ PShift)
    ≡⟨ cong₂ (λ a b → mEmp ∪m a ∪m b) (TransportMVarSet-Emp (L ∘ PExt)) (TransportMVarSet-Emp (L ∘ PShift)) ⟩
  mEmp ∪m mEmp ∪m mEmp
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  mEmp ∎

TransportMVarSet-∪m : {X : MaybeTree n} → (xs ys : TVarSet S) → (L : Label X S)
                    → TransportMVarSet (xs ∪t ys) L ≡ TransportMVarSet xs L ∪m TransportMVarSet ys L
TransportMVarSet-∪m (VSSing false) (VSSing b′) L = sym (∪m-left-unit (TransportMVarSet (VSSing b′) L))
TransportMVarSet-∪m (VSSing true) (VSSing false) L = sym (∪m-right-unit (TransportMVarSet (VSSing true) L))
TransportMVarSet-∪m (VSSing true) (VSSing true) L = sym (∪m-idem (TransportMVarSet (VSSing true) L))
TransportMVarSet-∪m {X = X} (VSJoin b xs xs′) (VSJoin b′ ys ys′) L = begin
  (if b ∨ b′ then FVSTm (L PHere) else mEmp)
    ∪m TransportMVarSet (xs ∪t ys) (L ∘ PExt)
    ∪m TransportMVarSet (xs′ ∪t ys′) (L ∘ PShift)
    ≡⟨ cong₃ (λ a b c → a ∪m b ∪m c) (l1 b b′) (TransportMVarSet-∪m xs ys (L ∘ PExt)) (TransportMVarSet-∪m xs′ ys′ (L ∘ PShift)) ⟩
  (if b then FVSTm (L PHere) else mEmp) ∪m
    (if b′ then FVSTm (L PHere) else mEmp)
    ∪m
    (TransportMVarSet xs (λ x → L (PExt x)) ∪m
     TransportMVarSet ys (λ x → L (PExt x)))
    ∪m
    (TransportMVarSet xs′ (λ x → L (PShift x)) ∪m
     TransportMVarSet ys′ (λ x → L (PShift x)))
    ≡⟨ prove 6 ((((var 0F ⊕ var 1F) ⊕ (var 2F ⊕ var 3F)) ⊕ (var 4F ⊕ var 5F)))
               (((var 0F ⊕ var 2F) ⊕ var 4F) ⊕ ((var 1F ⊕ var 3F) ⊕ var 5F))
               (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ emp) ⟩
  (if b then FVSTm (L PHere) else mEmp) ∪m
      TransportMVarSet xs (λ x → L (PExt x))
      ∪m TransportMVarSet xs′ (λ x → L (PShift x))
      ∪m
      ((if b′ then FVSTm (L PHere) else mEmp) ∪m
       TransportMVarSet ys (λ x → L (PExt x))
       ∪m TransportMVarSet ys′ (λ x → L (PShift x))) ∎
  where
    l1 : ∀ b b′ → (if b ∨ b′ then FVSTm (L PHere) else mEmp) ≡
           (if b then FVSTm (L PHere) else mEmp) ∪m (if b′ then FVSTm (L PHere) else mEmp)
    l1 false b′ = sym (∪m-left-unit (if b′ then FVSTm (L PHere) else mEmp))
    l1 true false = sym (∪m-right-unit (if true then FVSTm (L PHere) else mEmp))
    l1 true true = sym (∪m-idem (if true then FVSTm (L PHere) else mEmp))

    import Algebra.Solver.IdempotentCommutativeMonoid as Solver
    open Solver (∪m-idempotentCommutativeMonoid {X = X})

_≡in[_]_ : MVarSet X → MVarSet X → MVarSet X → Set
xs ≡in[ ys ] zs = xs ∪m ys ≡ zs ∪m ys

TransportMVarSet-path : (P : Path S) → (L : Label X S) → TransportMVarSet (fromPath P) L ≡ FVSTm (L P)
TransportMVarSet-path {S = Sing} PHere L = refl
TransportMVarSet-path {S = Join S T} PHere L = {!!}
TransportMVarSet-path (PExt P) L = {!!}
TransportMVarSet-path (PShift P) L = {!!}

TransportMVarSet-term-comp : {X : MaybeTree n} → (a : STm (someTree S)) → (L : Label-WT X S)
                        → TransportMVarSet (FVSTm a) (ap L) ≡in[ FVSTy (lty L) ] FVSTm (a >>= L)
TransportMVarSet-type-comp : {X : MaybeTree n} → (As : STy (someTree S)) → (L : Label-WT X S)
                           → TransportMVarSet (FVSTy As) (ap L) ≡in[ FVSTy (lty L) ] FVSTy (label-on-sty As L)
TransportMVarSet-label-comp : {X : MaybeTree n} → (M : Label (someTree S) T) → (L : Label-WT X S)
                            → TransportMVarSet (FVLabel M) (ap L) ≡in[ FVSTy (lty L) ] FVLabel (label-comp M L)
TransportMVarSet-label-wt-comp : {X : MaybeTree n} → (M : Label-WT (someTree S) T) → (L : Label-WT X S)
                            → TransportMVarSet (FVLabel-WT M) (ap L) ≡in[ FVSTy (lty L) ] FVLabel-WT (label-wt-comp M L)

TransportMVarSet-term-comp {X = X} (SExt a) L = begin
  mEmp ∪m TransportMVarSet (FVSTm a) (ap L ∘ PExt) ∪m
      TransportMVarSet tEmp (λ x → ap L (PShift x)) ∪m (FVSTy (lty L))
    ≡⟨ cong (λ x → mEmp ∪m TransportMVarSet (FVSTm a) (ap L ∘ PExt) ∪m x ∪m (FVSTy (lty L))) (TransportMVarSet-Emp (ap L ∘ PShift)) ⟩
  mEmp ∪m TransportMVarSet (FVSTm a) (ap L ∘ PExt) ∪m mEmp ∪m (FVSTy (lty L))
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  TransportMVarSet (FVSTm a) (ap L ∘ PExt) ∪m (FVSTy (lty L))
    ≡⟨ {!!} ⟩
  TransportMVarSet (FVSTm a) (ap (label₁ L)) ∪m FVSTy (lty (label₁ L))
    ≡⟨ TransportMVarSet-term-comp a (label₁ L) ⟩
  FVSTm (a >>= label₁ L) ∪m FVSTy (lty (label₁ L))
    ≡⟨ {!!} ⟩
  FVSTm (a >>= label₁ L) ∪m (FVSTy (lty L)) ∎
TransportMVarSet-term-comp {X = X} (SShift a) L = begin
  mEmp ∪m TransportMVarSet tEmp (ap L ∘ PExt) ∪m TransportMVarSet (FVSTm a) (ap L ∘ PShift) ∪m (FVSTy (lty L))
    ≡⟨ cong (λ x → mEmp ∪m x ∪m TransportMVarSet (FVSTm a) (ap L ∘ PShift) ∪m (FVSTy (lty L))) (TransportMVarSet-Emp (ap L ∘ PExt)) ⟩
  mEmp ∪m mEmp ∪m TransportMVarSet (FVSTm a) (ap L ∘ PShift) ∪m (FVSTy (lty L))
    ≡⟨ solve (∪m-monoid {X = X}) ⟩
  TransportMVarSet (FVSTm a) (ap L ∘ PShift) ∪m (FVSTy (lty L))
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ TransportMVarSet-term-comp a (label₂ L) ⟩
  {!!}
    ≡⟨ {!!} ⟩
  FVSTm (a >>= label₂ L) ∪m (FVSTy (lty L)) ∎
TransportMVarSet-term-comp (SPath x) L = {!!} -- TransportMVarSet-path x (ap L)
TransportMVarSet-term-comp (SCoh S A M) L = {!!} -- TransportMVarSet-label-wt-comp M L

TransportMVarSet-type-comp S⋆ L = {!!}
TransportMVarSet-type-comp (SArr s As t) L = {!!}

TransportMVarSet-label-comp {T = Sing} M L = {!!} -- TransportMVarSet-term-comp (M PHere) L
TransportMVarSet-label-comp {T = Join T T′} M L = {!!} -- begin
  -- TransportMVarSet
  --     (FVSTm (M PHere) ∪t FVLabel (M ∘ PExt) ∪t FVLabel (M ∘ PShift))
  --     (ap L)
  --   ≡⟨ TransportMVarSet-∪m (FVSTm (M PHere) ∪t FVLabel (M ∘ PExt)) (FVLabel (λ x → M (PShift x))) (ap L) ⟩
  -- TransportMVarSet (FVSTm (M PHere) ∪t FVLabel (λ x → M (PExt x)))
  --   (proj₁ L)
  --   ∪m TransportMVarSet (FVLabel (M ∘ PShift)) (ap L)
  --   ≡⟨ {!!} ⟩
  -- {!!}
  --   ≡⟨ {!!} ⟩
  -- {!!}
  --   ≡⟨ {!!} ⟩
  -- FVSTm (M PHere >>= L) ∪m FVLabel (label-comp (M ∘ PExt) L)
  --     ∪m FVLabel (label-comp (M ∘ PShift) L) ∎

TransportMVarSet-label-wt-comp {X = X} M L = {!!} -- begin
  -- TransportMVarSet (FVSTy (lty M) ∪t FVLabel (ap M)) (ap L) ∪m FVSTy (lty L)
  --   ≡⟨ cong (_∪m FVSTy (lty L)) (TransportMVarSet-∪m (FVSTy (lty M)) (FVLabel (ap M)) (ap L)) ⟩
  -- TransportMVarSet (FVSTy (lty M)) (ap L) ∪m TransportMVarSet (FVLabel (ap M)) (ap L) ∪m FVSTy (lty L)
  --   ≡⟨ {!solve (∪m-monoid {X = X})!} ⟩
  -- TransportMVarSet (FVSTy (lty M)) (ap L) ∪m FVSTy (lty L) ∪m
  --   TransportMVarSet (FVLabel (proj₁ M)) (ap L)
  --   ≡⟨ cong₂ _∪m_ (TransportMVarSet-type-comp (lty M) L) (TransportMVarSet-label-comp (ap M) L) ⟩
  -- FVSTy (label-on-sty (lty M) L) ∪m
  --     FVLabel (label-comp (ap M) L) ∎
-}

FVSTm-susp : (a : STm (someTree S)) → supp-tvarset (DCT (FVSTm a)) ≡ DCT (FVSTm (susp-stm a))
FVSTm-susp {S = S} a rewrite Truth-prop (FVSTm-non-empty a) = refl
