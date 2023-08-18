module Catt.Tree.Structured.Support2 where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Support
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.ToTerm

VarSetTF : (X : MaybeTree n) → Set₁
VarSetTF X = Position X → Set

record _≃vst_ (xs ys : VarSetTF X) : Set where
  field
    forward : ∀ i → xs i → ys i
    backward : ∀ i → ys i → xs i

data StmFV : STm X → VarSetTF X
data StyFV : STy X → VarSetTF X
data LFV : Label X S → VarSetTF X
data LTFV : Label-WT X S → VarSetTF X

data StmFV where
  ∋SExt : {P : Path S} → StmFV a P → StmFV (SExt {T = T} a) (PExt P)
  ∋SShift : {P : Path T} → StmFV a P → StmFV (SShift {S = S} a) (PShift P)
  ∋SPath : {P Q : Path S} → StmFV (SPath P) Q
  ∋SCoh : {L : Label-WT X S} → {P : Position X} → LTFV L P → StmFV (SCoh S As L) P
  ∋SOther : {i : Fin n} → TmFV t i → StmFV (SOther t) i

data StyFV where
  ∋SSrc : {P : Position {n = n} X} → StmFV a P → StyFV (SArr a As b) P
  ∋SBase : {P : Position {n = n} X} → StyFV As P → StyFV (SArr a As b) P
  ∋STgt : {P : Position {n = n} X} → StmFV b P → StyFV (SArr a As b) P

data LFV where
  ∋SPos : {Pos : Position {n = n} X} → (P : Path S) → StmFV (L P) Pos → LFV L Pos

data LTFV where
  ∋SType : {P : Position {n = n} X} → {L : Label-WT X S} → StyFV (lty L) P → LTFV L P
  ∋SLabel : {P : Position {n = n} X} → {L : Label-WT X S} → LFV (ap L) P → LTFV L P

data ContainingPath : (T : Tree n) → (P Q : Path T) → Set where
  ConPRefl : ∀ P → ContainingPath T P P
  ConPFirst : ∀ P → ContainingPath (Join S T) (PExt P) PHere
  ConPSecond : ∀ P → ContainingPath (Join S T) (PExt P) (PShift PHere)

ContainingPos : (ΓS : CtxOrTree n) → (Pos Pos2 : Position (COT-to-MT ΓS)) → Set
ContainingPos (incTree T) P Q = ContainingPath T P Q
ContainingPos (incCtx Γ) P Q = ContainingVar Γ P Q

CloseT : (ΓS : CtxOrTree n) → (xs : VarSetTF (COT-to-MT ΓS)) → VarSetTF (COT-to-MT ΓS)
CloseT ΓS xs j = Σ[ i ∈ Position _ ] ContainingPos ΓS i j × xs i
