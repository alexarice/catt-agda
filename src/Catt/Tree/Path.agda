module Catt.Tree.Path where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Variables
open import Data.Sum
open import Catt.Prelude.Properties

data MaybeTree : ℕ → Set where
  someTree : Tree n → MaybeTree (suc n)
  Other : (n : ℕ) → MaybeTree n

variable
  X Y Z : MaybeTree n

maybeTreeSize : (X : MaybeTree n) → ℕ
maybeTreeSize {n} X = n

data CtxOrTree : ℕ → Set where
  incTree : Tree n → CtxOrTree (suc n)
  incCtx : Ctx n → CtxOrTree n

variable
  ΓS ΔT : CtxOrTree n

COT-to-MT : CtxOrTree n → MaybeTree n
COT-to-MT (incTree x) = someTree x
COT-to-MT (incCtx x) = Other _

COT-to-Ctx : CtxOrTree n → Ctx n
COT-to-Ctx (incTree x) = tree-to-ctx x
COT-to-Ctx (incCtx x) = x

data Path : MaybeTree n → Set where
  PHere : {S : Tree n} → Path (someTree S)
  PExt : {S : Tree m} {T : Tree n} → Path (someTree S) → Path (someTree (Join S T))
  PShift : {S : Tree m} {T : Tree n} → Path (someTree T) → Path (someTree (Join S T))
  POther : {S : MaybeTree n} → Tm n → Path S

variable
  P P′ Q Q′ : Path X


is-Path : Path (someTree S) → Set
is-Path PHere = ⊤
is-Path (PExt P) = is-Path P
is-Path (PShift P) = is-Path P
is-Path (POther x) = ⊥

PPath : Tree n → Set
PPath T = IΣ[ P ∈ Path (someTree T) ] is-Path P

PPHere : PPath S
PPHere = ⟦ PHere ⟧

PPExt : PPath S → PPath (Join S T)
PPExt ⟦ P ⟧ = ⟦ PExt P ⟧

PPShift : PPath T → PPath (Join S T)
PPShift ⟦ P ⟧ = ⟦ PShift P ⟧

path-length : {T : MaybeTree n} → (P : Path T) → ℕ
path-length PHere = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P
path-length (POther t) = 0

path-to-term : {T : MaybeTree n} → (P : Path T) → Tm n
path-to-term PHere = Var (fromℕ _)
path-to-term (PExt P) = suspTm (path-to-term P) [ connect-susp-inc-left _ _ ]tm
path-to-term (PShift P) = path-to-term P [ connect-susp-inc-right _ _ ]tm
path-to-term (POther t) = t

path-to-fin : {T : Tree n} → (P : PPath T) → Fin (suc n)
path-to-fin ⟦ PHere ⟧ = fromℕ _
path-to-fin {T = Join {n} {m} S T} ⟦ PExt P ⟧ = cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin ⟦ P ⟧))))
path-to-fin {T = Join {n} {m} S T} ⟦ PShift PHere ⟧ = cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ _))
path-to-fin {T = Join {n} {m} S T} ⟦ PShift P@(PExt _) ⟧ = inject+ (2 + n) (path-to-fin ⟦ P ⟧)
path-to-fin {T = Join {n} S T} ⟦ PShift P@(PShift _) ⟧ = inject+ (2 + n) (path-to-fin ⟦ P ⟧)

var-to-path : (T : Tree n) → (t : Tm (suc n)) → .⦃ isVar t ⦄ → PPath T
var-to-path-helper : (S : Tree n) → (T : Tree m) → Fin (m + ((suc n) + 2)) → PPath (Join S T)
var-to-path-helper-1 : (S : Tree n) → (T : Tree m) → Fin (suc n + 2) → PPath (Join S T)
var-to-path-helper-2 : (S : Tree n) → (T : Tree m) → Fin 2 → PPath (Join S T)

var-to-path Sing t = PPHere
var-to-path (Join {n} {m} S T) t = var-to-path-helper S T (cast lem (getVarFin t))
  where
    open ≡-Reasoning

    lem : suc (m + (2 + n)) ≡ m + (suc n + 2)
    lem = begin
      suc (m + (2 + n))
        ≡˘⟨ +-suc m (2 + n) ⟩
      m + suc (2 + n)
        ≡⟨ cong (λ - → m + suc -) (+-comm 2 n) ⟩
      m + (suc n + 2) ∎

var-to-path-helper S T i = [ (λ x → PPShift (var-to-path T (Var (inject₁ x)))) , (var-to-path-helper-1 S T) ]′ (splitAt (tree-size T) i)

var-to-path-helper-1 S T i = [ (λ x → PPExt (var-to-path S (Var x))) , (var-to-path-helper-2 S T) ]′ (splitAt (suc (tree-size S)) i)

var-to-path-helper-2 S T 0F = PPShift PPHere
var-to-path-helper-2 S T 1F = PPHere

last-path : (T : Tree n) → PPath T
last-path Sing = PPHere
last-path (Join S T) = PPShift (last-path T)

not-here : (P : PPath S) → Set
not-here ⟦ PHere ⟧ = ⊥
not-here ⟦ PExt P ⟧ = ⊤
not-here ⟦ PShift P ⟧ = ⊤

is-Maximal : PPath S → Set
is-Maximal {S = Sing} ⟦ PHere ⟧ = ⊤
is-Maximal {S = Join S T} ⟦ PHere ⟧ = ⊥
is-Maximal ⟦ PExt P ⟧ = is-Maximal ⟦ P ⟧
is-Maximal ⟦ PShift P ⟧ = not-here ⟦ P ⟧ × is-Maximal ⟦ P ⟧
is-Maximal ⟦ POther P ⟧ = ⊥

-- path-inc-left : (P : Path S) → .⦃ is-Path P ⦄ → (T : Tree n) → Path (connect-tree S T)
-- path-inc-left PHere T = PHere
-- path-inc-left (PExt P) T = PExt P
-- path-inc-left (PShift P) T = PShift (path-inc-left P T)

-- path-inc-right : (S : Tree n) → (P : Path T) → Path (connect-tree S T)
-- path-inc-right Sing P = P
-- path-inc-right (Join S₁ S₂) P = PShift (path-inc-right S₂ P)

-- path-func : Set → (S : Tree n) → Set
-- path-func X S = ∀ (P : Path S) → .⦃ is-Maximal P ⦄ → X
