module Catt.Tree.Path where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Variables
open import Data.Sum
open import Catt.Prelude.Properties

data Path : Tree n → Set where
  PHere : {S : Tree n} → Path S
  PExt : {S : Tree m} {T : Tree n} → Path S → Path (Join S T)
  PShift : {S : Tree m} {T : Tree n} → Path T → Path (Join S T)

path-length : {T : Tree n} → Path T → ℕ
path-length PHere = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P

path-to-var : {T : Tree n} → (P : Path T) → Tm (suc n)
path-to-var PHere = Var (fromℕ _)
path-to-var (PExt P) = suspTm (path-to-var P) [ connect-susp-inc-left _ _ ]tm
path-to-var (PShift P) = path-to-var P [ connect-susp-inc-right _ _ ]tm

path-to-fin : {T : Tree n} → (P : Path T) → Fin (suc n)
path-to-fin PHere = fromℕ _
path-to-fin {T = Join {n} {m} S T} (PExt P) = cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P))))
path-to-fin {T = Join {n} {m} S T} (PShift PHere) = cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ _))
path-to-fin {T = Join {n} {m} S T} (PShift P@(PExt _)) = inject+ (2 + n) (path-to-fin P)
path-to-fin {T = Join {n} S T} (PShift P@(PShift _)) = inject+ (2 + n) (path-to-fin P)

var-to-path : (T : Tree n) → (t : Tm (suc n)) → .⦃ isVar t ⦄ → Path T
var-to-path-helper : (S : Tree n) → (T : Tree m) → Fin (m + ((suc n) + 2)) → Path (Join S T)
var-to-path-helper-1 : (S : Tree n) → (T : Tree m) → Fin (suc n + 2) → Path (Join S T)
var-to-path-helper-2 : (S : Tree n) → (T : Tree m) → Fin 2 → Path (Join S T)

var-to-path Sing t = PHere
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

var-to-path-helper S T i = [ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , (var-to-path-helper-1 S T) ]′ (splitAt (tree-size T) i)

var-to-path-helper-1 S T i = [ (λ x → PExt (var-to-path S (Var x))) , (var-to-path-helper-2 S T) ]′ (splitAt (suc (tree-size S)) i)

var-to-path-helper-2 S T 0F = PShift PHere
var-to-path-helper-2 S T 1F = PHere

not-here : Path S → Set
not-here PHere = ⊥
not-here (PExt P) = ⊤
not-here (PShift P) = ⊤

is-Maximal : Path S → Set
is-Maximal {S = Sing} PHere = ⊤
is-Maximal {S = Join S T} PHere = ⊥
is-Maximal (PExt P) = is-Maximal P
is-Maximal (PShift P) = not-here P × is-Maximal P

last-path : (T : Tree n) → Path T
last-path Sing = PHere
last-path (Join S T) = PShift (last-path T)

path-inc-left : (P : Path S) → (T : Tree n) → Path (connect-tree S T)
path-inc-left PHere T = PHere
path-inc-left (PExt P) T = PExt P
path-inc-left (PShift P) T = PShift (path-inc-left P T)

path-inc-right : (S : Tree n) → (P : Path T) → Path (connect-tree S T)
path-inc-right Sing P = P
path-inc-right (Join S₁ S₂) P = PShift (path-inc-right S₂ P)
