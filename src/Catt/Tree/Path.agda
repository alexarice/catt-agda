module Catt.Tree.Path where

open import Catt.Prelude
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Variables
open import Data.Sum
open import Catt.Prelude.Properties

data Path : Tree n → Set

data Path′ : Tree n → Set

data Path where
  PHere : Path S
  POther : Path′ S → Path S

data Path′ where
  PExt : Path S → Path′ (Join S T)
  PNext : Path′ (Join S T)
  PShift : Path′ T → Path′ (Join S T)

-- data Path : Tree n → Set where
--   PHere : Path S
--   PExt : Path S → Path (Join S T)
--   PShift : Path T → Path (Join S T)

variable
  P Q R : Path S
  P′ Q′ R′ : Path′ S

path-length : (P : Path T) → ℕ
path′-length : (P′ : Path′ T) → ℕ

path-length PHere = 0
path-length (POther P′) = path′-length P′

path′-length (PExt x) = suc (path-length x)
path′-length PNext = 0
path′-length (PShift P′) = path′-length P′

path-to-term : {T : Tree n} → (P : Path T) → Tm (suc n)
path′-to-term : {T : Tree n} → (P′ : Path′ T) → Tm (suc n)

path-to-term PHere = Var (fromℕ _)
path-to-term (POther P′) = path′-to-term P′

path′-to-term (PExt x) = susp-tm (path-to-term x) [ connect-susp-inc-left _ _ ]tm
path′-to-term PNext = Var (fromℕ _) [ connect-susp-inc-right _ _ ]tm
path′-to-term (PShift P′) = path′-to-term P′ [ connect-susp-inc-right _ _ ]tm

-- path-to-fin : {T : Tree n} → (P : Path T) → Fin (suc n)
-- path-to-fin PHere = fromℕ _
-- path-to-fin {T = Join {n} {m} S T} (PExt P) = cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P))))
-- path-to-fin {T = Join {n} {m} S T} (PShift PHere) = cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ _))
-- path-to-fin {T = Join {n} {m} S T} (PShift P@(PExt _)) = inject+ (2 + n) (path-to-fin P)
-- path-to-fin {T = Join {n} S T} (PShift P@(PShift _)) = inject+ (2 + n) (path-to-fin P)

-- var-to-path : (T : Tree n) → (t : Tm (suc n)) → .⦃ isVar t ⦄ → Path T
-- var-to-path-helper : (S : Tree n) → (T : Tree m) → Fin (m + ((suc n) + 2)) → Path (Join S T)
-- var-to-path-helper-1 : (S : Tree n) → (T : Tree m) → Fin (suc n + 2) → Path (Join S T)
-- var-to-path-helper-2 : (S : Tree n) → (T : Tree m) → Fin 2 → Path (Join S T)

-- var-to-path Sing t = PHere
-- var-to-path (Join {n} {m} S T) t = var-to-path-helper S T (cast lem (getVarFin t))
--   where
--     open ≡-Reasoning

--     lem : suc (m + (2 + n)) ≡ m + (suc n + 2)
--     lem = begin
--       suc (m + (2 + n))
--         ≡˘⟨ +-suc m (2 + n) ⟩
--       m + suc (2 + n)
--         ≡⟨ cong (λ - → m + suc -) (+-comm 2 n) ⟩
--       m + (suc n + 2) ∎

-- var-to-path-helper S T i = [ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , (var-to-path-helper-1 S T) ]′ (splitAt (tree-size T) i)

-- var-to-path-helper-1 S T i = [ (λ x → PExt (var-to-path S (Var x))) , (var-to-path-helper-2 S T) ]′ (splitAt (suc (tree-size S)) i)

-- var-to-path-helper-2 S T 0F = PShift PHere
-- var-to-path-helper-2 S T 1F = PHere

last-path′ : (T : Tree n) → .⦃ is-join T ⦄ → Path′ T
last-path′ (Join S Sing) = PNext
last-path′ (Join S T@(Join _ _)) = PShift (last-path′ T)

last-path : (T : Tree n) → Path T
last-path Sing = PHere
last-path (Join S T) = POther (last-path′ (Join S T))

not-here : (P : Path S) → Set
not-here PHere = ⊥
not-here (POther P) = ⊤

is-Maximal : Path S → Set
is-Maximal′ : Path′ S → Set

is-Maximal {S = S} PHere = is-sing S
is-Maximal (POther x) = is-Maximal′ x

is-Maximal′ (PExt x) = is-Maximal x
is-Maximal′ PNext = ⊥
is-Maximal′ (PShift P′) = is-Maximal′ P′

is-linear-max-path : (T : Tree n) → .⦃ is-linear T ⦄ → Path T
is-linear-max-path Sing = PHere
is-linear-max-path (Join S Sing) = POther (PExt (is-linear-max-path S))

ppath-≃ : S ≃′ T → Path S → Path T
ppath′-≃ : S ≃′ T → Path′ S → Path′ T

ppath-≃ Refl≃′ P = P
ppath-≃ (Join≃′ p q) PHere = PHere
ppath-≃ (Join≃′ p q) (POther P′) = POther (ppath′-≃ (Join≃′ p q) P′)

ppath′-≃ Refl≃′ P′ = P′
ppath′-≃ (Join≃′ p q) (PExt x) = PExt (ppath-≃ p x)
ppath′-≃ (Join≃′ p q) PNext = PNext
ppath′-≃ (Join≃′ p q) (PShift P′) = PShift (ppath′-≃ q P′)
