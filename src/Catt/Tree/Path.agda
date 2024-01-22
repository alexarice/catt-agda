module Catt.Tree.Path where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Variables
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Tree
open import Catt.Tree.Properties

data Path : Tree n → Set where
  PHere : Path S
  PExt : Path S → Path (Join S T)
  PShift : Path T → Path (Join S T)

variable
  P P′ Q Q′ : Path S

path-length : (P : Path T) → ℕ
path-length PHere = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P

path-to-term : {T : Tree n} → (P : Path T) → Tm (suc n)
path-to-term PHere = Var (fromℕ _)
path-to-term (PExt P) = susp-tm (path-to-term P) [ wedge-susp-inc-left _ _ ]tm
path-to-term (PShift P) = path-to-term P [ wedge-susp-inc-right _ _ ]tm

path-to-fin : {T : Tree n} → (P : Path T) → Fin (suc n)
path-to-fin PHere = fromℕ _
path-to-fin {T = Join {n} {m} S T} (PExt P) = cast (+-suc m (suc (suc n))) (m ↑ʳ (inject₁ (inject₁ (path-to-fin P))))
path-to-fin {T = Join {n} {m} S T} (PShift PHere) = cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ _))
path-to-fin {T = Join {n} {m} S T} (PShift P@(PExt _)) = path-to-fin P ↑ˡ 2 + n
path-to-fin {T = Join {n} S T} (PShift P@(PShift _)) = path-to-fin P ↑ˡ 2 + n

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

last-path : (T : Tree n) → Path T
last-path Sing = PHere
last-path (Join S T) = PShift (last-path T)

not-here : (P : Path S) → Set
not-here PHere = ⊥
not-here (PExt P) = ⊤
not-here (PShift P) = ⊤

is-maximal : Path S → Set
is-maximal {S = Sing} PHere = ⊤
is-maximal {S = Join S T} PHere = ⊥
is-maximal (PExt P) = WrapInst (is-maximal P)
is-maximal (PShift P) = not-here P ×′ is-maximal P

is-linear-max-path : (T : Tree n) → .⦃ is-linear T ⦄ → Path T
is-linear-max-path Sing = PHere
is-linear-max-path (Join S Sing) = PExt (is-linear-max-path S)

instance
  is-linear-max-path-max : {S : Tree n} → .⦃ _ : is-linear S ⦄ → is-maximal (is-linear-max-path S)
  is-linear-max-path-max {S = Sing} = tt
  is-linear-max-path-max {S = Join S Sing} = inst

disc-path : (n : ℕ) → Path (n-disc n)
disc-path n = is-linear-max-path (n-disc n)

ppath-≃ : S ≃′ T → Path S → Path T
ppath-≃ Refl≃′ P = P
ppath-≃ (Join≃′ p q) PHere = PHere
ppath-≃ (Join≃′ p q) (PExt Z) = PExt (ppath-≃ p Z)
ppath-≃ (Join≃′ p q) (PShift Z) = PShift (ppath-≃ q Z)
