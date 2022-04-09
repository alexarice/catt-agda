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



-- fin-condition : ∀ (n m : ℕ) → Fin 3 → Set
-- fin-condition n m 0F = Fin (suc n)
-- fin-condition n m 1F = Fin (suc m)
-- fin-condition n m 2F = ⊤

-- fin-condition-suc : (i : Fin (suc (n + (2 + m)))) → Cases (fin-condition n m) → Cases (fin-condition (suc n) m)
-- doesC (fin-condition-suc i c) = doesC c
-- proofC (fin-condition-suc i (case 0F p)) = suc p
-- proofC (fin-condition-suc i (case 1F p)) = p
-- proofC (fin-condition-suc i (case 2F p)) = p

-- fin-cases-1 : (i : Fin (suc m)) → Maybe (Fin m)
-- fin-cases-1 {zero} i = nothing
-- fin-cases-1 {suc m} 0F = just 0F
-- fin-cases-1 {suc m} (suc i) = map suc (fin-cases-1 i)

-- fin-cases : (i : Fin (suc (n + (2 + m)))) → Cases (fin-condition n m)
-- fin-cases {zero} {m} 0F = case 0F 0F
-- fin-cases {zero} {m} (suc i) = maybe′ (case 1F) (case 2F tt) (fin-cases-1 i)
-- fin-cases {suc n} {m} 0F = case 0F 0F
-- fin-cases {suc n} {m} (suc i) = fin-condition-suc i (fin-cases i)




-- var-to-path : (T : Tree n) (t : Tm (suc n)) → .⦃ isVar t ⦄ → Path T
-- var-to-path-cases : (S : Tree m) → (T : Tree n) → (i : Fin (suc (n + (2 + m)))) → (j : Fin 3) → fin-condition n m j → Path (Join S T)

-- var-to-path Sing t = PHere
-- var-to-path (Join S T) t = cases (fin-cases (getVarFin t)) (var-to-path-cases S T (getVarFin t))

-- var-to-path-cases S T i 0F p = PShift (var-to-path T (Var p))
-- var-to-path-cases S T i 1F p = PExt (var-to-path S (Var p))
-- var-to-path-cases S T i 2F p = PHere

-- var-to-path-list′ : (T : Tree n) → List (Path T)
-- var-to-path-list : (T : Tree n) → List (Path T)

-- var-to-path-list′ Sing = []
-- var-to-path-list′ (Join S T) = (PShift PHere) ∷ (map PExt (var-to-path-list S) ++ map PShift (var-to-path-list′ T))

-- var-to-path-list T = PHere ∷ var-to-path-list′ T

-- var-to-path-list′-len : (T : Tree n) → length (var-to-path-list′ T) ≡ n
-- var-to-path-list-len : (T : Tree n) → length (var-to-path-list T) ≡ suc n

-- var-to-path-list′-len Sing = refl
-- var-to-path-list′-len (Join {n} {m} S T) = begin
--   1 + length (map PExt (var-to-path-list S) ++ map PShift (var-to-path-list′ T))
--     ≡⟨ {!!} ⟩
--   {!!}
--     ≡⟨ {!!} ⟩
--   m + (2 + n) ∎
--   where
--     open ≡-Reasoning

-- var-to-path-list-len T = cong suc (var-to-path-list′-len T)



-- splitAt′ : ∀ m n o → .(m + n ≡ o) → Fin o → Fin m ⊎ Fin n
-- splitAt′ zero n m p i = inj₂ (cast (sym p) i)
-- splitAt′ (suc m) n .(suc _) p 0F = inj₁ 0F
-- splitAt′ (suc m) n (suc o) p (suc i) = map suc (λ x → x) (splitAt′ m n o (cong pred p) i)

-- cast-refl : (i : Fin n) → cast refl i ≡ i
-- cast-refl 0F = refl
-- cast-refl (suc i) = cong suc (cast-refl i)

-- -- var-to-path′ : (T : Tree n) → (i : Fin (suc n)) → Path T
-- -- var-to-path′ Sing i = PHere
-- -- var-to-path′ (Join S T) 0F = PHere
-- -- var-to-path′ (Join {n} {zero} S T) 1F = PShift PHere
-- -- var-to-path′ (Join {n} {zero} S T) (suc (suc i)) = PExt (var-to-path′ S i)
-- -- var-to-path′ (Join {n} {suc m} S T) 1F = PShift PHere
-- -- var-to-path′ (Join {n} {suc m} S T) (suc (suc i)) = [ {!!} , {!!} ]′ (splitAt m i)

-- var-to-path : (T : Tree n) → (t : Tm (suc n)) → .⦃ isVar t ⦄ → Path T
-- var-to-path Sing t = PHere
-- var-to-path (Join {n} {m} S T) t = [ (λ x → PShift (var-to-path T (Var (suc x)))) , f ]′ (splitAt′ m (suc (2 + n)) (suc (m + (2 + n))) (+-suc m (suc (suc n))) (getVarFin t))
--   where
--     g : Fin 2 → Path (Join S T)
--     g 0F = PShift PHere
--     g 1F = PHere

--     f : Fin (suc (2 + n)) → Path (Join S T)
--     f i = [ (λ x → PExt (var-to-path S (Var x))) , g ]′ (splitAt′ (suc n) 2 (suc (2 + n)) (cong suc (+-comm n 2)) i)

-- var-to-path : (T : Tree n) → (t : Tm (suc n)) → .⦃ isVar t ⦄ → Path T
-- var-to-path-helper : (S : Tree n) → (T : Tree m) → Fin (m + ((suc n) + 2)) → Path (Join S T)

-- var-to-path Sing t = PHere
-- var-to-path (Join {n} {m} S T) (Var i) = var-to-path-helper S T (cast lem i)
--   where
--     open ≡-Reasoning
--     lem : suc (m + (2 + n)) ≡ m + (suc n + 2)
--     lem = begin
--       suc m + (2 + n)
--         ≡⟨ cong (suc m +_) (+-comm 2 n) ⟩
--       suc m + (n + 2)
--         ≡˘⟨ +-assoc (suc m) n 2 ⟩
--       suc m + n + 2
--         ≡˘⟨ cong (_+ 2) (+-suc m n) ⟩
--       m + suc n + 2
--         ≡⟨ +-assoc m (suc n) 2 ⟩
--       m + (suc n + 2) ∎

-- var-to-path-helper {n} {m} S T i = [ (λ x → PShift (var-to-path T (Var (suc x)))) , f ]′ (splitAt m i)
--   where
--     g : Fin 2 → Path (Join S T)
--     g 0F = PShift PHere
--     g 1F = PHere

--     f : Fin (suc n + 2) → Path (Join S T)
--     f i = [ (λ x → PExt (var-to-path S (Var x))) , g ]′ (splitAt (suc n) i)


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
