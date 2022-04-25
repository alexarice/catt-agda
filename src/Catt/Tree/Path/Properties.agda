module Catt.Tree.Path.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Tree
open import Catt.Syntax
open import Catt.Tree.Path
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Sum
open import Catt.Syntax.SyntacticEquality
open import Catt.Syntax.Bundles

maximal-join-not-here : (P : Path T) → .⦃ is-join T ⦄ → .⦃ is-Maximal P ⦄ → not-here P
maximal-join-not-here {T = Join S T} (PExt P) = tt
maximal-join-not-here {T = Join S T} (PShift P) = tt

path-to-var-is-var : (P : Path T) → isVar (path-to-var P)
path-to-var-is-var PHere = tt
path-to-var-is-var (PExt P) = var-to-var-comp-tm (suspTm (path-to-var P)) ⦃ suspTm-var (path-to-var P) ⦃ path-to-var-is-var P ⦄ ⦄ (connect-susp-inc-left _ _) ⦃ connect-susp-inc-left-var-to-var _ _ ⦄
path-to-var-is-var (PShift P) = var-to-var-comp-tm (path-to-var P) ⦃ path-to-var-is-var P ⦄ (connect-susp-inc-right _ _) ⦃ connect-susp-inc-right-var-to-var _ _ ⦄

-- fin-cases-1-fromℕ : ∀ m → fin-cases-1 (fromℕ m) ≡ nothing
-- fin-cases-1-fromℕ zero = refl
-- fin-cases-1-fromℕ (suc m) = cong (map suc) (fin-cases-1-fromℕ m)

-- fin-cases-fromℕ : ∀ m n → doesC (fin-cases (fromℕ (m + (2 + n)))) ≡ 2F
-- fin-cases-fromℕ zero n = cong (λ - → doesC {P = fin-condition zero n} (maybe′ (case 1F) (case 2F tt) (map suc -))) (fin-cases-1-fromℕ n)
-- fin-cases-fromℕ (suc m) n = fin-cases-fromℕ m n

-- var-to-path-shift : (S : Tree n) (T : Tree m) → (t : Tm (suc m)) → .⦃ _ : isVar t ⦄ → var-to-path (Join S T) (t [ connect-susp-inc-right n m ]tm) ⦃ var-to-var-comp-tm t (connect-susp-inc-right _ _) ⦃ connect-susp-inc-right-var-to-var n m ⦄ ⦄ ≡ PShift (var-to-path T t)
-- var-to-path-shift S T (Var i) = {!!}
--   where
--     lem : ∀ n m (i : Fin (suc m)) → getVarFin (Var i [ connect-susp-inc-right n m ]tm) ⦃ var-to-var-comp-tm (Var i) (connect-susp-inc-right n m) ⦃ connect-susp-inc-right-var-to-var n m ⦄ ⦄ ≡ inject≤ i (s≤s (m≤m+n m (2 + n)))
--     lem n zero 0F = {!!}
--     lem n (suc m) i = {!!}

-- splitAt′-fromℕ : ∀ m n o (p : m + suc n ≡ suc o) → splitAt′ m (suc n) (suc o) p (fromℕ o) ≡ inj₂ (fromℕ n)
-- splitAt′-fromℕ zero n o refl = cong inj₂ (cast-refl (fromℕ n))
-- splitAt′-fromℕ (suc zero) n .(suc n) refl = cong inj₂ (cast-refl (fromℕ n))
-- splitAt′-fromℕ (suc (suc m)) n .(suc (m + suc n)) refl = cong (map suc (λ x → x)) (splitAt′-fromℕ (suc m) n (m + suc n) refl)

cast-fromℕ : ∀ {n} {m} → .(p : suc n ≡ suc m) → cast p (fromℕ n) ≡ fromℕ m
cast-fromℕ {zero} {zero} p = refl
cast-fromℕ {suc n} {suc m} p = cong suc (cast-fromℕ (cong pred p))

opposite-fromℕ : ∀ n → opposite (fromℕ n) ≡ 0F
opposite-fromℕ zero = refl
opposite-fromℕ (suc n) = cong inject₁ (opposite-fromℕ n)

cast-refl : (i : Fin n) → cast refl i ≡ i
cast-refl 0F = refl
cast-refl (suc i) = cong suc (cast-refl i)

var-connect-susp-inc-left : (i : Fin (3 + m)) → (n : ℕ) → Var i [ connect-susp-inc-left m n ]tm ≃tm Var (raise n i)
var-connect-susp-inc-left i zero = id-on-tm (Var i)
var-connect-susp-inc-left i (suc n) = begin
  < Var i [ connect-susp-inc-left _ (suc n) ]tm >tm
    ≈⟨ apply-lifted-sub-tm-≃ (Var i) (connect-susp-inc-left _ n) ⟩
  < liftTerm (Var i [ connect-susp-inc-left _ n ]tm) >tm
    ≈⟨ lift-tm-≃ (var-connect-susp-inc-left i n) ⟩
  < Var (raise (suc n) i) >tm ∎
  where
    open Reasoning tm-setoid

var-connect-susp-inc-right : (i : Fin (suc m)) → (n : ℕ) → i ≢ fromℕ m → Var i [ connect-susp-inc-right n m ]tm ≃tm Var (inject+ (2 + n) i)
var-connect-susp-inc-right {zero} 0F n p = ⊥-elim (p refl)
var-connect-susp-inc-right {suc m} 0F n p = refl≃tm
var-connect-susp-inc-right {suc m} (suc i) n p = begin
  < Var i [ liftSub (connect-susp-inc-right n m) ]tm >tm
    ≈⟨ apply-lifted-sub-tm-≃ (Var i) (connect-susp-inc-right n m) ⟩
  < liftTerm (Var i [ connect-susp-inc-right n m ]tm) >tm
    ≈⟨ lift-tm-≃ (var-connect-susp-inc-right i n (λ x → p (cong suc x))) ⟩
  < liftTerm (Var (inject+ (2 + n) i)) >tm ∎
  where
    open Reasoning tm-setoid

var-cast : (p : n ≡ m) → (i : Fin n) → Var (cast p i) ≃tm Var i
var-cast p i = Var≃ (sym p) (toℕ-cast p i)

open import Data.Fin.Properties
open import Data.Fin using (inject≤; lower₁;join)



fromℕ≢inject₁ : (n : ℕ) → (i : Fin n) → toℕ (fromℕ n) ≢ toℕ (inject₁ i)
fromℕ≢inject₁ (suc n) 0F ()
fromℕ≢inject₁ (suc n) (suc i) p = fromℕ≢inject₁ n i (cong pred p)

fromℕ≢inject+ : (n m : ℕ) → (i : Fin (suc n)) → fromℕ (n + suc m) ≢ inject+ (suc m) i
fromℕ≢inject+ zero m 0F ()
fromℕ≢inject+ (suc n) m (suc i) p = fromℕ≢inject+ n m i (Data.Fin.Properties.suc-injective p)

path-to-fin-lem : (P : Path T) → path-to-fin P ≡ fromℕ _ → P ≡ PHere
path-to-fin-lem PHere p = refl
path-to-fin-lem {T = Join {n} {m} S T} (PExt P) p = ⊥-elim (fromℕ≢inject₁ (2 + n) (inject₁ (path-to-fin P)) (sym lem))
  where
    open ≡-Reasoning
    lem : toℕ (inject₁ (inject₁ (path-to-fin P))) ≡ toℕ (fromℕ (2 + n))
    lem = +-cancelˡ-≡ m (begin
      m + toℕ (inject₁ (inject₁ (path-to-fin P)))
        ≡˘⟨ toℕ-raise m (inject₁ (inject₁ (path-to-fin P))) ⟩
      toℕ (raise m (inject₁ (inject₁ (path-to-fin P))))
        ≡˘⟨ toℕ-cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P)))) ⟩
      toℕ (cast _ (raise m (inject₁ (inject₁ (path-to-fin P)))))
        ≡⟨ cong toℕ p ⟩
      toℕ (fromℕ (m + (2 + n)))
        ≡⟨ toℕ-fromℕ (m + (2 + n)) ⟩
      m + (2 + n)
        ≡˘⟨ cong (m +_) (toℕ-fromℕ (suc (suc n))) ⟩
      m + toℕ (fromℕ (2 + n)) ∎)

path-to-fin-lem {T = Join {n} {m} S T} (PShift PHere) p = ⊥-elim (lem n lem2)
  where
    lem : ∀ (n : ℕ) → n ≡ suc n → ⊥
    lem zero ()
    lem (suc n) p = lem n (cong pred p)

    open ≡-Reasoning
    lem2 : n ≡ suc n
    lem2 = cong pred (+-cancelˡ-≡ m (begin
      m + suc n
        ≡˘⟨ toℕ-fromℕ (m + suc n) ⟩
      toℕ (fromℕ (m + suc n))
        ≡˘⟨ toℕ-inject₁ (fromℕ (m + suc n)) ⟩
      toℕ (inject₁ (fromℕ (m + suc n)))
        ≡˘⟨ toℕ-cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ (m + suc n))) ⟩
      toℕ (cast _ (inject₁ (fromℕ (m + suc n))))
        ≡⟨ cong toℕ p ⟩
      toℕ (fromℕ (m + (2 + n)))
        ≡⟨ toℕ-fromℕ (m + (2 + n)) ⟩
      m + (2 + n) ∎))
path-to-fin-lem {T = Join {n} {m} S T} (PShift (PExt P)) p = ⊥-elim (fromℕ≢inject+ (_ + (2 + _)) (suc n) _ (sym p))
path-to-fin-lem {T = Join {n} {m} S T} (PShift (PShift P)) p = ⊥-elim (fromℕ≢inject+ (_ + (2 + _)) (suc n) (path-to-fin (PShift P)) (sym p))


path-to-var-is-path-to-fin : (P : Path T) → path-to-var P ≃tm Var (path-to-fin P)
path-to-var-is-path-to-fin PHere = refl≃tm
path-to-var-is-path-to-fin {T = Join {n} {m} S T} (PExt P) = begin
  < suspTm (path-to-var P) [ connect-susp-inc-left n m ]tm >tm
    ≈⟨ sub-action-≃-tm (susp-tm-≃ (path-to-var-is-path-to-fin P)) refl≃s ⟩
  < Var (inject₁ (inject₁ (path-to-fin P))) [ connect-susp-inc-left n m ]tm >tm
    ≈⟨ var-connect-susp-inc-left (inject₁ (inject₁ (path-to-fin P))) m ⟩
  < Var (raise m (inject₁ (inject₁ (path-to-fin P)))) >tm
    ≈˘⟨ var-cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P)))) ⟩
  < Var (cast _ (raise m (inject₁ (inject₁ (path-to-fin P))))) >tm ∎
  where open Reasoning tm-setoid
path-to-var-is-path-to-fin {T = Join {n} {m} S T} (PShift PHere) = begin
  < Var (fromℕ m) [ connect-susp-inc-right n m ]tm >tm
    ≈˘⟨ connect-inc-fst-var getSnd m ⟩
  < getSnd [ connect-susp-inc-left n m ]tm >tm
    ≈⟨ var-connect-susp-inc-left (inject₁ (fromℕ _)) m ⟩
  < Var (raise m (inject₁ (fromℕ (suc n)))) >tm
    ≈˘⟨ Var≃ (sym (+-suc m (2 + n))) lem ⟩
  < Var (cast _ (inject₁ (fromℕ (m + suc n)))) >tm ∎
  where
    lem : toℕ (cast _ (inject₁ (fromℕ (m + suc n)))) ≡
            toℕ (raise m (inject₁ (fromℕ (suc n))))
    lem = begin
      toℕ (cast _ (inject₁ (fromℕ (m + suc n))))
        ≡⟨ toℕ-cast (sym (+-suc (suc m) (suc n))) (inject₁ (fromℕ (m + suc n))) ⟩
      toℕ (inject₁ (fromℕ (m + suc n)))
        ≡⟨ toℕ-inject₁ (fromℕ (m + suc n)) ⟩
      toℕ (fromℕ (m + suc n))
        ≡⟨ toℕ-fromℕ (m + suc n) ⟩
      m + suc n
        ≡˘⟨ cong (m +_) (trans (toℕ-inject₁ (suc (fromℕ n))) (toℕ-fromℕ (suc n))) ⟩
      m + toℕ (inject₁ (fromℕ (suc n)))
        ≡˘⟨ toℕ-raise m (inject₁ (fromℕ (suc n))) ⟩
      toℕ (raise m (inject₁ (fromℕ (suc n)))) ∎
      where
        open ≡-Reasoning
    open Reasoning tm-setoid
path-to-var-is-path-to-fin {T = Join {n} {m} S T} (PShift P@(PExt _)) = begin
  < path-to-var P [ connect-susp-inc-right n m ]tm >tm
    ≈⟨ sub-action-≃-tm (path-to-var-is-path-to-fin P) refl≃s ⟩
  < Var (path-to-fin P) [ connect-susp-inc-right n m ]tm >tm
    ≈⟨ var-connect-susp-inc-right (path-to-fin P) n (λ y → l2 (path-to-fin-lem P y)) ⟩
  < Var (inject+ (2 + n) (path-to-fin P)) >tm ∎
  where
    open Reasoning tm-setoid

    l2 : P ≢ PHere
    l2 ()

path-to-var-is-path-to-fin {T = Join {n} {m} S T} (PShift P@(PShift _)) = begin
  < path-to-var P [ connect-susp-inc-right n m ]tm >tm
    ≈⟨ sub-action-≃-tm (path-to-var-is-path-to-fin P) refl≃s ⟩
  < Var (path-to-fin P) [ connect-susp-inc-right n m ]tm >tm
    ≈⟨ var-connect-susp-inc-right (path-to-fin P) n (λ y → l2 (path-to-fin-lem P y)) ⟩
  < Var (inject+ (2 + n) (path-to-fin P)) >tm ∎
  where
    open Reasoning tm-setoid

    l2 : P ≢ PHere
    l2 ()

vtph-end : (S : Tree n) → (T : Tree m) → (i : Fin 2) → var-to-path-helper S T (raise m (raise (suc n) i)) ≡ var-to-path-helper-2 S T i
vtph-end S T i = begin
  var-to-path-helper S T (raise _ (raise (suc _) i))
    ≡⟨ cong [ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , var-to-path-helper-1 S T ]′ (splitAt-raise _ (suc _ + 2) (raise (suc _) i)) ⟩
  var-to-path-helper-1 S T (raise (suc _) i)
    ≡⟨ cong [ (λ x → PExt (var-to-path S (Var x))) , var-to-path-helper-2 S T ]′ (splitAt-raise (suc _) 2 i) ⟩
  var-to-path-helper-2 S T i ∎
  where
    open ≡-Reasoning

vtph-ext : (S : Tree n) → (T : Tree m) → (i : Fin (suc n)) → var-to-path-helper S T (raise m (inject+ 2 i)) ≡ PExt (var-to-path S (Var i))
vtph-ext S T i = begin
  var-to-path-helper S T (raise (tree-size T) (inject+ 2 i))
    ≡⟨ cong [ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , (var-to-path-helper-1 S T) ]′ (splitAt-raise _ (suc _ + 2) (inject+ 2 i)) ⟩
  var-to-path-helper-1 S T (inject+ 2 i)
    ≡⟨ cong [ (λ x → PExt (var-to-path S (Var x))) , var-to-path-helper-2 S T ]′ (splitAt-inject+ (suc (tree-size S)) 2 i) ⟩
  PExt (var-to-path S (Var i)) ∎
  where
    open ≡-Reasoning

vtph-shift : (S : Tree n) → (T : Tree m) → (i : Fin m) → var-to-path-helper S T (inject+ (suc n + 2) i) ≡ PShift (var-to-path T (Var (inject₁ i)))
vtph-shift S T i = cong [ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , var-to-path-helper-1 S T ]′ (splitAt-inject+ _ (suc _ + 2) i)

path-to-fin-to-path : (P : Path T) → var-to-path T (Var (path-to-fin P)) ≡ P

path-to-fin-to-path {T = Sing} PHere = refl
path-to-fin-to-path {T = Join {n} {m} S T} PHere = begin
  var-to-path-helper S T (cast _ (fromℕ (m + suc (suc n))))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (raise m (raise (suc n) 1F))
    ≡⟨ vtph-end S T 1F ⟩
  PHere ∎
  where
    open ≡-Reasoning

    lem : toℕ (cast _ (fromℕ (m + suc (suc n)))) ≡
            toℕ (raise m (raise (suc n) 1F))
    lem = begin
      toℕ (cast _ (fromℕ (m + suc (suc n))))
        ≡⟨ toℕ-cast _ (fromℕ (m + suc (suc n))) ⟩
      toℕ (fromℕ (m + suc (suc n)))
        ≡⟨ toℕ-fromℕ (m + suc (suc n)) ⟩
      m + suc (suc n)
        ≡⟨ cong (λ - → m + suc -) (+-comm 1 n) ⟩
      m + (suc n + 1)
        ≡˘⟨ cong (m +_) (toℕ-raise (suc n) 1F) ⟩
      m + toℕ (suc (raise n 1F))
        ≡˘⟨ toℕ-raise m (suc (raise n 1F)) ⟩
      toℕ (raise m (suc (raise n 1F))) ∎

path-to-fin-to-path {T = Join {n} {m} S T} (PExt P) = begin
  var-to-path-helper S T (cast _ (cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P))))))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (raise m (inject+ 2 (path-to-fin P)))
    ≡⟨ vtph-ext S T (path-to-fin P) ⟩
  PExt (var-to-path S (Var (path-to-fin P)))
    ≡⟨ cong PExt (path-to-fin-to-path P) ⟩
  PExt P ∎
  where
    open ≡-Reasoning

    lem2 : toℕ (inject₁ (inject₁ (path-to-fin P))) ≡
             toℕ (inject+ 2 (path-to-fin P))
    lem2 = begin
       toℕ (inject₁ (inject₁ (path-to-fin P)))
         ≡⟨ toℕ-inject₁ (inject₁ (path-to-fin P)) ⟩
       toℕ (inject₁ (path-to-fin P))
         ≡⟨ toℕ-inject₁ (path-to-fin P) ⟩
       toℕ (path-to-fin P)
         ≡⟨ toℕ-inject+ 2 (path-to-fin P) ⟩
       toℕ (inject+ 2 (path-to-fin P)) ∎

    lem : toℕ (cast _ (cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P)))))) ≡ toℕ (raise m (inject+ 2 (path-to-fin P)))
    lem = begin
      toℕ (cast _ (cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P))))))
        ≡⟨ toℕ-cast _ (cast _ (raise m (inject₁ (inject₁ (path-to-fin P))))) ⟩
      toℕ (cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P)))))
        ≡⟨ toℕ-cast (+-suc m (suc (suc n))) (raise m (inject₁ (inject₁ (path-to-fin P)))) ⟩
      toℕ (raise m (inject₁ (inject₁ (path-to-fin P))))
        ≡⟨ toℕ-raise m (inject₁ (inject₁ (path-to-fin P))) ⟩
      m + toℕ (inject₁ (inject₁ (path-to-fin P)))
        ≡⟨ cong (m +_) lem2 ⟩
      m + toℕ (inject+ 2 (path-to-fin P))
        ≡˘⟨ toℕ-raise m (inject+ 2 (path-to-fin P)) ⟩
      toℕ (raise m (inject+ 2 (path-to-fin P))) ∎

path-to-fin-to-path {T = Join {n} {m} S T} (PShift PHere) = begin
  var-to-path-helper S T (cast _ (cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ (m + suc n)))))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (raise m (raise (suc n) 0F))
    ≡⟨ vtph-end S T 0F ⟩
  PShift PHere ∎
  where
    open ≡-Reasoning

    lem : toℕ (cast _ (cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ (m + suc n))))) ≡
            toℕ (raise m (raise (suc n) 0F))
    lem = begin
      toℕ (cast _ (cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ (m + suc n)))))
        ≡⟨ toℕ-cast _ (cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ (m + suc n)))) ⟩
      toℕ (cast _ (inject₁ (fromℕ (m + suc n))))
        ≡⟨ toℕ-cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ (m + suc n))) ⟩
      toℕ (inject₁ (fromℕ (m + suc n)))
        ≡⟨ toℕ-inject₁ (fromℕ (m + suc n)) ⟩
      toℕ (fromℕ (m + suc n))
        ≡⟨ toℕ-fromℕ (m + suc n) ⟩
      m + suc n
        ≡⟨ cong (m +_) (+-comm 0 (suc n)) ⟩
      m + (suc n + 0)
        ≡˘⟨ cong (m +_) (toℕ-raise (suc n) 0F) ⟩
      m + toℕ (suc (raise n 0F))
        ≡˘⟨ toℕ-raise m (suc (raise n 0F)) ⟩
      toℕ (raise m (suc (raise n 0F))) ∎

path-to-fin-to-path {T = Join {n} {m} S T} (PShift P@(PExt _)) = begin
  var-to-path-helper S T (cast _ (inject+ (suc (suc n)) (path-to-fin P)))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (inject+ (suc n + 2) (lower₁ (path-to-fin P) l1))
    ≡⟨ vtph-shift S T (lower₁ (path-to-fin P) l1) ⟩
  PShift (var-to-path T (Var (inject₁ (lower₁ (path-to-fin P) l1))))
    ≡⟨ cong (λ - → PShift (var-to-path T (Var -))) (inject₁-lower₁ (path-to-fin P) l1) ⟩
  PShift (var-to-path T (Var (path-to-fin P)))
    ≡⟨ cong PShift (path-to-fin-to-path P) ⟩
  PShift P ∎
  where
    open ≡-Reasoning

    l2 : P ≢ PHere
    l2 ()

    l1 : m ≢ toℕ (path-to-fin P)
    l1 p = l2 (path-to-fin-lem P (toℕ-injective (sym (trans (toℕ-fromℕ (_ + (2 + _))) p))))

    lem : toℕ (cast _ (inject+ (suc (suc n)) (path-to-fin P))) ≡
            toℕ (inject+ (suc n + 2) (lower₁ (path-to-fin P) l1))
    lem = begin
      toℕ (cast _ (inject+ (suc (suc n)) (path-to-fin P)))
        ≡⟨ toℕ-cast _ (inject+ (suc (suc n)) (path-to-fin P)) ⟩
      toℕ (inject+ (2 + n) (path-to-fin P))
        ≡˘⟨ toℕ-inject+ (2 + n) (path-to-fin P) ⟩
      toℕ (path-to-fin P)
        ≡˘⟨ toℕ-lower₁ (path-to-fin P) l1 ⟩
      toℕ (lower₁ (path-to-fin P) l1)
        ≡⟨ toℕ-inject+ (suc (n + 2)) (lower₁ (path-to-fin P) l1) ⟩
      toℕ (inject+ (suc (n + 2)) (lower₁ (path-to-fin P) l1)) ∎

path-to-fin-to-path {T = Join {n} {m} S T} (PShift P@(PShift _)) = begin
  var-to-path-helper S T (cast _ (inject+ (suc (suc n)) (path-to-fin P)))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (inject+ (suc n + 2) (lower₁ (path-to-fin P) l1))
    ≡⟨ vtph-shift S T (lower₁ (path-to-fin P) l1) ⟩
  PShift (var-to-path T (Var (inject₁ (lower₁ (path-to-fin P) l1))))
    ≡⟨ cong (λ - → PShift (var-to-path T (Var -))) (inject₁-lower₁ (path-to-fin P) l1) ⟩
  PShift (var-to-path T (Var (path-to-fin P)))
    ≡⟨ cong PShift (path-to-fin-to-path P) ⟩
  PShift P ∎
  where
    open ≡-Reasoning

    l2 : P ≢ PHere
    l2 ()

    l1 : m ≢ toℕ (path-to-fin P)
    l1 p = l2 (path-to-fin-lem P (toℕ-injective (sym (trans (toℕ-fromℕ (_ + (2 + _))) p))))

    lem : toℕ (cast _ (inject+ (suc (suc n)) (path-to-fin P))) ≡
            toℕ (inject+ (suc n + 2) (lower₁ (path-to-fin P) l1))
    lem = begin
      toℕ (cast _ (inject+ (suc (suc n)) (path-to-fin P)))
        ≡⟨ toℕ-cast _ (inject+ (suc (suc n)) (path-to-fin P)) ⟩
      toℕ (inject+ (2 + n) (path-to-fin P))
        ≡˘⟨ toℕ-inject+ (2 + n) (path-to-fin P) ⟩
      toℕ (path-to-fin P)
        ≡˘⟨ toℕ-lower₁ (path-to-fin P) l1 ⟩
      toℕ (lower₁ (path-to-fin P) l1)
        ≡⟨ toℕ-inject+ (suc (n + 2)) (lower₁ (path-to-fin P) l1) ⟩
      toℕ (inject+ (suc (n + 2)) (lower₁ (path-to-fin P) l1)) ∎

path-to-var-to-path : (P : Path T) → var-to-path T (path-to-var P) ⦃ path-to-var-is-var P ⦄ ≡ P
path-to-var-to-path {T = T} P = begin
  var-to-path T (path-to-var P) ⦃ path-to-var-is-var P ⦄
    ≡⟨ lem (path-to-var P) (Var (path-to-fin P)) (≃tm-to-≡ (path-to-var-is-path-to-fin P)) ⟩
  var-to-path T (Var (path-to-fin P))
    ≡⟨ path-to-fin-to-path P ⟩
  P ∎

  where
    open ≡-Reasoning

    lem : (t s : Tm (suc _)) → .⦃ v : isVar s ⦄ → (p : t ≡ s) → var-to-path T t ⦃ subst isVar (sym p) v ⦄ ≡ var-to-path T s
    lem t s refl = refl

path-to-fin-shift-lem : (S : Tree n) → (P : Path T) → P ≢ PHere → path-to-fin (PShift {S = S} P) ≡ inject+ (2 + n) (path-to-fin P)
path-to-fin-shift-lem S PHere p = ⊥-elim (p refl)
path-to-fin-shift-lem S (PExt P) p = refl
path-to-fin-shift-lem S (PShift P) p = refl


var-to-path-to-fin : (T : Tree n) → (t : Tm (suc n)) → .⦃ _ : isVar t ⦄ → toℕ (path-to-fin (var-to-path T t)) ≡ toℕ (getVarFin t)

var-helper-to-fin : (S : Tree n) → (T : Tree m) → (i : Fin (m + ((suc n) + 2))) → toℕ (path-to-fin (var-to-path-helper S T i)) ≡ toℕ i
var-helper-to-fin {n} {m} S T i = begin
  toℕ (path-to-fin ([ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , (var-to-path-helper-1 S T) ]′ (splitAt (tree-size T) i)))
    ≡⟨ lem (splitAt (tree-size T) i) ⟩
  toℕ ([ inject+ (suc _ + 2) , raise (tree-size T) ]′ (splitAt (tree-size T) i))
    ≡⟨ cong toℕ (join-splitAt (tree-size T) (suc _ + 2) i) ⟩
  toℕ i ∎
  where
    open ≡-Reasoning

    l2 : ∀ x → toℕ (path-to-fin ([ (λ x → PExt (var-to-path S (Var x))) , var-to-path-helper-2 S T ]′ x)) ≡ toℕ (raise m (join (suc (tree-size S)) 2 x))
    l2 (inj₁ x) = begin
      toℕ (cast _ (raise m (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x)))))))
        ≡⟨ toℕ-cast _ (raise m (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x)))))) ⟩
      toℕ (raise m (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x))))))
        ≡⟨ toℕ-raise m (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x))))) ⟩
      m + toℕ (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x)))))
        ≡⟨ cong (m +_) (toℕ-inject₁ (inject₁ (path-to-fin (var-to-path S (Var x))))) ⟩
      m + toℕ (inject₁ (path-to-fin (var-to-path S (Var x))))
        ≡⟨ cong (m +_) (toℕ-inject₁ (path-to-fin (var-to-path S (Var x)))) ⟩
      m + toℕ (path-to-fin (var-to-path S (Var x)))
        ≡⟨ cong (m +_) (var-to-path-to-fin S (Var x)) ⟩
      m + toℕ x
        ≡⟨ cong (m +_) (toℕ-inject+ 2 x) ⟩
      m + toℕ (inject+ 2 x)
        ≡˘⟨ toℕ-raise m (inject+ 2 x) ⟩
      toℕ (raise m (inject+ 2 x)) ∎
    l2 (inj₂ 0F) = begin
      toℕ (cast _ (inject₁ (fromℕ (m + suc n))))
        ≡⟨ toℕ-cast _ (inject₁ (fromℕ (m + suc n))) ⟩
      toℕ (inject₁ (fromℕ (m + suc n)))
        ≡⟨ toℕ-inject₁ (fromℕ (m + suc n)) ⟩
      toℕ (fromℕ (m + suc n))
        ≡⟨ toℕ-fromℕ (m + suc n) ⟩
      m + suc n
        ≡⟨ cong (m +_) (+-comm 0 (suc n)) ⟩
      m + (suc n + 0)
        ≡˘⟨ cong (m +_) (toℕ-raise (suc n) 0F) ⟩
      m + toℕ (suc (raise n 0F))
        ≡˘⟨ toℕ-raise m (suc (raise n 0F)) ⟩
      toℕ (raise m (suc (raise n 0F))) ∎
    l2 (inj₂ 1F) = begin
      toℕ (fromℕ (m + suc (suc n)))
        ≡⟨ toℕ-fromℕ (m + suc (suc n)) ⟩
      m + suc (suc n)
        ≡⟨ cong (m +_) (+-comm 1 (suc n)) ⟩
      m + (suc n + 1)
        ≡˘⟨ cong (m +_) (toℕ-raise (suc n) 1F) ⟩
      m + toℕ (suc (raise n 1F))
        ≡˘⟨ toℕ-raise m (suc (raise n 1F)) ⟩
      toℕ (raise m (suc (raise n 1F))) ∎

    l3 : ∀ x → var-to-path T (Var (inject₁ x)) ≡ PHere → toℕ (inject₁ x) ≡ toℕ (fromℕ m)
    l3 x p = begin
      toℕ (inject₁ x)
        ≡˘⟨ var-to-path-to-fin T (Var (inject₁ x)) ⟩
      toℕ (path-to-fin (var-to-path T (Var (inject₁ x))))
        ≡⟨ cong toℕ (cong path-to-fin p) ⟩
      toℕ (fromℕ m) ∎

    lem : ∀ x → toℕ (path-to-fin ([ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , (var-to-path-helper-1 S T) ]′ x)) ≡ toℕ (join _ (suc _ + 2) x)
    lem (inj₁ x) = begin
      toℕ (path-to-fin (PShift (var-to-path T (Var (inject₁ x)))))
        ≡⟨ cong toℕ (path-to-fin-shift-lem S (var-to-path T (Var (inject₁ x))) λ y → fromℕ≢inject₁ m x (sym (l3 x y))) ⟩
      toℕ (inject+ (2 + n) (path-to-fin (var-to-path T (Var (inject₁ x)))))
        ≡˘⟨ toℕ-inject+ (2 + n) (path-to-fin (var-to-path T (Var (inject₁ x)))) ⟩
      toℕ (path-to-fin (var-to-path T (Var (inject₁ x))))
        ≡⟨ var-to-path-to-fin T (Var (inject₁ x)) ⟩
      toℕ (inject₁ x)
        ≡⟨ toℕ-inject₁ x ⟩
      toℕ x
        ≡⟨ toℕ-inject+ (suc (n + 2)) x ⟩
      toℕ (inject+ (suc (n + 2)) x) ∎
    lem (inj₂ y) = begin
      toℕ (path-to-fin ([ (λ x → PExt (var-to-path S (Var x))) , var-to-path-helper-2 S T ]′ (splitAt (suc _) y)))
        ≡⟨ l2 (splitAt (suc _) y) ⟩
      toℕ (raise m (join (suc (tree-size S)) 2 (splitAt (suc (tree-size S)) y)))
        ≡⟨ cong toℕ (cong (raise m) (join-splitAt (suc (tree-size S)) 2 y)) ⟩
      toℕ (raise m y) ∎

var-to-path-to-fin Sing (Var 0F) = refl
var-to-path-to-fin (Join S T) t = begin
  toℕ (path-to-fin (var-to-path-helper S T (cast _ (getVarFin t))))
    ≡⟨ var-helper-to-fin S T (cast _ (getVarFin t)) ⟩
  toℕ (cast _ (getVarFin t))
    ≡⟨ toℕ-cast _ (getVarFin t) ⟩
  toℕ (getVarFin t) ∎
  where
    open ≡-Reasoning

var-to-path-to-var : (T : Tree n) → (t : Tm (suc n)) → .⦃ _ : isVar t ⦄ → path-to-var (var-to-path T t) ≃tm t
var-to-path-to-var T (Var i) = begin
  < path-to-var (var-to-path T (Var i)) >tm
    ≈⟨ path-to-var-is-path-to-fin (var-to-path T (Var i)) ⟩
  < Var (path-to-fin (var-to-path T (Var i))) >tm
    ≈⟨ Var≃ refl (var-to-path-to-fin T (Var i)) ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid
