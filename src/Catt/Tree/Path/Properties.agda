module Catt.Tree.Path.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Wedge.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path

data _≃p_ : Path S → Path T → Set where
  Here≃ : S ≃ S′ → PHere {S = S} ≃p PHere {S = S′}
  Ext≃ : ∀ {P : Path S} {Q : Path S′} → P ≃p Q → T ≃ T′ → PExt {T = T} P ≃p PExt {T = T′} Q
  Shift≃ : ∀ {P : Path T} {Q : Path T′} → S ≃ S′ → P ≃p Q → PShift {S = S} P ≃p PShift {S = S′} Q

≃p-to-same-n : {S : Tree n} → {T : Tree m} → {P : Path S} → {Q : Path T} → P ≃p Q → n ≡ m
≃p-to-same-n (Here≃ x) = ≃-to-same-n x
≃p-to-same-n (Ext≃ p x) = cong₂ (λ a b → a + (2 + b)) (≃-to-same-n x) (≃p-to-same-n p)
≃p-to-same-n (Shift≃ x p) = cong₂ (λ a b → a + suc (suc b)) (≃p-to-same-n p) (≃-to-same-n x)

path-to-term-≃ : P ≃p Q → path-to-term P ≃tm path-to-term Q
path-to-term-≃ (Here≃ x) = Var≃ (cong suc (≃-to-same-n x)) (cong (λ - → toℕ (fromℕ -)) (≃-to-same-n x))
path-to-term-≃ (Ext≃ p x) = sub-action-≃-tm (susp-tm-≃ (path-to-term-≃ p)) (wedge-susp-inc-left-≃ (≃p-to-same-n p) (≃-to-same-n x))
path-to-term-≃ (Shift≃ x p) = sub-action-≃-tm (path-to-term-≃ p) (wedge-susp-inc-right-≃ (≃-to-same-n x) (≃p-to-same-n p))

refl≃p : P ≃p P
refl≃p {P = PHere} = Here≃ refl≃
refl≃p {P = PExt P} = Ext≃ refl≃p refl≃
refl≃p {P = PShift P} = Shift≃ refl≃ refl≃p

sym≃p : P ≃p Q → Q ≃p P
sym≃p (Here≃ x) = Here≃ (sym≃ x)
sym≃p (Ext≃ p x) = Ext≃ (sym≃p p) (sym≃ x)
sym≃p (Shift≃ x p) = Shift≃ (sym≃ x) (sym≃p p)

trans≃p : P ≃p Q → Q ≃p Q′ → P ≃p Q′
trans≃p (Here≃ x) (Here≃ y) = Here≃ (trans≃ x y)
trans≃p (Ext≃ p x) (Ext≃ q y) = Ext≃ (trans≃p p q) (trans≃ x y)
trans≃p (Shift≃ x p) (Shift≃ y q) = Shift≃ (trans≃ x y) (trans≃p p q)

record PATH : Set where
  constructor <_>p
  field
    {path-n} : ℕ
    {path-S} : Tree path-n
    path : Path path-S

open PATH public

path-setoid : Setoid _ _
path-setoid = record { Carrier = PATH
                     ; _≈_ = λ x y → path x ≃p path y
                     ; isEquivalence = record { refl = refl≃p
                                              ; sym = sym≃p
                                              ; trans = trans≃p
                                              }
                     }

ppath-≃-≃p : (p : S ≃′ T) → (P : Path S) → P ≃p ppath-≃ p P
ppath-≃-≃p Refl≃′ P = refl≃p
ppath-≃-≃p (Join≃′ p q) PHere = Here≃ (≃′-to-≃ (Join≃′ p q))
ppath-≃-≃p (Join≃′ p q) (PExt P) = Ext≃ (ppath-≃-≃p p P) (≃′-to-≃ q)
ppath-≃-≃p (Join≃′ p q) (PShift P) = Shift≃ (≃′-to-≃ p) (ppath-≃-≃p q P)

maximal-join-not-here : (P : Path T) → .⦃ is-join T ⦄ → .⦃ is-maximal P ⦄ → not-here P
maximal-join-not-here {T = Join S T} (PExt P) = tt
maximal-join-not-here {T = Join S T} (PShift P) = tt

path-to-term-is-var : (P : Path T) → isVar (path-to-term P)
path-to-term-is-var PHere = tt
path-to-term-is-var (PExt P) = var-to-var-comp-tm (susp-tm (path-to-term P)) ⦃ susp-tm-var (path-to-term P) ⦃ path-to-term-is-var P ⦄ ⦄ (wedge-susp-inc-left _ _) ⦃ wedge-susp-inc-left-var-to-var _ _ ⦄
path-to-term-is-var (PShift P) = var-to-var-comp-tm (path-to-term P) ⦃ path-to-term-is-var P ⦄ (wedge-susp-inc-right _ _) ⦃ wedge-susp-inc-right-var-to-var _ _ ⦄

max-path-lin-tree : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (Z : Path T) → .⦃ is-maximal Z ⦄ → S ≃ T → is-linear-max-path S ≃p Z
max-path-lin-tree Sing PHere Sing≃ = Here≃ Sing≃
max-path-lin-tree (Join S Sing) (PExt Z) (Join≃ p Sing≃) = Ext≃ (max-path-lin-tree S Z p) Sing≃
max-path-lin-tree (Join S Sing) (PShift PHere) (Join≃ p Sing≃) = ⊥-elim it

max-path-unique : (S : Tree n) → .⦃ _ : is-linear S ⦄ → (P : Path S) → .⦃ is-maximal P ⦄ → (Q : Path S) → .⦃ is-maximal Q ⦄ → P ≃p Q
max-path-unique Sing PHere PHere = refl≃p
max-path-unique (Join S Sing) (PExt P) (PExt Q) = Ext≃ (max-path-unique S P Q) refl≃
max-path-unique (Join S Sing) (PExt P) (PShift PHere) = ⊥-elim it
max-path-unique (Join S Sing) (PShift PHere) Q = ⊥-elim it

proj-ext : PExt {T = S} P ≃p PExt {T = T} Q → P ≃p Q
proj-ext (Ext≃ p _) = p

proj-shift : PShift {S = S} P ≃p PShift {S = T} Q → P ≃p Q
proj-shift (Shift≃ _ p) = p

var-wedge-susp-inc-left : (i : Fin (3 + m)) → (n : ℕ) → Var i [ wedge-susp-inc-left m n ]tm ≃tm Var (n ↑ʳ i)
var-wedge-susp-inc-left i zero = id-on-tm (Var i)
var-wedge-susp-inc-left i (suc n) = begin
  < Var i [ wedge-susp-inc-left _ (suc n) ]tm >tm
    ≈⟨ apply-wk-sub-tm-≃ (Var i) (wedge-susp-inc-left _ n) ⟩
  < wk-tm (Var i [ wedge-susp-inc-left _ n ]tm) >tm
    ≈⟨ wk-tm-≃ (var-wedge-susp-inc-left i n) ⟩
  < Var (suc n ↑ʳ i) >tm ∎
  where
    open Reasoning tm-setoid

var-wedge-susp-inc-right : (i : Fin (suc m)) → (n : ℕ) → i ≢ fromℕ m → Var i [ wedge-susp-inc-right n m ]tm ≃tm Var (i ↑ˡ 2 + n)
var-wedge-susp-inc-right {zero} 0F n p = ⊥-elim (p refl)
var-wedge-susp-inc-right {suc m} 0F n p = refl≃tm
var-wedge-susp-inc-right {suc m} (suc i) n p = begin
  < Var i [ wk-sub (wedge-susp-inc-right n m) ]tm >tm
    ≈⟨ apply-wk-sub-tm-≃ (Var i) (wedge-susp-inc-right n m) ⟩
  < wk-tm (Var i [ wedge-susp-inc-right n m ]tm) >tm
    ≈⟨ wk-tm-≃ (var-wedge-susp-inc-right i n (λ x → p (cong suc x))) ⟩
  < wk-tm (Var (i ↑ˡ 2 + n)) >tm ∎
  where
    open Reasoning tm-setoid

var-cast : (p : n ≡ m) → (i : Fin n) → Var (cast p i) ≃tm Var i
var-cast p i = Var≃ (sym p) (toℕ-cast p i)

open import Data.Fin.Properties
open import Data.Fin using (inject≤; lower₁;join)

fromℕ≢inject₁-toℕ : (n : ℕ) → (i : Fin n) → toℕ (fromℕ n) ≢ toℕ (inject₁ i)
fromℕ≢inject₁-toℕ n i x = fromℕ≢inject₁ (toℕ-injective x)

fromℕ≢inject+ : (n m : ℕ) → (i : Fin (suc n)) → fromℕ (n + suc m) ≢ i ↑ˡ suc m
fromℕ≢inject+ zero m 0F ()
fromℕ≢inject+ (suc n) m (suc i) p = fromℕ≢inject+ n m i (Data.Fin.Properties.suc-injective p)

path-to-fin-lem : (P : Path T) → path-to-fin P ≡ fromℕ _ → P ≡ PHere
path-to-fin-lem PHere p = refl
path-to-fin-lem {T = Join {n} {m} S T} (PExt P) p = ⊥-elim (fromℕ≢inject₁-toℕ (2 + n) (inject₁ (path-to-fin P)) (sym lem))
  where
    open ≡-Reasoning
    lem : toℕ (inject₁ (inject₁ (path-to-fin P))) ≡ toℕ (fromℕ (2 + n))
    lem = +-cancelˡ-≡ m _ _ (begin
      m + toℕ (inject₁ (inject₁ (path-to-fin P)))
        ≡˘⟨ toℕ-↑ʳ m (inject₁ (inject₁ (path-to-fin P))) ⟩
      toℕ (m ↑ʳ (inject₁ (inject₁ (path-to-fin P))))
        ≡˘⟨ toℕ-cast (+-suc m (suc (suc n))) (m ↑ʳ (inject₁ (inject₁ (path-to-fin P)))) ⟩
      toℕ (cast _ (m ↑ʳ (inject₁ (inject₁ (path-to-fin P)))))
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
    lem2 = cong pred (+-cancelˡ-≡ m _ _ (begin
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

path-to-term-is-path-to-fin : (P : Path T) → path-to-term P ≃tm Var (path-to-fin P)
path-to-term-is-path-to-fin PHere = refl≃tm
path-to-term-is-path-to-fin {T = Join {n} {m} S T} (PExt P) = begin
  < susp-tm (path-to-term P) [ wedge-susp-inc-left n m ]tm >tm
    ≈⟨ sub-action-≃-tm (susp-tm-≃ (path-to-term-is-path-to-fin P)) refl≃s ⟩
  < Var (inject₁ (inject₁ (path-to-fin P))) [ wedge-susp-inc-left n m ]tm >tm
    ≈⟨ var-wedge-susp-inc-left (inject₁ (inject₁ (path-to-fin P))) m ⟩
  < Var (m ↑ʳ (inject₁ (inject₁ (path-to-fin P)))) >tm
    ≈˘⟨ var-cast (+-suc m (suc (suc n))) (m ↑ʳ (inject₁ (inject₁ (path-to-fin P)))) ⟩
  < Var (cast _ (m ↑ʳ (inject₁ (inject₁ (path-to-fin P))))) >tm ∎
  where open Reasoning tm-setoid
path-to-term-is-path-to-fin {T = Join {n} {m} S T} (PShift PHere) = begin
  < Var (fromℕ m) [ wedge-susp-inc-right n m ]tm >tm
    ≈˘⟨ wedge-inc-fst-var get-snd m ⟩
  < get-snd [ wedge-susp-inc-left n m ]tm >tm
    ≈⟨ var-wedge-susp-inc-left (inject₁ (fromℕ _)) m ⟩
  < Var (m ↑ʳ (inject₁ (fromℕ (suc n)))) >tm
    ≈˘⟨ Var≃ (sym (+-suc m (2 + n))) lem ⟩
  < Var (cast _ (inject₁ (fromℕ (m + suc n)))) >tm ∎
  where
    lem : toℕ (cast _ (inject₁ (fromℕ (m + suc n)))) ≡
            toℕ (m ↑ʳ (inject₁ (fromℕ (suc n))))
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
        ≡˘⟨ toℕ-↑ʳ m (inject₁ (fromℕ (suc n))) ⟩
      toℕ (m ↑ʳ (inject₁ (fromℕ (suc n)))) ∎
      where
        open ≡-Reasoning
    open Reasoning tm-setoid
path-to-term-is-path-to-fin {T = Join {n} {m} S T} (PShift P@(PExt _)) = begin
  < path-to-term P [ wedge-susp-inc-right n m ]tm >tm
    ≈⟨ sub-action-≃-tm (path-to-term-is-path-to-fin P) refl≃s ⟩
  < Var (path-to-fin P) [ wedge-susp-inc-right n m ]tm >tm
    ≈⟨ var-wedge-susp-inc-right (path-to-fin P) n (λ y → l2 (path-to-fin-lem P y)) ⟩
  < Var (path-to-fin P ↑ˡ 2 + n) >tm ∎
  where
    open Reasoning tm-setoid

    l2 : P ≢ PHere
    l2 ()

path-to-term-is-path-to-fin {T = Join {n} {m} S T} (PShift P@(PShift _)) = begin
  < path-to-term P [ wedge-susp-inc-right n m ]tm >tm
    ≈⟨ sub-action-≃-tm (path-to-term-is-path-to-fin P) refl≃s ⟩
  < Var (path-to-fin P) [ wedge-susp-inc-right n m ]tm >tm
    ≈⟨ var-wedge-susp-inc-right (path-to-fin P) n (λ y → l2 (path-to-fin-lem P y)) ⟩
  < Var (path-to-fin P ↑ˡ 2 + n) >tm ∎
  where
    open Reasoning tm-setoid

    l2 : P ≢ PHere
    l2 ()

vtph-end : (S : Tree n) → (T : Tree m) → (i : Fin 2) → var-to-path-helper S T (m ↑ʳ (suc n ↑ʳ i)) ≡ var-to-path-helper-2 S T i
vtph-end S T i = begin
  var-to-path-helper S T (_ ↑ʳ (suc _ ↑ʳ i))
    ≡⟨ cong [ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , var-to-path-helper-1 S T ]′ (splitAt-↑ʳ _ (suc _ + 2) (suc _ ↑ʳ i)) ⟩
  var-to-path-helper-1 S T (suc _ ↑ʳ i)
    ≡⟨ cong [ (λ x → PExt (var-to-path S (Var x))) , var-to-path-helper-2 S T ]′ (splitAt-↑ʳ (suc _) 2 i) ⟩
  var-to-path-helper-2 S T i ∎
  where
    open ≡-Reasoning

vtph-ext : (S : Tree n) → (T : Tree m) → (i : Fin (suc n)) → var-to-path-helper S T (m ↑ʳ (i ↑ˡ 2)) ≡ PExt (var-to-path S (Var i))
vtph-ext S T i = begin
  var-to-path-helper S T (tree-size T ↑ʳ (i ↑ˡ 2))
    ≡⟨ cong [ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , (var-to-path-helper-1 S T) ]′ (splitAt-↑ʳ _ (suc _ + 2) (i ↑ˡ 2)) ⟩
  var-to-path-helper-1 S T (i ↑ˡ 2)
    ≡⟨ cong [ (λ x → PExt (var-to-path S (Var x))) , var-to-path-helper-2 S T ]′ (splitAt-↑ˡ (suc (tree-size S)) i 2) ⟩
  PExt (var-to-path S (Var i)) ∎
  where
    open ≡-Reasoning

vtph-shift : (S : Tree n) → (T : Tree m) → (i : Fin m) → var-to-path-helper S T (i ↑ˡ (suc n + 2)) ≡ PShift (var-to-path T (Var (inject₁ i)))
vtph-shift S T i = cong [ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , var-to-path-helper-1 S T ]′ (splitAt-↑ˡ _ i (suc _ + 2))

path-to-fin-to-path : (P : Path T) → var-to-path T (Var (path-to-fin P)) ≡ P

path-to-fin-to-path {T = Sing} PHere = refl
path-to-fin-to-path {T = Join {n} {m} S T} PHere = begin
  var-to-path-helper S T (cast _ (fromℕ (m + suc (suc n))))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (m ↑ʳ (suc n ↑ʳ 1F))
    ≡⟨ vtph-end S T 1F ⟩
  PHere ∎
  where
    open ≡-Reasoning

    lem : toℕ (cast _ (fromℕ (m + suc (suc n)))) ≡
            toℕ (m ↑ʳ (suc n ↑ʳ 1F))
    lem = begin
      toℕ (cast _ (fromℕ (m + suc (suc n))))
        ≡⟨ toℕ-cast _ (fromℕ (m + suc (suc n))) ⟩
      toℕ (fromℕ (m + suc (suc n)))
        ≡⟨ toℕ-fromℕ (m + suc (suc n)) ⟩
      m + suc (suc n)
        ≡⟨ cong (λ - → m + suc -) (+-comm 1 n) ⟩
      m + (suc n + 1)
        ≡˘⟨ cong (m +_) (toℕ-↑ʳ (suc n) 1F) ⟩
      m + toℕ (suc (n ↑ʳ 1F))
        ≡˘⟨ toℕ-↑ʳ m (suc (n ↑ʳ 1F)) ⟩
      toℕ (m ↑ʳ (suc (n ↑ʳ 1F))) ∎

path-to-fin-to-path {T = Join {n} {m} S T} (PExt P) = begin
  var-to-path-helper S T (cast _ (cast (+-suc m (suc (suc n))) (m ↑ʳ inject₁ (inject₁ (path-to-fin P)))))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (m ↑ʳ (path-to-fin P ↑ˡ 2))
    ≡⟨ vtph-ext S T (path-to-fin P) ⟩
  PExt (var-to-path S (Var (path-to-fin P)))
    ≡⟨ cong PExt (path-to-fin-to-path P) ⟩
  PExt P ∎
  where
    open ≡-Reasoning

    lem2 : toℕ (inject₁ (inject₁ (path-to-fin P))) ≡
             toℕ (path-to-fin P ↑ˡ 2)
    lem2 = begin
       toℕ (inject₁ (inject₁ (path-to-fin P)))
         ≡⟨ toℕ-inject₁ (inject₁ (path-to-fin P)) ⟩
       toℕ (inject₁ (path-to-fin P))
         ≡⟨ toℕ-inject₁ (path-to-fin P) ⟩
       toℕ (path-to-fin P)
         ≡˘⟨ toℕ-↑ˡ (path-to-fin P) 2 ⟩
       toℕ (path-to-fin P ↑ˡ 2) ∎

    lem : toℕ (cast _ (cast (+-suc m (suc (suc n))) (m ↑ʳ (inject₁ (inject₁ (path-to-fin P)))))) ≡ toℕ (m ↑ʳ (path-to-fin P ↑ˡ 2))
    lem = begin
      toℕ (cast _ (cast (+-suc m (suc (suc n))) (m ↑ʳ inject₁ (inject₁ (path-to-fin P)))))
        ≡⟨ toℕ-cast _ (cast _ (m ↑ʳ (inject₁ (inject₁ (path-to-fin P))))) ⟩
      toℕ (cast (+-suc m (suc (suc n))) (m ↑ʳ inject₁ (inject₁ (path-to-fin P))))
        ≡⟨ toℕ-cast (+-suc m (suc (suc n))) (m ↑ʳ inject₁ (inject₁ (path-to-fin P))) ⟩
      toℕ (m ↑ʳ (inject₁ (inject₁ (path-to-fin P))))
        ≡⟨ toℕ-↑ʳ m (inject₁ (inject₁ (path-to-fin P))) ⟩
      m + toℕ (inject₁ (inject₁ (path-to-fin P)))
        ≡⟨ cong (m +_) lem2 ⟩
      m + toℕ (path-to-fin P ↑ˡ 2)
        ≡˘⟨ toℕ-↑ʳ m (path-to-fin P ↑ˡ 2) ⟩
      toℕ (m ↑ʳ (path-to-fin P ↑ˡ 2)) ∎

path-to-fin-to-path {T = Join {n} {m} S T} (PShift PHere) = begin
  var-to-path-helper S T (cast _ (cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ (m + suc n)))))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (m ↑ʳ (suc n ↑ʳ 0F))
    ≡⟨ vtph-end S T 0F ⟩
  PShift PHere ∎
  where
    open ≡-Reasoning

    lem : toℕ (cast _ (cast (cong suc (sym (+-suc m (suc n)))) (inject₁ (fromℕ (m + suc n))))) ≡
            toℕ (m ↑ʳ (suc n ↑ʳ 0F))
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
        ≡˘⟨ cong (m +_) (toℕ-↑ʳ (suc n) 0F) ⟩
      m + toℕ (suc (n ↑ʳ 0F))
        ≡˘⟨ toℕ-↑ʳ m (suc (n ↑ʳ 0F)) ⟩
      toℕ (m ↑ʳ (suc (n ↑ʳ 0F))) ∎

path-to-fin-to-path {T = Join {n} {m} S T} (PShift P@(PExt _)) = begin
  var-to-path-helper S T (cast _ (path-to-fin P ↑ˡ suc (suc n)))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (lower₁ (path-to-fin P) l1 ↑ˡ suc n + 2)
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

    lem : toℕ (cast _ (path-to-fin P ↑ˡ suc (suc n))) ≡
            toℕ (lower₁ (path-to-fin P) l1 ↑ˡ suc n + 2)
    lem = begin
      toℕ (cast _ (path-to-fin P ↑ˡ suc (suc n)))
        ≡⟨ toℕ-cast _ (path-to-fin P ↑ˡ suc (suc n)) ⟩
      toℕ (path-to-fin P ↑ˡ 2 + n)
        ≡⟨ toℕ-↑ˡ (path-to-fin P) (2 + n) ⟩
      toℕ (path-to-fin P)
        ≡˘⟨ toℕ-lower₁ (path-to-fin P) l1 ⟩
      toℕ (lower₁ (path-to-fin P) l1)
        ≡˘⟨ toℕ-↑ˡ (lower₁ (path-to-fin P) l1) (suc (n + 2)) ⟩
      toℕ (lower₁ (path-to-fin P) l1 ↑ˡ suc (n + 2)) ∎

path-to-fin-to-path {T = Join {n} {m} S T} (PShift P@(PShift _)) = begin
  var-to-path-helper S T (cast _ (path-to-fin P ↑ˡ suc (suc n)))
    ≡⟨ cong (var-to-path-helper S T) (toℕ-injective lem) ⟩
  var-to-path-helper S T (lower₁ (path-to-fin P) l1 ↑ˡ suc n + 2)
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

    lem : toℕ (cast _ (path-to-fin P ↑ˡ suc (suc n))) ≡
            toℕ (lower₁ (path-to-fin P) l1 ↑ˡ suc n + 2)
    lem = begin
      toℕ (cast _ (path-to-fin P ↑ˡ suc (suc n)))
        ≡⟨ toℕ-cast _ (path-to-fin P ↑ˡ suc (suc n)) ⟩
      toℕ (path-to-fin P ↑ˡ 2 + n)
        ≡⟨ toℕ-↑ˡ (path-to-fin P) (2 + n) ⟩
      toℕ (path-to-fin P)
        ≡˘⟨ toℕ-lower₁ (path-to-fin P) l1 ⟩
      toℕ (lower₁ (path-to-fin P) l1)
        ≡˘⟨ toℕ-↑ˡ (lower₁ (path-to-fin P) l1) (suc (n + 2)) ⟩
      toℕ (lower₁ (path-to-fin P) l1 ↑ˡ suc (n + 2)) ∎

path-to-term-to-path : (P : Path T) → var-to-path T (path-to-term P) ⦃ path-to-term-is-var P ⦄ ≡ P
path-to-term-to-path {T = T} P = begin
  var-to-path T (path-to-term P) ⦃ path-to-term-is-var P ⦄
    ≡⟨ lem (path-to-term P) (Var (path-to-fin P)) (≃tm-to-≡ (path-to-term-is-path-to-fin P)) ⟩
  var-to-path T (Var (path-to-fin P))
    ≡⟨ path-to-fin-to-path P ⟩
  P ∎

  where
    open ≡-Reasoning

    lem : (t s : Tm (suc _)) → .⦃ v : isVar s ⦄ → (p : t ≡ s) → var-to-path T t ⦃ subst isVar (sym p) v ⦄ ≡ var-to-path T s
    lem t s refl = refl

path-to-fin-shift-lem : (S : Tree n) → (P : Path T) → P ≢ PHere → path-to-fin (PShift {S = S} P) ≡ path-to-fin P ↑ˡ 2 + n
path-to-fin-shift-lem S PHere p = ⊥-elim (p refl)
path-to-fin-shift-lem S (PExt P) p = refl
path-to-fin-shift-lem S (PShift P) p = refl

var-to-path-to-fin : (T : Tree n) → (t : Tm (suc n)) → .⦃ _ : isVar t ⦄ → toℕ (path-to-fin (var-to-path T t)) ≡ toℕ (getVarFin t)

var-helper-to-fin : (S : Tree n) → (T : Tree m) → (i : Fin (m + ((suc n) + 2))) → toℕ (path-to-fin (var-to-path-helper S T i)) ≡ toℕ i
var-helper-to-fin {n} {m} S T i = begin
  toℕ (path-to-fin ([ (λ x → PShift (var-to-path T (Var (inject₁ x)))) , (var-to-path-helper-1 S T) ]′ (splitAt (tree-size T) i)))
    ≡⟨ lem (splitAt (tree-size T) i) ⟩
  toℕ ([ _↑ˡ (suc _ + 2) , (tree-size T) ↑ʳ_ ]′ (splitAt (tree-size T) i))
    ≡⟨ cong toℕ (join-splitAt (tree-size T) (suc _ + 2) i) ⟩
  toℕ i ∎
  where
    open ≡-Reasoning

    l2 : ∀ x → toℕ (path-to-fin ([ (λ x → PExt (var-to-path S (Var x))) , var-to-path-helper-2 S T ]′ x)) ≡ toℕ (m ↑ʳ (join (suc (tree-size S)) 2 x))
    l2 (inj₁ x) = begin
      toℕ (cast _ (m ↑ʳ (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x)))))))
        ≡⟨ toℕ-cast _ (m ↑ʳ (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x)))))) ⟩
      toℕ (m ↑ʳ (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x))))))
        ≡⟨ toℕ-↑ʳ m (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x))))) ⟩
      m + toℕ (inject₁ (inject₁ (path-to-fin (var-to-path S (Var x)))))
        ≡⟨ cong (m +_) (toℕ-inject₁ (inject₁ (path-to-fin (var-to-path S (Var x))))) ⟩
      m + toℕ (inject₁ (path-to-fin (var-to-path S (Var x))))
        ≡⟨ cong (m +_) (toℕ-inject₁ (path-to-fin (var-to-path S (Var x)))) ⟩
      m + toℕ (path-to-fin (var-to-path S (Var x)))
        ≡⟨ cong (m +_) (var-to-path-to-fin S (Var x)) ⟩
      m + toℕ x
        ≡˘⟨ cong (m +_) (toℕ-↑ˡ x 2) ⟩
      m + toℕ (x ↑ˡ 2)
        ≡˘⟨ toℕ-↑ʳ m (x ↑ˡ 2) ⟩
      toℕ (m ↑ʳ (x ↑ˡ 2)) ∎
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
        ≡˘⟨ cong (m +_) (toℕ-↑ʳ (suc n) 0F) ⟩
      m + toℕ (suc (n ↑ʳ 0F))
        ≡˘⟨ toℕ-↑ʳ m (suc (n ↑ʳ 0F)) ⟩
      toℕ (m ↑ʳ (suc (n ↑ʳ 0F))) ∎
    l2 (inj₂ 1F) = begin
      toℕ (fromℕ (m + suc (suc n)))
        ≡⟨ toℕ-fromℕ (m + suc (suc n)) ⟩
      m + suc (suc n)
        ≡⟨ cong (m +_) (+-comm 1 (suc n)) ⟩
      m + (suc n + 1)
        ≡˘⟨ cong (m +_) (toℕ-↑ʳ (suc n) 1F) ⟩
      m + toℕ (suc (n ↑ʳ 1F))
        ≡˘⟨ toℕ-↑ʳ m (suc (n ↑ʳ 1F)) ⟩
      toℕ (m ↑ʳ (suc (n ↑ʳ 1F))) ∎

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
        ≡⟨ cong toℕ (path-to-fin-shift-lem S (var-to-path T (Var (inject₁ x))) λ y → fromℕ≢inject₁-toℕ m x (sym (l3 x y))) ⟩
      toℕ (path-to-fin (var-to-path T (Var (inject₁ x))) ↑ˡ 2 + n)
        ≡⟨ toℕ-↑ˡ (path-to-fin (var-to-path T (Var (inject₁ x)))) (2 + n) ⟩
      toℕ (path-to-fin (var-to-path T (Var (inject₁ x))))
        ≡⟨ var-to-path-to-fin T (Var (inject₁ x)) ⟩
      toℕ (inject₁ x)
        ≡⟨ toℕ-inject₁ x ⟩
      toℕ x
        ≡˘⟨ toℕ-↑ˡ x (suc (n + 2)) ⟩
      toℕ (x ↑ˡ suc (n + 2)) ∎
    lem (inj₂ y) = begin
      toℕ (path-to-fin ([ (λ x → PExt (var-to-path S (Var x))) , var-to-path-helper-2 S T ]′ (splitAt (suc _) y)))
        ≡⟨ l2 (splitAt (suc _) y) ⟩
      toℕ (m ↑ʳ (join (suc (tree-size S)) 2 (splitAt (suc (tree-size S)) y)))
        ≡⟨ cong toℕ (cong (m ↑ʳ_) (join-splitAt (suc (tree-size S)) 2 y)) ⟩
      toℕ (m ↑ʳ y) ∎

var-to-path-to-fin Sing (Var 0F) = refl
var-to-path-to-fin (Join S T) t = begin
  toℕ (path-to-fin (var-to-path-helper S T (cast _ (getVarFin t))))
    ≡⟨ var-helper-to-fin S T (cast _ (getVarFin t)) ⟩
  toℕ (cast _ (getVarFin t))
    ≡⟨ toℕ-cast _ (getVarFin t) ⟩
  toℕ (getVarFin t) ∎
  where
    open ≡-Reasoning

var-to-path-to-term : (T : Tree n) → (t : Tm (suc n)) → .⦃ _ : isVar t ⦄ → path-to-term (var-to-path T t) ≃tm t
var-to-path-to-term T (Var i) = begin
  < path-to-term (var-to-path T (Var i)) >tm
    ≈⟨ path-to-term-is-path-to-fin (var-to-path T (Var i)) ⟩
  < Var (path-to-fin (var-to-path T (Var i))) >tm
    ≈⟨ Var≃ refl (var-to-path-to-fin T (Var i)) ⟩
  < Var i >tm ∎
  where
    open Reasoning tm-setoid

last-path-to-term : (T : Tree n) → path-to-term (last-path T) ≃tm tree-last-var T
last-path-to-term Sing = refl≃tm
last-path-to-term (Join S T) = sub-action-≃-tm (last-path-to-term T) refl≃s

not-here-≃ : (P ≃p Q) → .⦃ not-here P ⦄ → not-here Q
not-here-≃ (Ext≃ p x) = tt
not-here-≃ (Shift≃ x p) = tt

maximal-≃ : (P ≃p Q) → .⦃ is-maximal P ⦄ → is-maximal Q
maximal-≃ (Here≃ Sing≃) = tt
maximal-≃ (Ext≃ p x) = inst ⦃ maximal-≃ p ⦄
maximal-≃ (Shift≃ x p) .p₁ = not-here-≃ p
maximal-≃ (Shift≃ x p) .p₂ = maximal-≃ p

is-linear-max-path-is-0V : (S : Tree n) → .⦃ _ : is-linear S ⦄ → path-to-term (is-linear-max-path S) ≃tm (0V {n = suc n})
is-linear-max-path-is-0V Sing = refl≃tm
is-linear-max-path-is-0V (Join S Sing) = begin
  < susp-tm (path-to-term (is-linear-max-path S)) [ idSub ]tm >tm
    ≈⟨ id-on-tm (susp-tm (path-to-term (is-linear-max-path S))) ⟩
  < susp-tm (path-to-term (is-linear-max-path S)) >tm
    ≈⟨ susp-tm-≃ (is-linear-max-path-is-0V S) ⟩
  < susp-tm 0V >tm
    ≡⟨⟩
  < 0V >tm ∎
  where
    open Reasoning tm-setoid
