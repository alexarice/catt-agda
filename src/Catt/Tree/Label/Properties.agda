module Catt.Tree.Label.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree.Label
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Syntax.Bundles
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties

-- data _≃stm_ : STm X → STm Y → Set where
--   ≃Here : S ≃ S′ → SHere {S = S} ≃stm SHere {S = S′}
--   ≃Ext : ∀ {a : STm (someTree S)} {b : STm (someTree S′)} → a ≃stm b → T ≃ T′ → SExt {T = T} a ≃stm SExt {T = T′} b
--   ≃Shift : ∀ {a : STm (someTree T)} {b : STm (someTree T′)} → S ≃ S′ → a ≃stm b → SShift {S = S} a ≃stm SShift {S = S′} b
--   ≃SCoh : S ≃ T →
--   ≃Other : stm-to-term a ≃tm stm-to-term b → a ≃stm b

-- ≃stm-to-same-n : {X : MaybeTree n} → {Y : MaybeTree m} → {a : STm X} → {b : STm Y} → a ≃stm b → n ≡ m
-- ≃stm-to-same-n (≃Here x) = cong suc (≃-to-same-n x)
-- ≃stm-to-same-n (≃Ext p x) = cong₂ (λ a b → suc a + suc b) (≃-to-same-n x) (≃stm-to-same-n p)
-- ≃stm-to-same-n (≃Shift x p) = cong₂ (λ a b → a + suc (suc b)) (≃stm-to-same-n p) (≃-to-same-n x)
-- ≃stm-to-same-n (≃Other x) = ≃tm-to-same-length x

-- stm-to-term-≃ : a ≃stm b → stm-to-term a ≃tm stm-to-term b
-- stm-to-term-≃ (≃Here x) = Var≃ (cong suc (≃-to-same-n x)) (cong (λ - → toℕ (fromℕ -)) (≃-to-same-n x))
-- stm-to-term-≃ (≃Ext p x) = sub-action-≃-tm (susp-tm-≃ (stm-to-term-≃ p)) (connect-susp-inc-left-≃ (cong pred (≃stm-to-same-n p)) (≃-to-same-n x))
-- stm-to-term-≃ (≃Shift x p) = sub-action-≃-tm (stm-to-term-≃ p) (connect-susp-inc-right-≃ (≃-to-same-n x) (cong pred (≃stm-to-same-n p)))
-- stm-to-term-≃ (≃Other x) = x

-- refl≃stm : a ≃stm a
-- refl≃stm {a = SHere} = ≃Here refl≃
-- refl≃stm {a = SExt a} = ≃Ext refl≃stm refl≃
-- refl≃stm {a = SShift a} = ≃Shift refl≃ refl≃stm
-- refl≃stm {a = SCoh S A L} = {!!}
-- refl≃stm {a = SOther x} = ≃Other refl≃tm

-- sym≃stm : P ≃stm Q → Q ≃stm P
-- sym≃stm (≃Here x) = ≃Here (sym≃ x)
-- sym≃stm (≃Ext p x) = ≃Ext (sym≃stm p) (sym≃ x)
-- sym≃stm (≃Shift x p) = ≃Shift (sym≃ x) (sym≃stm p)
-- sym≃stm (≃Other x) = ≃Other (sym≃tm x)

-- trans≃stm : P ≃stm Q → Q ≃stm Q′ → P ≃stm Q′
-- trans≃stm (≃Here x) (≃Here y) = ≃Here (trans≃ x y)
-- trans≃stm (≃Here x) (≃Other y) = ≃Other (trans≃tm (stm-to-term-≃ (≃Here x)) y)
-- trans≃stm (≃Ext p x) (≃Ext q y) = ≃Ext (trans≃stm p q) (trans≃ x y)
-- trans≃stm (≃Ext p x) (≃Other y) = ≃Other (trans≃tm (stm-to-term-≃ (≃Ext p x)) y)
-- trans≃stm (≃Shift x p) (≃Shift y q) = ≃Shift (trans≃ x y) (trans≃stm p q)
-- trans≃stm (≃Shift x p) (≃Other y) = ≃Other (trans≃tm (stm-to-term-≃ (≃Shift x p)) y)
-- trans≃stm (≃Other x) p = ≃Other (trans≃tm x (stm-to-term-≃ p))

-- record PATH : Set where
--   constructor <_>p
--   field
--     {path-n} : ℕ
--     {path-X} : MaybeTree path-n
--     path : Path path-X

-- open PATH public

-- path-setoid : Setoid _ _
-- path-setoid = record { Carrier = PATH
--                         ; _≈_ = λ x y → path x ≃stm path y
--                         ; isEquivalence = record { refl = refl≃stm
--                                                  ; sym = sym≃stm
--                                                  ; trans = trans≃stm
--                                                  }
--                         }

_≃stm_ : (a : STm X) → (b : STm Y) → Set
a ≃stm b = Wrap (λ a b → stm-to-term a ≃tm stm-to-term b) a b

refl≃stm : a ≃stm a
refl≃stm = [ refl≃tm ]

reflexive≃stm : a ≡ b → a ≃stm b
reflexive≃stm refl = refl≃stm

sym≃stm : a ≃stm b → b ≃stm a
sym≃stm [ p ] = [ sym≃tm p ]

trans≃stm : a ≃stm b → b ≃stm c → a ≃stm c
trans≃stm [ p ] [ q ] = [ trans≃tm p q ]

record STM : Set where
  constructor <_>stm
  field
    {stm-n} : ℕ
    {stm-X} : MaybeTree stm-n
    stm : STm stm-X

open STM public

stm-setoid : Setoid _ _
stm-setoid = record { Carrier = STM
                    ; _≈_ = λ x y → stm x ≃stm stm y
                    ; isEquivalence = record { refl = refl≃stm
                                             ; sym = sym≃stm
                                             ; trans = trans≃stm
                                             }
                    }

_≃l_ : Label X S → Label Y S → Set
_≃l_ {S = S} L M = Wrap (λ L M → (P : Path S) → L P ≃stm M P) L M

_≃lp_ : Label′ T S → Label′ U S → Set
_≃lp_ {S = S} L M = Wrap (λ L M → (P : Path S) → L P ≃p M P) L M

refl≃l : {L : Label X S} → L ≃l L
refl≃l .get P = refl≃stm

sym≃l : {L : Label X S} → {M : Label Y S} → L ≃l M → M ≃l L
sym≃l [ p ] .get P = sym≃stm (p P)

trans≃l : {L : Label X S} → {M : Label Y S} → {N : Label Z S} → L ≃l M → M ≃l N → L ≃l N
trans≃l [ p ] [ q ] .get P = trans≃stm (p P) (q P)

record LABEL (S : Tree n) : Set where
  constructor <_>l
  field
    {label-n} : ℕ
    {label-X} : MaybeTree label-n
    label : Label label-X S

open LABEL public

label-setoid : (S : Tree n) → Setoid _ _
label-setoid S = record { Carrier = LABEL S
                        ; _≈_ = λ x y → label x ≃l label y
                        ; isEquivalence = record { refl = refl≃l
                                                 ; sym = sym≃l
                                                 ; trans = trans≃l
                                                 }
                        }

≃SExt : a ≃stm b → S ≃ T → SExt {T = S} a ≃stm SExt {T = T} b
≃SExt [ p ] q = [ sub-action-≃-tm (susp-tm-≃ p) (connect-susp-inc-left-≃ (cong pred (≃tm-to-same-length p)) (≃-to-same-n q)) ]

≃SShift : S ≃ T → a ≃stm b → SShift {S = S} a ≃stm SShift {S = T} b
≃SShift p [ q ] = [ sub-action-≃-tm q (connect-susp-inc-right-≃ (≃-to-same-n p) (cong pred (≃tm-to-same-length q))) ]

≃SPath : P ≃p Q → SPath P ≃stm SPath Q
≃SPath p = [ path-to-term-≃ p ]

compute-to-term : (a : STm (someTree T)) → compute-stm a ≃stm a
compute-to-term (SExt a) = refl≃stm
compute-to-term (SShift a) = refl≃stm
compute-to-term (SPath PHere) = refl≃stm
compute-to-term (SPath (PExt x)) = [ refl≃tm ]
compute-to-term (SPath (PShift x)) = [ refl≃tm ]
compute-to-term (SCoh S A L) = refl≃stm

compute-stm-≃ : a ≃stm b → compute-stm a ≃stm compute-stm b
compute-stm-≃ {a = a} {b = b} p = begin
  < compute-stm a >stm
    ≈⟨ compute-to-term a ⟩
  < a >stm
    ≈⟨ p ⟩
  < b >stm
    ≈˘⟨ compute-to-term b ⟩
  < compute-stm b >stm ∎
  where
    open Reasoning stm-setoid

compute-≃ : compute-stm a ≃stm compute-stm b → a ≃stm b
compute-≃ {a = a} {b = b} p = begin
  < a >stm
    ≈˘⟨ compute-to-term a ⟩
  < compute-stm a >stm
    ≈⟨ p ⟩
  < compute-stm b >stm
    ≈⟨ compute-to-term b ⟩
  < b >stm ∎
  where
    open Reasoning stm-setoid

label-to-sub-≃ : (L : Label-WT X S) → (M : Label-WT Y S) → (ap L ≃l ap M) → lty L ≃ty lty M → label-to-sub L ≃s label-to-sub M
label-to-sub-≃ {S = Sing} L M [ p ] q = Ext≃ (Null≃ q) (p PHere .get)
label-to-sub-≃ {S = Join S T} L M [ p ] q
  = sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ (label₁ L) (label₁ M) ([ (λ P → p (PExt P)) ]) (Arr≃ (p PHere .get) q (p (PShift PHere) .get))))
                       (label-to-sub-≃ (label₂ L) (label₂ M) ([ (λ P → p (PShift P)) ]) q)

≃SCoh : (S : Tree n) → A ≃ty A′ → ∀ {L : Label-WT X S} {M : Label-WT X S} → ap L ≃l ap M → lty L ≃ty lty M → SCoh S A L ≃stm SCoh S A′ M
≃SCoh S p q r = [ sub-action-≃-tm (Coh≃ refl≃c p refl≃s) (label-to-sub-≃ _ _ q r) ]

label-sub-to-sub : {X : MaybeTree n} → (L : Label-WT X S) → (σ : Sub n m B) → label-to-sub (label-sub L σ) ≃s σ ● label-to-sub L
label-sub-to-sub {S = Sing} L σ = refl≃s
label-sub-to-sub {S = Join S T} L σ = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (label-sub L σ))))
                     (label-to-sub (label₂ (label-sub L σ))) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (σ ● unrestrict (label-to-sub (label₁ L)))
                     (σ ● label-to-sub (label₂ L)) >s
    ≈˘⟨ sub-from-connect-sub (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) σ ⟩
  < σ ● label-to-sub L >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (label₁ (label-sub L σ))) ≃s (σ ● unrestrict (label-to-sub (label₁ L)))
    l1 = begin
      < unrestrict (label-to-sub (label₁ (label-sub L σ))) >s
        ≡⟨⟩
      < unrestrict (label-to-sub (label-sub (label₁ L) σ)) >s
        ≈⟨ unrestrict-≃ (label-sub-to-sub (label₁ L) σ) ⟩
      < unrestrict (σ ● label-to-sub (label₁ L)) >s
        ≈⟨ unrestrict-comp-higher σ (label-to-sub (label₁ L)) ⟩
      < σ ● unrestrict (label-to-sub (label₁ L)) >s ∎

    l2 : label-to-sub (label₂ (label-sub L σ)) ≃s (σ ● label-to-sub (label₂ L))
    l2 = begin
      < label-to-sub (label₂ (label-sub L σ)) >s
        ≡⟨⟩
      < label-to-sub (label-sub (label₂ L) σ) >s
        ≈⟨ label-sub-to-sub (label₂ L) σ ⟩
      < σ ● label-to-sub (label₂ L) >s ∎

label-to-sub-stm : (L : Label-WT X S) → (a : STm (someTree S)) → stm-to-term a [ label-to-sub L ]tm ≃tm stm-to-term (a >>= L)
label-comp-to-sub : (L : Label-WT (someTree T) S) → (M : Label-WT X T) → label-to-sub M ● label-to-sub L ≃s label-to-sub (label-wt-comp L M)
label-to-sub-lem : (L : Label-WT X (Join S T)) → getSnd [ unrestrict (label-to-sub (label₁ L)) ]tm ≃tm Var (fromℕ m) [ label-to-sub (label₂ L) ]tm

label-to-sub-phere : (L : Label-WT X S) → Var (fromℕ (tree-size S)) [ label-to-sub L ]tm ≃tm apt L PHere
label-to-sub-phere {S = Sing} L = refl≃tm
label-to-sub-phere {S = Join S₁ S₂} L = begin
  < Var (fromℕ _) [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]tm >tm
    ≈⟨ sub-from-connect-fst-var (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < getFst [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
    ≈⟨ unrestrict-fst (label-to-sub (label₁ L)) ⟩
  < apt L PHere >tm ∎
  where
    open Reasoning tm-setoid

label-to-sub-path : (L : Label-WT X S) → (P : Path S) → path-to-term P [ label-to-sub L ]tm ≃tm apt L P
label-to-sub-path L PHere = label-to-sub-phere L
label-to-sub-path L (PExt P) = begin
  < suspTm (path-to-term P) [ connect-susp-inc-left _ _ ]tm
                            [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (suspTm (path-to-term P)) ⟩
  < suspTm (path-to-term P) [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L))
                            ● connect-susp-inc-left _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (path-to-term P)}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L))) ⟩
  < suspTm (path-to-term P) [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
    ≈⟨ unrestrict-comp-tm (path-to-term P) (label-to-sub (label₁ L)) ⟩
  < path-to-term P [ label-to-sub (label₁ L) ]tm >tm
    ≈⟨ label-to-sub-path (label₁ L) P ⟩
  < apt L (PExt P) >tm ∎
  where
    open Reasoning tm-setoid
label-to-sub-path L (PShift P) = begin
  < path-to-term P [ connect-susp-inc-right _ _ ]tm
                   [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                      (label-to-sub (label₂ L)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (path-to-term P) ⟩
  < path-to-term P [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                      (label-to-sub (label₂ L))
                   ● connect-susp-inc-right _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = path-to-term P}) (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L)) (label-to-sub-lem L)) ⟩
  < path-to-term P [ label-to-sub (label₂ L) ]tm >tm
    ≈⟨ label-to-sub-path (label₂ L) P ⟩
  < apt L (PShift P) >tm ∎
  where
    open Reasoning tm-setoid

label-to-sub-stm L (SExt a) = begin
  < suspTm (stm-to-term a) [ connect-susp-inc-left _ _ ]tm
                            [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (suspTm (stm-to-term a)) ⟩
  < suspTm (stm-to-term a) [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L))
                            ● connect-susp-inc-left _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (stm-to-term a)}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L))) ⟩
  < suspTm (stm-to-term a) [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
    ≈⟨ unrestrict-comp-tm (stm-to-term a) (label-to-sub (label₁ L)) ⟩
  < stm-to-term a [ label-to-sub (label₁ L) ]tm >tm
    ≈⟨ label-to-sub-stm (label₁ L) a ⟩
  < stm-to-term (a >>= label₁ L) >tm ∎
  where
    open Reasoning tm-setoid
label-to-sub-stm L (SShift a) = begin
  < stm-to-term a [ connect-susp-inc-right _ _ ]tm
                   [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                      (label-to-sub (label₂ L)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (stm-to-term a) ⟩
  < stm-to-term a [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                      (label-to-sub (label₂ L))
                   ● connect-susp-inc-right _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L)) (label-to-sub-lem L)) ⟩
  < stm-to-term a [ label-to-sub (label₂ L) ]tm >tm
    ≈⟨ label-to-sub-stm (label₂ L) a ⟩
  < stm-to-term (a >>= label₂ L) >tm ∎
  where
    open Reasoning tm-setoid
label-to-sub-stm L (SPath P) = label-to-sub-path L P
label-to-sub-stm L (SCoh U A M) = begin
  < Coh (tree-to-ctx U) A idSub [ label-to-sub M ]tm
                                [ label-to-sub L ]tm >tm
    ≈˘⟨ assoc-tm (label-to-sub L) (label-to-sub M) (Coh (tree-to-ctx U) A idSub) ⟩
  < Coh (tree-to-ctx U) A idSub [ label-to-sub L ● label-to-sub M ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx U) A idSub}) (label-comp-to-sub M L) ⟩
  < Coh (tree-to-ctx U) A idSub [ label-to-sub (label-wt-comp M L) ]tm >tm ∎
  where
    open Reasoning tm-setoid

label-comp-to-sub L M = begin
  < label-to-sub M ● label-to-sub L >s
    ≈˘⟨ label-sub-to-sub L (label-to-sub M) ⟩
  < label-to-sub (label-sub L (label-to-sub M)) >s
    ≈⟨ label-to-sub-≃ (label-sub L (label-to-sub M)) (label-wt-comp L M) ([ (λ P → [ label-to-sub-stm M (ap L P) ] ) ]) refl≃ty ⟩
  < label-to-sub (label-wt-comp L M) >s ∎
  where
    open Reasoning sub-setoid

label-to-sub-lem L = begin
  < getSnd [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
    ≈⟨ unrestrict-snd (label-to-sub (label₁ L)) ⟩
  < apt L (PShift PHere) >tm
    ≡⟨⟩
  < apt (label₂ L) PHere >tm
    ≈˘⟨ label-to-sub-stm (label₂ L) SHere ⟩
  < Var (fromℕ _) [ label-to-sub (label₂ L) ]tm >tm ∎
    where
      open Reasoning tm-setoid

ap-≃ : {L : Label X S} → {M : Label Y S} → L ≃l M → P ≃p Q → L P ≃stm M Q
ap-≃ p (≃Here x) = p .get PHere
ap-≃ p (≃Ext q x) = ap-≃ [ (λ P → p .get (PExt P)) ] q
ap-≃ p (≃Shift x q) = ap-≃ [ (λ P → p .get (PShift P)) ] q

ap′-≃ : (L : Label′ T S) → P ≃p Q → L P ≃p L Q
ap′-≃ L (≃Here x) = refl≃p
ap′-≃ L (≃Ext q x) = ap′-≃ (L ∘ PExt) q
ap′-≃ L (≃Shift x q) = ap′-≃ (L ∘ PShift) q

extend-≃ : (a ≃stm b) → L ≃l M → A ≃ty B → (a >>= L ,, A) ≃stm (b >>= M ,, B)
extend-≃ {a = a} {b = b} {L = L} {M = M} {A = A} {B = B} [ p ] q r = [ begin
  < stm-to-term (a >>= L ,, A) >tm
    ≈˘⟨ label-to-sub-stm (L ,, A) a ⟩
  < stm-to-term a [ label-to-sub (L ,, A) ]tm >tm
    ≈⟨ sub-action-≃-tm p (label-to-sub-≃ (L ,, A) (M ,, B) q r) ⟩
  < stm-to-term b [ label-to-sub (M ,, B) ]tm >tm
    ≈⟨ label-to-sub-stm (M ,, B) b ⟩
  < stm-to-term (b >>= M ,, B) >tm ∎ ]
  where
    open Reasoning tm-setoid

label-comp-≃ : {L L′ : Label (someTree T) S} → {M : Label-WT X T} → {M′ : Label-WT Y T} → L ≃l L′ → ap M ≃l ap M′ → lty M ≃ty lty M′ → label-comp L M ≃l label-comp L′ M′
label-comp-≃ p q r .get Z = extend-≃ (ap-≃ p refl≃p) q r

label-comp-assoc : (L : Label-WT (someTree S) U) → (M : Label-WT (someTree T) S) → (N : Label-WT X T) → ap (label-wt-comp (label-wt-comp L M) N) ≃l ap (label-wt-comp L (label-wt-comp M N))
extend-assoc : (a : STm (someTree S)) → (L : Label-WT (someTree T) S) → (M : Label-WT X T) → (a >>= L >>= M) ≃stm (a >>= label-wt-comp L M)

label-comp-assoc L M N .get Z = extend-assoc (ap L Z) M N

extend-assoc (SExt a) L M = begin
  < a >>= label₁ L >>= M >stm
    ≈⟨ extend-assoc a (label₁ L) M ⟩
  < a >>= label-wt-comp (label₁ L) M >stm
    ≈⟨ extend-≃ (refl≃stm {a = a}) [ (λ P → refl≃stm) ] (Arr≃ (label-to-sub-stm M (ap L PHere)) refl≃ty (label-to-sub-stm M (ap L (PShift PHere)))) ⟩
  < a >>= label₁ (label-wt-comp L M) >stm ∎
  where
    open Reasoning stm-setoid
extend-assoc (SShift a) L M = extend-assoc a (label₂ L) M
extend-assoc (SPath P) L M = refl≃stm
extend-assoc (SCoh S A L′) L M = ≃SCoh S refl≃ty (label-comp-assoc L′ L M) (begin
  < (lty L′) [ label-to-sub L ]ty [ label-to-sub M ]ty >ty
    ≈˘⟨ assoc-ty (label-to-sub M) (label-to-sub L) (lty L′) ⟩
  < (lty L′) [ label-to-sub M ● label-to-sub L ]ty >ty
    ≈⟨ sub-action-≃-ty (refl≃ty {A = (lty L′)}) (label-comp-to-sub L M) ⟩
  < (lty L′) [ label-to-sub (label-wt-comp L M) ]ty >ty ∎)
  where
    open Reasoning ty-setoid

connect-tree-inc-left-phere : (S : Tree n)
                            → (T : Tree m)
                            → connect-tree-inc-left′ S T PHere ≃p PHere {S = connect-tree S T}
connect-tree-inc-left-phere Sing T = refl≃p
connect-tree-inc-left-phere (Join S₁ S₂) T = refl≃p

connect-tree-inc-phere : (S : Tree n)
                       → (T : Tree m)
                       → connect-tree-inc-left′ S T (last-path S) ≃p connect-tree-inc-right′ S T PHere
connect-tree-inc-phere Sing T = refl≃p
connect-tree-inc-phere (Join S₁ S₂) T = ≃Shift refl≃ (connect-tree-inc-phere S₂ T)

connect-tree-inc-right-last-path : (S : Tree n)
                                 → (T : Tree m)
                                 → connect-tree-inc-right′ S T (last-path T) ≃p last-path (connect-tree S T)
connect-tree-inc-right-last-path Sing T = refl≃p
connect-tree-inc-right-last-path (Join S₁ S₂) T = ≃Shift refl≃ (connect-tree-inc-right-last-path S₂ T)

susp-stm-to-term : (a : STm X) → stm-to-term (susp-stm a) ≃tm suspTm (stm-to-term a)
susp-label-to-sub′ : (L : Label-WT X S) → ((P : Path S) → apt (susp-label L) P ≃tm suspTm (apt L P)) → label-to-sub (susp-label L) ≃s suspSubRes (label-to-sub L)
susp-label-to-sub : (L : Label-WT X S) → label-to-sub (susp-label L) ≃s suspSubRes (label-to-sub L)

susp-stm-to-term {X = someTree x} a = id-on-tm (suspTm (stm-to-term a))
susp-stm-to-term {X = Other _} (SCoh S A L) = begin
  < Coh (tree-to-ctx S) A idSub [ label-to-sub (susp-label L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) A idSub}) (susp-label-to-sub L) ⟩
  < Coh (tree-to-ctx S) A idSub [ suspSubRes (label-to-sub L) ]tm >tm
    ≈˘⟨ susp-res-comp-tm (Coh (tree-to-ctx S) A idSub) (label-to-sub L) ⟩
  < suspTm (Coh (tree-to-ctx S) A idSub [ label-to-sub L ]tm) >tm ∎
  where
    open Reasoning tm-setoid
susp-stm-to-term {X = Other _} (SOther t) = refl≃tm

susp-label-to-sub′ {S = Sing} L f = Ext≃ (Null≃ refl≃ty) (f PHere)
susp-label-to-sub′ {S = Join S T} L f = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (susp-label L))))
                                 (label-to-sub (label₂ (susp-label L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ (label₁ (susp-label L)) (susp-label (label₁ L)) ([ (λ P → [ refl≃tm ]) ]) (Arr≃ (f PHere) refl≃ty (f (PShift PHere))))) refl≃s ⟩
  < sub-from-connect (unrestrict (label-to-sub (susp-label (label₁ L))))
                                 (label-to-sub (susp-label (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (susp-label-to-sub′ (label₁ L) λ P → f (PExt P)))
                          (susp-label-to-sub′ (label₂ L) λ P → f (PShift P)) ⟩
  < sub-from-connect (unrestrict (suspSubRes (label-to-sub (label₁ L)))) (suspSubRes (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-≃ (sub-res-unrestrict-comm (label-to-sub (label₁ L))) refl≃s ⟩
  < sub-from-connect (suspSubRes (unrestrict (label-to-sub (label₁ L)))) (suspSubRes (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-susp-res (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < suspSubRes (sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                             (label-to-sub (label₂ L))) >s ∎
  where
    open Reasoning sub-setoid

susp-label-to-sub L = susp-label-to-sub′ L (λ P → susp-stm-to-term (ap L P))

label-to-sub-map-pshift : (L : Label-WT (someTree T) S) → label-to-sub (map-pshift {S = U} L) ≃s connect-susp-inc-right (tree-size U) (tree-size T) ● label-to-sub L
label-to-sub-map-pshift {U = U} L = begin
  < label-to-sub (map-pshift {S = U} L) >s
    ≈⟨ label-to-sub-≃ (map-pshift {S = U} L) (label-sub L (connect-susp-inc-right (tree-size U) _)) [ (λ P → [ refl≃tm ]) ] refl≃ty ⟩
  < label-to-sub (label-sub L (connect-susp-inc-right (tree-size U) _)) >s
    ≈⟨ label-sub-to-sub L (connect-susp-inc-right (tree-size U) _) ⟩
  < connect-susp-inc-right (tree-size U) _ ● label-to-sub L >s ∎
  where
    open Reasoning sub-setoid

label-to-sub-map-pext : (L : Label-WT (someTree T) S) → label-to-sub (map-pext {T = U} L) ≃s connect-susp-inc-left (tree-size T) (tree-size U) ● suspSubRes (label-to-sub L)
label-to-sub-map-pext {U = U} L = begin
  < label-to-sub (map-pext {T = U} L) >s
    ≈˘⟨ label-to-sub-≃  (label-sub (susp-label L) (connect-susp-inc-left _ (tree-size U)))
                        (map-pext {T = U} L)
                        [ (λ P → [ sub-action-≃-tm (id-on-tm (suspTm (stm-to-term (ap L P)))) refl≃s ]) ]
                        refl≃ty ⟩
  < label-to-sub (label-sub (susp-label L) (connect-susp-inc-left _ (tree-size U))) >s
    ≈⟨ label-sub-to-sub (susp-label L) (connect-susp-inc-left _ (tree-size U)) ⟩
  < connect-susp-inc-left _ (tree-size U) ● label-to-sub (susp-label L) >s
    ≈⟨ sub-action-≃-sub (susp-label-to-sub L) refl≃s ⟩
  < connect-susp-inc-left _ (tree-size U) ● suspSubRes (label-to-sub L) >s ∎
  where
    open Reasoning sub-setoid

lift-stm-to-term : (a : STm (Other n)) → stm-to-term (lift-stm a) ≃tm liftTerm (stm-to-term a)
lift-label-to-sub′ : (L : Label-WT (Other n) S) → ((P : Path S) → apt (lift-label L) P ≃tm liftTerm (apt L P)) → label-to-sub (lift-label L) ≃s liftSub (label-to-sub L)
lift-label-to-sub : (L : Label-WT (Other n) S) → label-to-sub (lift-label L) ≃s liftSub (label-to-sub L)

lift-stm-to-term (SCoh S A L) = begin
  < Coh (tree-to-ctx S) A idSub [ label-to-sub (lift-label L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) A idSub}) (lift-label-to-sub L) ⟩
  < Coh (tree-to-ctx S) A idSub [ liftSub (label-to-sub L) ]tm >tm
    ≈⟨ apply-lifted-sub-tm-≃ (Coh (tree-to-ctx S ) A idSub) (label-to-sub L) ⟩
  < liftTerm (Coh (tree-to-ctx S) A idSub [ label-to-sub L ]tm) >tm ∎
  where
    open Reasoning tm-setoid
lift-stm-to-term (SOther t) = refl≃tm

lift-label-to-sub′ {S = Sing} L f = Ext≃ (Null≃ refl≃ty) (f PHere)
lift-label-to-sub′ {S = Join S T} L f = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (lift-label L))))
                                 (label-to-sub (label₂ (lift-label L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ (label₁ (lift-label L)) (lift-label (label₁ L)) [ (λ P → [ refl≃tm ]) ] (Arr≃ (f PHere) refl≃ty (f (PShift PHere))))) refl≃s ⟩
  < sub-from-connect (unrestrict (label-to-sub (lift-label (label₁ L)))) (label-to-sub (lift-label (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (lift-label-to-sub′ (label₁ L) (λ P → f (PExt P)))) (lift-label-to-sub′ (label₂ L) (λ P → f (PShift P))) ⟩
  < sub-from-connect (unrestrict (liftSub (label-to-sub (label₁ L)))) (liftSub (label-to-sub (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-lift (label-to-sub (label₁ L))) (refl≃s {σ = liftSub (label-to-sub (label₂ L))}) ⟩
  < sub-from-connect (liftSub (unrestrict (label-to-sub (label₁ L)))) (liftSub (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-lift (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < liftSub (sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))) >s ∎
  where
    open Reasoning sub-setoid

lift-label-to-sub L = lift-label-to-sub′ L (λ P → lift-stm-to-term (ap L P))

id-label-to-sub : (S : Tree n) → label-to-sub (id-label-wt S) ≃s idSub {n = suc n}
id-label-to-sub Sing = refl≃s
id-label-to-sub (Join S T) = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (id-label-wt (Join S T)))))
                                 (label-to-sub (label₂ (id-label-wt (Join S T)))) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (connect-susp-inc-left _ _) (connect-susp-inc-right _ _) >s
    ≈⟨ sub-from-connect-prop getSnd ⟩
  < idSub >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (label₁ (id-label-wt (Join S T)))) ≃s connect-susp-inc-left (tree-size S) (tree-size T)
    l1 = begin
      < unrestrict (label-to-sub (label₁ (id-label-wt (Join S T)))) >s
        ≈˘⟨ unrestrict-≃ (label-to-sub-≃ (label-sub (susp-label (id-label-wt S))
                                                    (connect-susp-inc-left (tree-size S) (tree-size T)))
                                         (label₁ (id-label-wt (Join S T)))
                                         [ (λ P → [ sub-action-≃-tm (id-on-tm (suspTm (path-to-term P))) refl≃s ]) ]
                                         (Arr≃ (connect-inc-left-fst-var getSnd (tree-size T))
                                               refl≃ty
                                               (connect-inc-fst-var getSnd (tree-size T)))) ⟩
      < unrestrict (label-to-sub (label-sub (susp-label (id-label-wt S)) (connect-susp-inc-left (tree-size S) (tree-size T)))) >s
        ≈⟨ unrestrict-≃ (label-sub-to-sub (susp-label (id-label-wt S)) (connect-susp-inc-left (tree-size S) (tree-size T))) ⟩
      < unrestrict (connect-susp-inc-left (tree-size S) (tree-size T) ● label-to-sub (susp-label (id-label-wt S))) >s
        ≈⟨ unrestrict-comp-higher (connect-susp-inc-left (tree-size S) (tree-size T)) (label-to-sub (susp-label (id-label-wt S))) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● unrestrict (label-to-sub (susp-label (id-label-wt S))) >s
        ≈⟨ sub-action-≃-sub (unrestrict-≃ (susp-label-to-sub (id-label-wt S))) refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● suspSub (label-to-sub (id-label-wt S)) >s
        ≈⟨ sub-action-≃-sub (susp-sub-≃ (id-label-to-sub S)) refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● suspSub idSub >s
        ≈⟨ sub-action-≃-sub susp-functorial-id refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-left (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) >s ∎

    l2 : label-to-sub (label₂ (id-label-wt (Join S T))) ≃s connect-susp-inc-right (tree-size S) (tree-size T)
    l2 = begin
      < label-to-sub (label₂ (id-label-wt (Join S T))) >s
        ≈⟨ label-to-sub-≃ (label₂ (id-label-wt (Join S T))) (label-sub (id-label-wt T) (connect-susp-inc-right (tree-size S) (tree-size T))) [ (λ P → [ refl≃tm ]) ] refl≃ty ⟩
      < label-to-sub (label-sub (id-label-wt T) (connect-susp-inc-right (tree-size S) (tree-size T))) >s
        ≈⟨ label-sub-to-sub (id-label-wt T) (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ● label-to-sub (id-label-wt T) >s
        ≈⟨ sub-action-≃-sub (id-label-to-sub T) refl≃s ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ● idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) >s ∎

sub-to-label-to-sub : (S : Tree n) → (σ : Sub (suc n) m A) → label-to-sub (to-label S σ ,, A) ≃s σ
sub-to-label-to-sub {A = A} S σ = begin
  < label-to-sub (to-label S σ ,, A) >s
    ≡⟨⟩
  < label-to-sub (label-sub (id-label-wt S) σ) >s
    ≈⟨ label-sub-to-sub (id-label-wt S) σ ⟩
  < σ ● label-to-sub (id-label-wt S) >s
    ≈⟨ sub-action-≃-sub (id-label-to-sub S) refl≃s ⟩
  < σ ● idSub >s
    ≈⟨ id-right-unit σ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid

-- sub-path-equality : {S : Tree n} → (σ : Sub (suc n) m A) → (τ : Sub (suc n) m′ B) → ((P : PPath S) → path-to-term (carrier P) [ σ ]tm ≃tm path-to-term (carrier P) [ τ ]tm) → A ≃ty B → σ ≃s τ
-- sub-path-equality {S = S} σ τ f p = begin
--   < σ >s
--     ≈˘⟨ sub-to-label-to-sub S σ (Other _) ⟩
--   < label-to-sub (to-label S σ (Other _)) >s
--     ≈⟨ label-to-sub-≃ (to-label S σ (Other _)) (to-label S τ (Other _)) (λ P → ≃Other (f P)) p ⟩
--   < label-to-sub (to-label S τ (Other _)) >s
--     ≈⟨ sub-to-label-to-sub S τ (Other _) ⟩
--   < τ >s ∎
--   where
--     open Reasoning sub-setoid

extend-id : (a : STm (someTree T)) → (a >>= id-label-wt T) ≃stm a
extend-id {T = T} a = [ begin
  < stm-to-term (a >>= id-label-wt T) >tm
    ≈˘⟨ label-to-sub-stm (id-label-wt T) a ⟩
  < stm-to-term a [ label-to-sub (id-label-wt T) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (id-label-to-sub T) ⟩
  < stm-to-term a [ idSub ]tm >tm
    ≈⟨ id-on-tm (stm-to-term a) ⟩
  < stm-to-term a >tm ∎ ]
  where
    open Reasoning tm-setoid

_≃lm_ : (L : Label X S) → (M : Label Y S) → Set
_≃lm_ {S = S} L M = Wrap (λ L M → ∀ (Q : Path S) → .⦃ is-Maximal Q ⦄ → L Q ≃stm M Q) L M

refl≃lm : L ≃lm L
refl≃lm = [ (λ Q → refl≃stm ) ]

≃l-to-≃lm : L ≃l M → L ≃lm M
≃l-to-≃lm p .get Z = p .get Z

replace-not-here : (L : Label X S) → (a : STm X) → (P : Path S) → .⦃ not-here P ⦄ → replace-label L a P ≃stm L P
replace-not-here L a (PExt P) = refl≃stm
replace-not-here L a (PShift P) = refl≃stm

replace-join-≃lm : (L : Label X S) → .⦃ is-join S ⦄ → (a : STm X) → replace-label L a ≃lm L
replace-join-≃lm L a .get Z = replace-not-here L a Z ⦃ maximal-join-not-here Z ⦄

connect-label-phere : (L : Label X S)
                    → (M : Label X T)
                    → connect-label L M PHere ≃stm L PHere
connect-label-phere {S = Sing} L M = refl≃stm
connect-label-phere {S = Join S₁ S₂} L M = refl≃stm

connect-label-inc-left : (L : Label X S)
                       → (M : Label X T)
                       → (A : Ty _)
                       → (label-comp (ap (connect-tree-inc-left S T)) (connect-label L M ,, A)) ≃l L
connect-label-inc-left {S = Sing} L M A .get PHere = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get PHere = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get (PExt Q) = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get (PShift Q) = connect-label-inc-left (L ∘ PShift) M A .get Q

connect-label-inc-right : (L : Label X S)
                        → (M : Label X T)
                        → (A : Ty _)
                        → (Z : Path T) → .⦃ not-here Z ⦄ → .⦃ is-Maximal Z ⦄ → (label-comp (ap (connect-tree-inc-right S T)) (connect-label L M ,, A)) Z ≃stm M Z
connect-label-inc-right {S = Sing} L M A Z = replace-not-here M (L PHere) Z
connect-label-inc-right {S = Join S₁ S₂} L M A Z = connect-label-inc-right (L ∘ PShift) M A Z

replace-label-map : (f : STm X → STm Y) → (L : Label X S) → (a : STm X) → (f ∘ replace-label L a) ≃l replace-label (f ∘ L) (f a)
replace-label-map f L P .get PHere = refl≃stm
replace-label-map f L P .get (PExt Z) = refl≃stm
replace-label-map f L P .get (PShift Z) = refl≃stm

connect-label-map : (f : STm X → STm Y) → (L : Label X S) → (M : Label X T) → (f ∘ connect-label L M) ≃l connect-label (f ∘ L) (f ∘ M)
connect-label-map {S = Sing} f L M = replace-label-map f M (L PHere)
connect-label-map {S = Join S₁ S₂} f L M .get PHere = refl≃stm
connect-label-map {S = Join S₁ S₂} f L M .get (PExt Z) = refl≃stm
connect-label-map {S = Join S₁ S₂} f L M .get (PShift Z) = connect-label-map f (λ X → L (PShift X)) M .get Z

replace-label-≃ : ∀ {L : Label X S} {M : Label Y S} → L ≃l M → a ≃stm b → replace-label L a ≃l replace-label M b
replace-label-≃ p q .get PHere = q
replace-label-≃ p q .get (PExt Z) = p .get (PExt Z)
replace-label-≃ p q .get (PShift Z) = p .get (PShift Z)

connect-label-≃ : ∀ {L : Label X S} {M : Label X T} {L′ : Label Y S} {M′ : Label Y T}
                → L ≃l L′
                → M ≃l M′
                → connect-label L M ≃l connect-label L′ M′
connect-label-≃ {S = Sing} p q = replace-label-≃ q (p .get PHere)
connect-label-≃ {S = Join S₁ S₂} p q .get PHere = p .get PHere
connect-label-≃ {S = Join S₁ S₂} p q .get (PExt Z) = p .get (PExt Z)
connect-label-≃ {S = Join S₁ S₂} p q .get (PShift Z) = connect-label-≃ [ (λ P → p .get (PShift P)) ] q .get Z

replace-label-≃m : ∀ {L : Label X S} {M : Label Y S} → L ≃lm M → a ≃stm b → replace-label L a ≃lm replace-label M b
replace-label-≃m p q .get PHere = q
replace-label-≃m p q .get (PExt Z) = p .get (PExt Z)
replace-label-≃m p q .get (PShift Z) = p .get (PShift Z)

connect-label-≃m : ∀ {L : Label X S} {M : Label X T} {L′ : Label Y S} {M′ : Label Y T}
                → L ≃lm L′
                → M ≃lm M′
                → connect-label L M ≃lm connect-label L′ M′
connect-label-≃m {S = Sing} p q = replace-label-≃m q (p .get PHere)
connect-label-≃m {S = Join S₁ S₂} p q .get PHere = p .get PHere
connect-label-≃m {S = Join S₁ S₂} p q .get (PExt Z) = p .get (PExt Z)
connect-label-≃m {S = Join S₁ Sing} {L = L} {M} {L′} {M′} p q .get (PShift Z) = let
  instance .x : not-here Z
  x = proj₁ it
  in begin
  < replace-label M (L (PShift PHere)) Z >stm
    ≈⟨ replace-not-here M (L (PShift PHere)) Z ⟩
  < M Z >stm
    ≈⟨ q .get Z ⦃ proj₂ it ⦄ ⟩
  < M′ Z >stm
    ≈˘⟨ replace-not-here M′ (L′ (PShift PHere)) Z ⟩
  < replace-label M′ (L′ (PShift PHere)) Z >stm ∎
  where
    open Reasoning stm-setoid
connect-label-≃m {S = Join S₁ (Join S₂ S₃)} {L = L} {M} {L′} p q .get (PShift Z) = connect-label-≃m {L = L ∘ PShift} {L′ = L′ ∘ PShift} [ (λ Q → p .get (PShift Q) ⦃ maximal-join-not-here Q ,, it ⦄) ] q .get Z ⦃ proj₂ it ⦄

connect-label-sing : (L : Label X S) → (M M′ : Label X Sing) → connect-label L M ≃l connect-label L M′
connect-label-sing {S = Sing} L M M′ .get PHere = refl≃stm
connect-label-sing {S = Join S₁ S₂} L M M′ .get PHere = refl≃stm
connect-label-sing {S = Join S₁ S₂} L M M′ .get (PExt Z) = refl≃stm
connect-label-sing {S = Join S₁ S₂} L M M′ .get (PShift Z) = connect-label-sing (L ∘ PShift) M M′ .get Z

replace-label-prop : (L : Label X S) → (a : STm X) → a ≃stm L PHere → replace-label L a ≃l L
replace-label-prop L a p .get PHere = p
replace-label-prop L a p .get (PExt Q) = refl≃stm
replace-label-prop L a p .get (PShift Q) = refl≃stm

connect-label-prop : (S : Tree n) → (T : Tree m) → connect-label (ap (connect-tree-inc-left S T)) (ap (connect-tree-inc-right S T)) ≃l id-label (connect-tree S T)
connect-label-prop Sing T = replace-label-prop (id-label T) SHere refl≃stm
connect-label-prop (Join S₁ S₂) T .get PHere = refl≃stm
connect-label-prop (Join S₁ S₂) T .get (PExt Z) = refl≃stm
connect-label-prop (Join S₁ S₂) T .get (PShift Z) = begin
  < connect-label
       (λ x → SPath (PShift (connect-tree-inc-left′ S₂ T x)))
       (λ x → SPath (PShift (connect-tree-inc-right′ S₂ T x))) Z >stm
    ≈⟨ connect-label-≃ {L′ = SShift ∘ ap (connect-tree-inc-left S₂ T)} [ (λ P → [ refl≃tm ]) ] [ (λ P → [ refl≃tm ]) ] .get Z ⟩
  < connect-label (SShift ∘ ap (connect-tree-inc-left S₂ T))
                  (SShift ∘ ap (connect-tree-inc-right S₂ T)) Z >stm
    ≈˘⟨ connect-label-map SShift (ap (connect-tree-inc-left S₂ T)) (ap (connect-tree-inc-right S₂ T)) .get Z ⟩
  < SShift (connect-label (ap (connect-tree-inc-left S₂ T))
                          (ap (connect-tree-inc-right S₂ T)) Z) >stm
    ≈⟨ ≃SShift refl≃ (connect-label-prop S₂ T .get Z) ⟩
  < SShift {S = S₁} (SPath Z) >stm
    ≈⟨ [ refl≃tm ] ⟩
  < SPath (PShift Z) >stm ∎
  where
    open Reasoning stm-setoid

label-≃ : S ≃′ T → Label X T → Label X S
label-≃ p L = L ∘ ppath-≃ p

label-wt-≃ : S ≃′ T → Label-WT X T → Label-WT X S
label-wt-≃ p L = (label-≃ p (ap L)) ,, (lty L)

_≃l′_ : Label X S → Label Y T → Set
_≃l′_ {S = S} {T = T} L M = Σ[ p ∈ S ≃′ T ] L ≃l label-≃ p M

label-to-sub-≃′ : (L : Label-WT X S) → (M : Label-WT Y T) → ap L ≃l′ ap M → lty L ≃ty lty M → label-to-sub L ≃s label-to-sub M
label-to-sub-≃′ L M (p ,, [ q ]) r with ≃-to-same-n (≃′-to-≃ p)
... | refl with ≃-to-≡ (≃′-to-≃ p)
... | refl = label-to-sub-≃ L M [ (λ P → trans≃stm (q P) (ap-≃ (refl≃l {L = ap M}) (sym≃p (ppath-≃-≃p p P)))) ] r

extend-susp-label : (a : STm (someTree S)) → (L : Label-WT X S) → susp-stm (a >>= L) ≃stm (a >>= susp-label L)
extend-susp-label a L = [ begin
  < stm-to-term (susp-stm (a >>= L)) >tm
    ≈⟨ susp-stm-to-term (a >>= L) ⟩
  < suspTm (stm-to-term (a >>= L)) >tm
    ≈˘⟨ susp-tm-≃ (label-to-sub-stm L a) ⟩
  < suspTm (stm-to-term a [ label-to-sub L ]tm) >tm
    ≈⟨ susp-res-comp-tm (stm-to-term a) (label-to-sub L) ⟩
  < stm-to-term a [ suspSubRes (label-to-sub L) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (susp-label-to-sub L) ⟩
  < stm-to-term a [ label-to-sub (susp-label L) ]tm >tm
    ≈⟨ label-to-sub-stm (susp-label L) a ⟩
  < stm-to-term (a >>= susp-label L) >tm ∎ ]
  where
    open Reasoning tm-setoid

SCoh-shift : (S : Tree n) → (A : Ty (suc n)) → (L : Label-WT (someTree T) S) → SCoh S A (map-pshift {S = U} L) ≃stm SShift {S = U} (SCoh S A L)
SCoh-shift {U = U} S A L .get = begin
  < Coh (tree-to-ctx S) A idSub [ label-to-sub (map-pshift {S = U} L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) A idSub}) (label-to-sub-map-pshift {U = U} L) ⟩
  < Coh (tree-to-ctx S) A idSub [ connect-susp-inc-right _ _ ● label-to-sub L ]tm
    >tm
    ≈⟨ assoc-tm (connect-susp-inc-right _ _) (label-to-sub L) (Coh (tree-to-ctx S) A idSub) ⟩
  < Coh (tree-to-ctx S) A idSub [ label-to-sub L ]tm [ connect-susp-inc-right _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

SCoh-ext : (S : Tree n) → (A : Ty (suc n)) → (L : Label-WT (someTree T) S) → SCoh S A (map-pext {T = U} L) ≃stm SExt {T = U} (SCoh S A L)
SCoh-ext {U = U} S A L .get = begin
  < Coh (tree-to-ctx S) A idSub [ label-to-sub (map-pext {T = U} L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) A idSub}) (label-to-sub-map-pext {U = U} L) ⟩
  < Coh (tree-to-ctx S) A idSub [ connect-susp-inc-left _ (tree-size U)
                                ● suspSubRes (label-to-sub L) ]tm >tm
    ≈⟨ assoc-tm (connect-susp-inc-left _ (tree-size U)) (suspSubRes (label-to-sub L)) (Coh (tree-to-ctx S) A idSub) ⟩
  < Coh (tree-to-ctx S) A idSub [ suspSubRes (label-to-sub L) ]tm
                                [ connect-susp-inc-left _ (tree-size U) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (susp-res-comp-tm (Coh (tree-to-ctx S) A idSub) (label-to-sub L)) refl≃s ⟩
  < suspTm (Coh (tree-to-ctx S) A idSub [ label-to-sub L ]tm) [ connect-susp-inc-left _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

extend-map-pshift : (a : STm (someTree S)) → (L : Label-WT (someTree T) S) → (a >>= map-pshift {S = U} L) ≃stm SShift {S = U} (a >>= L)
map-pshift-comp : (L : Label (someTree T) S) → (M : Label-WT (someTree U) T)
                → label-comp L (map-pshift {S = U′} M) ≃l (SShift {S = U′} ∘ label-comp L M)
map-pshift-comp L M .get Z = extend-map-pshift (L Z) M

extend-map-pshift (SExt a) L = extend-map-pshift a (label₁ L)
extend-map-pshift (SShift a) L = extend-map-pshift a (label₂ L)
extend-map-pshift (SPath P) l = refl≃stm
extend-map-pshift {U = U} (SCoh S A M) L = begin
  < SCoh S A (label-wt-comp M (map-pshift L)) >stm
    ≈⟨ ≃SCoh S refl≃ty (map-pshift-comp (ap M) L) lem ⟩
  < SCoh S A (map-pshift (label-wt-comp M L)) >stm
    ≈⟨ SCoh-shift S A (label-wt-comp M L) ⟩
  < SShift (SCoh S A (label-wt-comp M L)) >stm ∎
  where
    lem : (lty M [ label-to-sub (map-pshift {S = U} L) ]ty) ≃ty
            ((lty M [ label-to-sub L ]ty) [ connect-susp-inc-right _ _ ]ty)
    lem = begin
      < lty M [ label-to-sub (map-pshift {S = U} L) ]ty >ty
        ≈⟨ sub-action-≃-ty (refl≃ty {A = lty M}) (label-to-sub-map-pshift {U = U} L) ⟩
      < lty M [ connect-susp-inc-right _ _ ● label-to-sub L ]ty >ty
        ≈⟨ assoc-ty (connect-susp-inc-right _ _) (label-to-sub L) (lty M) ⟩
      < (lty M [ label-to-sub L ]ty) [ connect-susp-inc-right _ _ ]ty >ty ∎
      where
        open Reasoning ty-setoid

    open Reasoning stm-setoid

extend-map-pext : (a : STm (someTree S)) → (L : Label-WT (someTree T) S) → (a >>= map-pext {T = U} L) ≃stm SExt {T = U} (a >>= L)
map-pext-comp : (L : Label (someTree T) S) → (M : Label-WT (someTree U) T)
                → label-comp L (map-pext {T = U′} M) ≃l (SExt {T = U′} ∘ label-comp L M)
map-pext-comp L M .get Z = extend-map-pext (L Z) M

extend-map-pext (SExt a) L = extend-map-pext a (label₁ L)
extend-map-pext (SShift a) L = extend-map-pext a (label₂ L)
extend-map-pext (SPath a) L = refl≃stm
extend-map-pext {U = U} (SCoh S A M) L = begin
  < SCoh S A (label-wt-comp M (map-pext L)) >stm
    ≈⟨ ≃SCoh S refl≃ty (map-pext-comp (ap M) L) lem ⟩
  < SCoh S A (map-pext (label-wt-comp M L)) >stm
    ≈⟨ SCoh-ext S A (label-wt-comp M L) ⟩
  < SExt (SCoh S A (label-wt-comp M L)) >stm ∎
  where
    lem : (lty M [ label-to-sub (map-pext {T = U} L) ]ty) ≃ty
            (suspTy (lty M [ label-to-sub L ]ty) [ connect-susp-inc-left _ (tree-size U) ]ty)
    lem = begin
      < lty M [ label-to-sub (map-pext {T = U} L) ]ty >ty
        ≈⟨ sub-action-≃-ty (refl≃ty {A = lty M}) (label-to-sub-map-pext {U = U} L) ⟩
      < lty M [ connect-susp-inc-left _ (tree-size U) ● suspSubRes (label-to-sub L) ]ty >ty
        ≈⟨ assoc-ty _ _ (lty M) ⟩
      < lty M [ suspSubRes (label-to-sub L) ]ty
          [ connect-susp-inc-left _ (tree-size U) ]ty >ty
        ≈˘⟨ sub-action-≃-ty (susp-res-comp-ty (lty M) (label-to-sub L)) refl≃s ⟩
      < suspTy (lty M [ label-to-sub L ]ty) [ connect-susp-inc-left _ (tree-size U) ]ty
        >ty ∎
      where
        open Reasoning ty-setoid

    open Reasoning stm-setoid
