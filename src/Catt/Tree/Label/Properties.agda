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

_≃l_ : Label X S A → Label Y S B → Set
_≃l_ {S = S} L M = Wrap (λ L M → (P : Path S) → ap L P ≃stm ap M P) L M

refl≃l : L ≃l L
refl≃l = [ (λ P → refl≃stm) ]

≃SHere : S ≃ T → SHere {S = S} ≃stm SHere {S = T}
≃SHere p = [ ≃Here p ]

≃SExt : a ≃stm b → S ≃ T → SExt {T = S} a ≃stm SExt {T = T} b
≃SExt [ p ] q = [ ≃Ext p q ]

≃SShift : S ≃ T → a ≃stm b → SShift {S = S} a ≃stm SShift {S = T} b
≃SShift p [ q ] = [ ≃Shift p q ]

path-to-stm-to-term : (P : Path S) → path-to-term′ P ≃tm path-to-term P
path-to-stm-to-term PHere = refl≃tm
path-to-stm-to-term (PExt P) = sub-action-≃-tm (susp-tm-≃ (path-to-stm-to-term P)) refl≃s
path-to-stm-to-term (PShift P) = sub-action-≃-tm (path-to-stm-to-term P) refl≃s

ppath-≃-≃stm : (p : S ≃ T) → (P : Path S) → path-to-term′ (ppath-≃ p P) ≃tm path-to-term′ P
ppath-≃-≃stm p PHere = ≃Here (sym≃ p)
ppath-≃-≃stm (Join≃ p q) (PExt P) = ≃Ext (ppath-≃-≃stm p P) (sym≃ q)
ppath-≃-≃stm (Join≃ p q) (PShift P) = ≃Shift (sym≃ p) (ppath-≃-≃stm q P)

label-to-sub-≃ : (L : Label X S A) → (M : Label Y S B) → (L ≃l M) → A ≃ty B → label-to-sub L ≃s label-to-sub M
label-to-sub-≃ {S = Sing} L M [ p ] q = Ext≃ (Null≃ q) (p PHere .get)
label-to-sub-≃ {S = Join S T} L M [ p ] q
  = sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ (label₁ L) (label₁ M) ([ (λ P → p (PExt P)) ]) (Arr≃ (p PHere .get) q (p (PShift PHere) .get))))
                       (label-to-sub-≃ (label₂ L) (label₂ M) ([ (λ P → p (PShift P)) ]) q)

≃SCoh : (S : Tree n) → A ≃ty A′ → ∀ {L : Label X S B} {M : Label X S C} → L ≃l M → B ≃ty C → SCoh S A L ≃stm SCoh S A′ M
≃SCoh S p q r = [ sub-action-≃-tm (Coh≃ refl≃c p refl≃s) (label-to-sub-≃ _ _ q r) ]

label-sub-to-sub : {X : MaybeTree n} → (L : Label X S A) → (σ : Sub n m B) → label-to-sub (label-sub L σ) ≃s σ ∘ label-to-sub L
label-sub-to-sub {S = Sing} L σ = refl≃s
label-sub-to-sub {S = Join S T} L σ = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (label-sub L σ))))
                     (label-to-sub (label₂ (label-sub L σ))) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (σ ∘ unrestrict (label-to-sub (label₁ L)))
                     (σ ∘ label-to-sub (label₂ L)) >s
    ≈˘⟨ sub-from-connect-sub (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) σ ⟩
  < σ ∘ label-to-sub L >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (label₁ (label-sub L σ))) ≃s (σ ∘ unrestrict (label-to-sub (label₁ L)))
    l1 = begin
      < unrestrict (label-to-sub (label₁ (label-sub L σ))) >s
        ≡⟨⟩
      < unrestrict (label-to-sub (label-sub (label₁ L) σ)) >s
        ≈⟨ unrestrict-≃ (label-sub-to-sub (label₁ L) σ) ⟩
      < unrestrict (σ ∘ label-to-sub (label₁ L)) >s
        ≈⟨ unrestrict-comp-higher σ (label-to-sub (label₁ L)) ⟩
      < σ ∘ unrestrict (label-to-sub (label₁ L)) >s ∎

    l2 : label-to-sub (label₂ (label-sub L σ)) ≃s (σ ∘ label-to-sub (label₂ L))
    l2 = begin
      < label-to-sub (label₂ (label-sub L σ)) >s
        ≡⟨⟩
      < label-to-sub (label-sub (label₂ L) σ) >s
        ≈⟨ label-sub-to-sub (label₂ L) σ ⟩
      < σ ∘ label-to-sub (label₂ L) >s ∎

label-to-sub-stm : (L : Label X S A) → (a : STm (someTree S)) → stm-to-term a [ label-to-sub L ]tm ≃tm stm-to-term (a >>= L)
label-comp-to-sub : (L : Label (someTree T) S A) → (M : Label X T B) → label-to-sub M ∘ label-to-sub L ≃s label-to-sub (label-comp L M)
label-to-sub-lem : (L : Label X (Join S T) A) → getSnd [ unrestrict (label-to-sub (label₁ L)) ]tm ≃tm Var (fromℕ m) [ label-to-sub (label₂ L) ]tm

label-to-sub-stm {S = Sing} L SHere = refl≃tm
label-to-sub-stm {S = Sing} L (SCoh S A M) = begin
  < Coh (tree-to-ctx S) A idSub [ label-to-sub M ]tm
                                [ label-to-sub L ]tm >tm
    ≈˘⟨ assoc-tm (label-to-sub L) (label-to-sub M) (Coh (tree-to-ctx S) A idSub) ⟩
  < Coh (tree-to-ctx S) A idSub [ label-to-sub L ∘ label-to-sub M ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) A idSub}) (label-comp-to-sub M L) ⟩
  < Coh (tree-to-ctx S) A idSub [ label-to-sub (label-comp M L) ]tm >tm ∎
  where
    open Reasoning tm-setoid
label-to-sub-stm {S = Join S T} L SHere = begin
  < Var (fromℕ _) [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]tm >tm
    ≈⟨ sub-from-connect-fst-var (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < getFst [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
    ≈⟨ unrestrict-fst (label-to-sub (label₁ L)) ⟩
  < apt L PHere >tm ∎
  where
    open Reasoning tm-setoid
label-to-sub-stm {S = Join S T} L (SExt a) = begin
  < suspTm (stm-to-term a) [ connect-susp-inc-left _ _ ]tm
                            [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (suspTm (stm-to-term a)) ⟩
  < suspTm (stm-to-term a) [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L))
                            ∘ connect-susp-inc-left _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = suspTm (stm-to-term a)}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L))) ⟩
  < suspTm (stm-to-term a) [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
    ≈⟨ unrestrict-comp-tm (stm-to-term a) (label-to-sub (label₁ L)) ⟩
  < stm-to-term a [ label-to-sub (label₁ L) ]tm >tm
    ≈⟨ label-to-sub-stm (label₁ L) a ⟩
  < stm-to-term (a >>= label₁ L) >tm ∎
  where
    open Reasoning tm-setoid
label-to-sub-stm {S = Join S T} L (SShift a) = begin
  < stm-to-term a [ connect-susp-inc-right _ _ ]tm
                   [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                      (label-to-sub (label₂ L)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (stm-to-term a) ⟩
  < stm-to-term a [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                      (label-to-sub (label₂ L))
                   ∘ connect-susp-inc-right _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L)) (label-to-sub-lem L)) ⟩
  < stm-to-term a [ label-to-sub (label₂ L) ]tm >tm
    ≈⟨ label-to-sub-stm (label₂ L) a ⟩
  < stm-to-term (a >>= label₂ L) >tm ∎
  where
    open Reasoning tm-setoid
label-to-sub-stm {S = Join S T} L (SCoh U A M) = begin
  < Coh (tree-to-ctx U) A idSub [ label-to-sub M ]tm
                                [ label-to-sub L ]tm >tm
    ≈˘⟨ assoc-tm (label-to-sub L) (label-to-sub M) (Coh (tree-to-ctx U) A idSub) ⟩
  < Coh (tree-to-ctx U) A idSub [ label-to-sub L ∘ label-to-sub M ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx U) A idSub}) (label-comp-to-sub M L) ⟩
  < Coh (tree-to-ctx U) A idSub [ label-to-sub (label-comp M L) ]tm >tm ∎
  where
    open Reasoning tm-setoid

label-comp-to-sub L M = begin
  < label-to-sub M ∘ label-to-sub L >s
    ≈˘⟨ label-sub-to-sub L (label-to-sub M) ⟩
  < label-to-sub (label-sub L (label-to-sub M)) >s
    ≈⟨ label-to-sub-≃ (label-sub L (label-to-sub M)) (label-comp L M) ([ (λ P → [ label-to-sub-stm M (ap L P) ] ) ]) refl≃ty ⟩
  < label-to-sub (label-comp L M) >s ∎
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

extend-≃ : (a ≃stm b) → L ≃l M → lty L ≃ty lty M → (a >>= L) ≃stm (b >>= M)
extend-≃ {a = a} {b = b} {L = L} {M = M} [ p ] q r = [ begin
  < stm-to-term (a >>= L) >tm
    ≈˘⟨ label-to-sub-stm L a ⟩
  < stm-to-term a [ label-to-sub L ]tm >tm
    ≈⟨ sub-action-≃-tm p (label-to-sub-≃ L M q r) ⟩
  < stm-to-term b [ label-to-sub M ]tm >tm
    ≈⟨ label-to-sub-stm M b ⟩
  < stm-to-term (b >>= M) >tm ∎ ]
  where
    open Reasoning tm-setoid

extend-path-to-stm : (P : Path S) → (L : Label X S A) → (path-to-stm P >>= L) ≃stm ap L P
extend-path-to-stm PHere L = refl≃stm
extend-path-to-stm (PExt P) L = extend-path-to-stm P (label₁ L)
extend-path-to-stm (PShift P) L = extend-path-to-stm P (label₂ L)

label-comp-assoc : (L : Label (someTree S) U A) → (M : Label (someTree T) S B) → (N : Label X T C) → label-comp (label-comp L M) N ≃l label-comp L (label-comp M N)
extend-assoc : (a : STm (someTree S)) → (L : Label (someTree T) S A) → (M : Label X T B) → (a >>= L >>= M) ≃stm (a >>= label-comp L M)

label-comp-assoc L M N .get Z = extend-assoc (ap L Z) M N

extend-assoc SHere L M = refl≃stm
extend-assoc (SExt a) L M = begin
  < a >>= label₁ L >>= M >stm
    ≈⟨ extend-assoc a (label₁ L) M ⟩
  < a >>= label-comp (label₁ L) M >stm
    ≈⟨ extend-≃ (refl≃stm {a = a}) [ (λ P → refl≃stm) ] (Arr≃ (label-to-sub-stm M (ap L PHere)) refl≃ty (label-to-sub-stm M (ap L (PShift PHere)))) ⟩
  < a >>= label₁ (label-comp L M) >stm ∎
  where
    open Reasoning stm-setoid
extend-assoc (SShift a) L M = extend-assoc a (label₂ L) M
extend-assoc (SCoh {B = B} S A L′) L M = ≃SCoh S refl≃ty (label-comp-assoc L′ L M) (begin
  < B [ label-to-sub L ]ty [ label-to-sub M ]ty >ty
    ≈˘⟨ assoc-ty (label-to-sub M) (label-to-sub L) B ⟩
  < B [ label-to-sub M ∘ label-to-sub L ]ty >ty
    ≈⟨ sub-action-≃-ty (refl≃ty {A = B}) (label-comp-to-sub L M) ⟩
  < B [ label-to-sub (label-comp L M) ]ty >ty ∎)
  where
    open Reasoning ty-setoid

label-to-sub-path : (L : Label X S A) → (P : Path S) → path-to-term P [ label-to-sub L ]tm ≃tm apt L P
label-to-sub-path L P = begin
  < path-to-term P [ label-to-sub L ]tm >tm
    ≈˘⟨ sub-action-≃-tm (path-to-stm-to-term P) refl≃s ⟩
  < stm-to-term (path-to-stm P) [ label-to-sub L ]tm >tm
    ≈⟨ label-to-sub-stm L (path-to-stm P) ⟩
  < stm-to-term (path-to-stm P >>= L) >tm
    ≈⟨ extend-path-to-stm P L .get ⟩
  < apt L P >tm ∎
  where
    open Reasoning tm-setoid

connect-tree-inc-left-phere : (S : Tree n)
                            → (T : Tree m)
                            → ap (connect-tree-inc-left S T) PHere ≃stm SHere {S = connect-tree S T}
connect-tree-inc-left-phere Sing T = refl≃stm
connect-tree-inc-left-phere (Join S₁ S₂) T = refl≃stm

connect-tree-inc-phere : (S : Tree n)
                       → (T : Tree m)
                       → ap (connect-tree-inc-left S T) (last-path S) ≃stm ap (connect-tree-inc-right S T) PHere
connect-tree-inc-phere Sing T = refl≃stm
connect-tree-inc-phere (Join S₁ S₂) T = ≃SShift refl≃ (connect-tree-inc-phere S₂ T)

susp-stm-to-term : (a : STm X) → stm-to-term (susp-stm a) ≃tm suspTm (stm-to-term a)
susp-label-to-sub′ : (L : Label X S A) → ((P : Path S) → apt (susp-label L) P ≃tm suspTm (apt L P)) → label-to-sub (susp-label L) ≃s suspSubRes (label-to-sub L)
susp-label-to-sub : (L : Label X S A) → label-to-sub (susp-label L) ≃s suspSubRes (label-to-sub L)

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
susp-label-to-sub′ {S = Join S T} {A = A} L f = begin
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

lift-stm-to-term : (a : STm (Other n)) → stm-to-term (lift-stm a) ≃tm liftTerm (stm-to-term a)
lift-label-to-sub′ : (L : Label (Other n) S A) → ((P : Path S) → apt (lift-label L) P ≃tm liftTerm (apt L P)) → label-to-sub (lift-label L) ≃s liftSub (label-to-sub L)
lift-label-to-sub : (L : Label (Other n) S A) → label-to-sub (lift-label L) ≃s liftSub (label-to-sub L)

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

id-label-to-sub : (S : Tree n) → label-to-sub (id-label S) ≃s idSub {n = suc n}
id-label-to-sub Sing = refl≃s
id-label-to-sub (Join S T) = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (id-label (Join S T)))))
                                 (label-to-sub (label₂ (id-label (Join S T)))) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (connect-susp-inc-left _ _) (connect-susp-inc-right _ _) >s
    ≈⟨ sub-from-connect-prop getSnd ⟩
  < idSub >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (label₁ (id-label (Join S T)))) ≃s connect-susp-inc-left (tree-size S) (tree-size T)
    l1 = begin
      < unrestrict (label-to-sub (label₁ (id-label (Join S T)))) >s
        ≈˘⟨ unrestrict-≃ (label-to-sub-≃ (label-sub (susp-label (id-label S))
                                                    (connect-susp-inc-left (tree-size S) (tree-size T)))
                                         (label₁ (id-label (Join S T)))
                                         [ (λ P → [ sub-action-≃-tm (id-on-tm (suspTm (stm-to-term (path-to-stm P)))) refl≃s ]) ]
                                         (Arr≃ (connect-inc-left-fst-var getSnd (tree-size T))
                                               refl≃ty
                                               (connect-inc-fst-var getSnd (tree-size T)))) ⟩
      < unrestrict (label-to-sub (label-sub (susp-label (id-label S)) (connect-susp-inc-left (tree-size S) (tree-size T)))) >s
        ≈⟨ unrestrict-≃ (label-sub-to-sub (susp-label (id-label S)) (connect-susp-inc-left (tree-size S) (tree-size T))) ⟩
      < unrestrict (connect-susp-inc-left (tree-size S) (tree-size T) ∘ label-to-sub (susp-label (id-label S))) >s
        ≈⟨ unrestrict-comp-higher (connect-susp-inc-left (tree-size S) (tree-size T)) (label-to-sub (susp-label (id-label S))) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ∘ unrestrict (label-to-sub (susp-label (id-label S))) >s
        ≈⟨ sub-action-≃-sub (unrestrict-≃ (susp-label-to-sub (id-label S))) refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ∘ suspSub (label-to-sub (id-label S)) >s
        ≈⟨ sub-action-≃-sub (susp-sub-≃ (id-label-to-sub S)) refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ∘ suspSub idSub >s
        ≈⟨ sub-action-≃-sub susp-functorial-id refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ∘ idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-left (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) >s ∎

    l2 : label-to-sub (label₂ (id-label (Join S T))) ≃s connect-susp-inc-right (tree-size S) (tree-size T)
    l2 = begin
      < label-to-sub (label₂ (id-label (Join S T))) >s
        ≈⟨ label-to-sub-≃ (label₂ (id-label (Join S T))) (label-sub (id-label T) (connect-susp-inc-right (tree-size S) (tree-size T))) [ (λ P → [ refl≃tm ]) ] refl≃ty ⟩
      < label-to-sub (label-sub (id-label T) (connect-susp-inc-right (tree-size S) (tree-size T))) >s
        ≈⟨ label-sub-to-sub (id-label T) (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ∘ label-to-sub (id-label T) >s
        ≈⟨ sub-action-≃-sub (id-label-to-sub T) refl≃s ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ∘ idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) >s ∎

sub-to-label-to-sub : (S : Tree n) → (σ : Sub (suc n) m A) → label-to-sub (to-label S σ) ≃s σ
sub-to-label-to-sub S σ = begin
  < label-to-sub (to-label S σ) >s
    ≈˘⟨ label-to-sub-≃ (label-sub (id-label S) σ) (to-label S σ) [ (λ P → [ sub-action-≃-tm (path-to-stm-to-term P) refl≃s ]) ] refl≃ty ⟩
  < label-to-sub (label-sub (id-label S) σ) >s
    ≈⟨ label-sub-to-sub (id-label S) σ ⟩
  < σ ∘ label-to-sub (id-label S) >s
    ≈⟨ sub-action-≃-sub (id-label-to-sub S) refl≃s ⟩
  < σ ∘ idSub >s
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

_≃lm_ : (L : Label X S A) → (M : Label Y S B) → Set
_≃lm_ {S = S} L M = Wrap (λ L M → ∀ (Q : Path S) → .⦃ is-Maximal Q ⦄ → ap L Q ≃stm ap M Q) L M

replace-not-here : (L : Label X S A) → (a : STm X) → (P : Path S) → .⦃ not-here P ⦄ → ap (replace-label L a) P ≃stm ap L P
replace-not-here L a (PExt P) = refl≃stm
replace-not-here L a (PShift P) = refl≃stm

connect-label-phere : (L : Label X S A)
                    → (M : Label X T A)
                    → apt (connect-label L M) PHere ≃tm apt L PHere
connect-label-phere {S = Sing} L M = refl≃tm
connect-label-phere {S = Join S₁ S₂} L M = refl≃tm

connect-label-inc-left : (L : Label X S A)
                       → (M : Label X T A)
                       → (label-comp (connect-tree-inc-left S T) (connect-label L M)) ≃l L
connect-label-inc-left {S = Sing} L M .get PHere = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M .get PHere = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M .get (PExt Q) = extend-path-to-stm (PExt Q) (connect-label L M)
connect-label-inc-left {S = Join S₁ S₂} L M .get (PShift Q) = connect-label-inc-left (label₂ L) M .get Q

connect-label-inc-right : (L : Label X S A)
                        → (M : Label X T A)
                        → (Z : Path T) → .⦃ not-here Z ⦄ → .⦃ is-Maximal Z ⦄ → (label-comp (connect-tree-inc-right S T) (connect-label L M)) .ap Z ≃stm ap M Z
connect-label-inc-right {S = Sing} L M Z = begin
  < path-to-stm Z >>= replace-label M (ap L PHere) >stm
    ≈⟨ extend-path-to-stm Z (replace-label M (ap L PHere)) ⟩
  < ap (replace-label M (ap L PHere)) Z >stm
    ≈⟨ replace-not-here M (ap L PHere) Z ⟩
  < ap M Z >stm ∎
  where
    open Reasoning stm-setoid
connect-label-inc-right {S = Join S₁ S₂} L M Z = connect-label-inc-right (label₂ L) M Z

replace-label-map-func : (f : STm X → STm Y) → (L : Label-func X S) → (a : STm X) → (Z : Path S) → map-lf f (replace-label-func L a) Z ≃stm replace-label-func (map-lf f L) (f a) Z
replace-label-map-func f L P PHere = refl≃stm
replace-label-map-func f L P (PExt Z) = refl≃stm
replace-label-map-func f L P (PShift Z) = refl≃stm

connect-label-map-func : (f : STm X → STm Y) → (L : Label-func X S) → (M : Label-func X T) → (Z : Path (connect-tree S T)) → map-lf f (connect-label-func L M) Z ≃stm connect-label-func (map-lf f L) (map-lf f M) Z
connect-label-map-func {S = Sing} f L M = replace-label-map-func f M (L PHere)
connect-label-map-func {S = Join S₁ S₂} f L M PHere = refl≃stm
connect-label-map-func {S = Join S₁ S₂} f L M (PExt Z) = refl≃stm
connect-label-map-func {S = Join S₁ S₂} f L M (PShift Z) = connect-label-map-func f (λ X → L (PShift X)) M Z

replace-label-prop : (L : Label X S A) → replace-label L (ap L PHere) ≃l L
replace-label-prop L .get PHere = [ refl≃tm ]
replace-label-prop L .get (PExt Q) = [ refl≃tm ]
replace-label-prop L .get (PShift Q) = [ refl≃tm ]

connect-label-prop : (S : Tree n) → (T : Tree m) → connect-label (connect-tree-inc-left S T) (connect-tree-inc-right S T) ≃l id-label (connect-tree S T)
connect-label-prop Sing T = replace-label-prop (id-label T)
connect-label-prop (Join S₁ S₂) T .get PHere = refl≃stm
connect-label-prop (Join S₁ S₂) T .get (PExt Z) = refl≃stm
connect-label-prop (Join S₁ S₂) T .get (PShift Z) = trans≃stm (sym≃stm (connect-label-map-func SShift (connect-tree-inc-left S₂ T .ap) (connect-tree-inc-right S₂ T .ap) Z)) (≃SShift refl≃ (connect-label-prop S₂ T .get Z))

label-≃ : S ≃ T → Label X T A → Label X S A
label-≃ p L .ap Z = ap L (ppath-≃ p Z)

_≃l′_ : Label X S A → Label Y T B → Set
_≃l′_ {S = S} {T = T} L M = Σ[ p ∈ S ≃ T ] L ≃l label-≃ p M

label-to-sub-≃′ : (L : Label X S A) → (M : Label Y T B) → L ≃l′ M → A ≃ty B → label-to-sub L ≃s label-to-sub M
label-to-sub-≃′ L M (p ,, [ q ]) r with ≃-to-same-n p
... | refl with ≃-to-≡ p
... | refl = label-to-sub-≃ L M [ (λ P → trans≃stm (q P) (lem P)) ] r
  where
    open Reasoning tm-setoid
    lem : (P : Path _) → ap M (ppath-≃ p P) ≃stm ap M P
    lem P = [ begin
      < apt M (ppath-≃ p P) >tm
        ≈˘⟨ label-to-sub-path M (ppath-≃ p P) ⟩
      < path-to-term (ppath-≃ p P) [ label-to-sub M ]tm >tm
        ≈⟨ sub-action-≃-tm (ppath-≃-≃tm p P) refl≃s ⟩
      < path-to-term P [ label-to-sub M ]tm >tm
        ≈⟨ label-to-sub-path M P ⟩
      < apt M P >tm ∎ ]

-- extend-susp-label : (a : STm (someTree S)) → (L : Label X S A) → susp-stm (a >>= L) ≃stm (a >>= susp-label L)
-- extend-susp-label a L = [ begin
--   < stm-to-term (susp-stm (a >>= L)) >tm
--     ≈⟨ susp-stm-to-term (a >>= L) ⟩
--   < suspTm (stm-to-term (a >>= L)) >tm
--     ≈˘⟨ susp-tm-≃ (label-to-sub-stm L a) ⟩
--   < suspTm (stm-to-term a [ label-to-sub L ]tm) >tm
--     ≈⟨ susp-res-comp-tm (stm-to-term a) (label-to-sub L) ⟩
--   < stm-to-term a [ suspSubRes (label-to-sub L) ]tm >tm
--     ≈˘⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (susp-label-to-sub L) ⟩
--   < stm-to-term a [ label-to-sub (susp-label L) ]tm >tm
--     ≈⟨ label-to-sub-stm (susp-label L) a ⟩
--   < stm-to-term (a >>= susp-label L) >tm ∎ ]
--   where
--     open Reasoning tm-setoid
