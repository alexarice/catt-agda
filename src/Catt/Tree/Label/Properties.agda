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

_≃sty_ : (a : STy X) → (b : STy Y) → Set
a ≃sty b = Wrap (λ a b → sty-to-type a ≃ty sty-to-type b) a b

refl≃sty : {A : STy X} → A ≃sty A
refl≃sty = [ refl≃ty ]

reflexive≃sty : {A : STy X} → {B : STy X} → A ≡ B → A ≃sty B
reflexive≃sty refl = refl≃sty

sym≃sty : {A : STy X} → {B : STy Y} → A ≃sty B → B ≃sty A
sym≃sty [ p ] = [ sym≃ty p ]

trans≃sty : {A : STy X} → {B : STy Y} → {C : STy Z} → A ≃sty B → B ≃sty C → A ≃sty C
trans≃sty [ p ] [ q ] = [ trans≃ty p q ]

record STY : Set where
  constructor <_>sty
  field
    {sty-n} : ℕ
    {sty-X} : MaybeTree sty-n
    sty : STy sty-X

open STY public

sty-setoid : Setoid _ _
sty-setoid = record { Carrier = STY
                    ; _≈_ = λ x y → sty x ≃sty sty y
                    ; isEquivalence = record { refl = refl≃sty
                                             ; sym = sym≃sty
                                             ; trans = trans≃sty
                                             }
                    }

≃SArr : {A : STy X} → {B : STy Y} → (a ≃stm a′) → A ≃sty B → b ≃stm b′ → SArr a A b ≃sty SArr a′ B b′
≃SArr [ p ] [ q ] [ r ] = [ Arr≃ p q r ]

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

label-to-sub-≃ : (L : Label-WT X S) → (M : Label-WT Y S) → (ap L ≃l ap M) → lty L ≃sty lty M → label-to-sub L ≃s label-to-sub M
label-to-sub-≃ {S = Sing} L M [ p ] q = Ext≃ (Null≃ (q .get)) (p PHere .get)
label-to-sub-≃ {S = Join S T} L M [ p ] q
  = sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ (label₁ L) (label₁ M) ([ (λ P → p (PExt P)) ]) (≃SArr (p PHere) q (p (PShift PHere)))))
                       (label-to-sub-≃ (label₂ L) (label₂ M) ([ (λ P → p (PShift P)) ]) q)

≃SCoh : (S : Tree n) → {A A′ : STy (someTree S)} → A ≃sty A′ → ∀ {L : Label-WT X S} {M : Label-WT X S} → ap L ≃l ap M → lty L ≃sty lty M → SCoh S A L ≃stm SCoh S A′ M
≃SCoh S p q r = [ sub-action-≃-tm (Coh≃ refl≃c (p .get) refl≃s) (label-to-sub-≃ _ _ q r) ]

to-sty-to-type : (A : Ty n) → sty-to-type (to-sty A) ≃ty A
to-sty-to-type ⋆ = refl≃ty
to-sty-to-type (s ─⟨ A ⟩⟶ t) = Arr≃ refl≃tm (to-sty-to-type A) refl≃tm

sty-sub-prop : {X : MaybeTree n} → (A : STy X) → (σ : Sub n m B) → sty-to-type (sty-sub A σ) ≃ty sty-to-type A [ σ ]ty
sty-sub-prop S⋆ σ = to-sty-to-type (sub-type σ)
sty-sub-prop (SArr s A t) σ = Arr≃ refl≃tm (sty-sub-prop A σ) refl≃tm

label-sub-to-sub : {X : MaybeTree n} → (L : Label-WT X S) → (σ : Sub n m B) → label-to-sub (label-sub L σ) ≃s σ ● label-to-sub L
label-sub-to-sub {S = Sing} L σ = Ext≃ (Null≃ (sty-sub-prop (lty L) σ)) refl≃tm
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
  < Coh (tree-to-ctx U) (sty-to-type A) idSub [ label-to-sub M ]tm
                                [ label-to-sub L ]tm >tm
    ≈˘⟨ assoc-tm (label-to-sub L) (label-to-sub M) (Coh (tree-to-ctx U) (sty-to-type A) idSub) ⟩
  < Coh (tree-to-ctx U) (sty-to-type A) idSub [ label-to-sub L ● label-to-sub M ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx U) (sty-to-type A) idSub}) (label-comp-to-sub M L) ⟩
  < Coh (tree-to-ctx U) (sty-to-type A) idSub [ label-to-sub (label-wt-comp M L) ]tm >tm ∎
  where
    open Reasoning tm-setoid

label-to-sub-sty : (L : Label-WT X S) → (A : STy (someTree S)) → sty-to-type A [ label-to-sub L ]ty ≃ty sty-to-type (label-on-sty A L)
label-to-sub-sty L S⋆ = refl≃ty
label-to-sub-sty L (SArr s A t) = Arr≃ (label-to-sub-stm L s) (label-to-sub-sty L A) (label-to-sub-stm L t)

sty-label-to-sub : (L : Label-WT X S) → (A : STy (someTree S)) → sty-sub A (label-to-sub L) ≃sty label-on-sty A L
sty-label-to-sub L S⋆ = [ (to-sty-to-type (sty-to-type (lty L))) ]
sty-label-to-sub L (SArr s A t) = ≃SArr [ label-to-sub-stm L s ] (sty-label-to-sub L A) [ label-to-sub-stm L t ]

label-comp-to-sub L M = begin
  < label-to-sub M ● label-to-sub L >s
    ≈˘⟨ label-sub-to-sub L (label-to-sub M) ⟩
  < label-to-sub (label-sub L (label-to-sub M)) >s
    ≈⟨ label-to-sub-≃ (label-sub L (label-to-sub M)) (label-wt-comp L M) ([ (λ P → [ label-to-sub-stm M (ap L P) ] ) ]) (sty-label-to-sub M (lty L)) ⟩
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

extend-≃ : {A : STy X} → {B : STy Y} → (a ≃stm b) → L ≃l M → A ≃sty B → (a >>= L ,, A) ≃stm (b >>= M ,, B)
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

label-comp-≃ : {L L′ : Label (someTree T) S} → {M : Label-WT X T} → {M′ : Label-WT Y T} → L ≃l L′ → ap M ≃l ap M′ → lty M ≃sty lty M′ → label-comp L M ≃l label-comp L′ M′
label-comp-≃ p q r .get Z = extend-≃ (ap-≃ p refl≃p) q r

label-comp-assoc : (L : Label-WT (someTree S) U) → (M : Label-WT (someTree T) S) → (N : Label-WT X T) → ap (label-wt-comp (label-wt-comp L M) N) ≃l ap (label-wt-comp L (label-wt-comp M N))
extend-assoc : (a : STm (someTree S)) → (L : Label-WT (someTree T) S) → (M : Label-WT X T) → (a >>= L >>= M) ≃stm (a >>= label-wt-comp L M)
label-on-sty-assoc : (A : STy (someTree S)) → (L : Label-WT (someTree T) S) → (M : Label-WT X T) → (label-on-sty (label-on-sty A L) M) ≃sty (label-on-sty A (label-wt-comp L M))

label-comp-assoc L M N .get Z = extend-assoc (ap L Z) M N

extend-assoc (SExt a) L M = extend-assoc a (label₁ L) M
extend-assoc (SShift a) L M = extend-assoc a (label₂ L) M
extend-assoc (SPath P) L M = refl≃stm
extend-assoc (SCoh S A L′) L M = ≃SCoh S refl≃sty (label-comp-assoc L′ L M) (label-on-sty-assoc (lty L′) L M)

label-on-sty-assoc S⋆ L M = refl≃sty
label-on-sty-assoc (SArr s A t) L M = ≃SArr (extend-assoc s L M) (label-on-sty-assoc A L M) (extend-assoc t L M)

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
susp-sty-to-type : (A : STy X) → sty-to-type (susp-sty A) ≃ty suspTy (sty-to-type A)
susp-label-to-sub′ : (L : Label-WT X S) → ((P : Path S) → apt (susp-label L) P ≃tm suspTm (apt L P)) → sty-to-type (susp-sty (lty L)) ≃ty suspTy (sty-to-type (lty L)) → label-to-sub (susp-label L) ≃s suspSubRes (label-to-sub L)
susp-label-to-sub : (L : Label-WT X S) → label-to-sub (susp-label L) ≃s suspSubRes (label-to-sub L)

susp-stm-to-term {X = someTree x} a = id-on-tm (suspTm (stm-to-term a))
susp-stm-to-term {X = Other _} (SCoh S A L) = begin
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub (susp-label L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type A) idSub}) (susp-label-to-sub L) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ suspSubRes (label-to-sub L) ]tm >tm
    ≈˘⟨ susp-res-comp-tm (Coh (tree-to-ctx S) (sty-to-type A) idSub) (label-to-sub L) ⟩
  < suspTm (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) >tm ∎
  where
    open Reasoning tm-setoid
susp-stm-to-term {X = Other _} (SOther t) = refl≃tm

susp-sty-to-type (SArr s A t) = Arr≃ (susp-stm-to-term s) (susp-sty-to-type A) (susp-stm-to-term t)
susp-sty-to-type {X = someTree x} S⋆ = refl≃ty
susp-sty-to-type {X = Other _} S⋆ = refl≃ty

susp-label-to-sub′ {S = Sing} L f p = Ext≃ (Null≃ p) (f PHere)
susp-label-to-sub′ {S = Join S T} L f p = begin
  < sub-from-connect (unrestrict (label-to-sub (susp-label (label₁ L))))
                                 (label-to-sub (susp-label (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (susp-label-to-sub′ (label₁ L) (λ P → f (PExt P)) (Arr≃ (f PHere) p (f (PShift PHere)))))
                          (susp-label-to-sub′ (label₂ L) (λ P → f (PShift P)) p) ⟩
  < sub-from-connect (unrestrict (suspSubRes (label-to-sub (label₁ L)))) (suspSubRes (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-≃ (sub-res-unrestrict-comm (label-to-sub (label₁ L))) refl≃s ⟩
  < sub-from-connect (suspSubRes (unrestrict (label-to-sub (label₁ L)))) (suspSubRes (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-susp-res (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < suspSubRes (sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                             (label-to-sub (label₂ L))) >s ∎
  where
    open Reasoning sub-setoid

susp-label-to-sub L = susp-label-to-sub′ L (λ P → susp-stm-to-term (ap L P)) (susp-sty-to-type (lty L))

map-sty-pshift-prop : (A : STy (someTree T)) → map-sty-pshift {S = S} A ≃sty sty-sub A (connect-susp-inc-right (tree-size S) (tree-size T))
map-sty-pshift-prop S⋆ = [ refl≃ty ]
map-sty-pshift-prop (SArr s A t) = ≃SArr [ refl≃tm ] (map-sty-pshift-prop A) [ refl≃tm ]

label-to-sub-map-pshift : (L : Label-WT (someTree T) S) → label-to-sub (map-pshift {S = U} L) ≃s connect-susp-inc-right (tree-size U) (tree-size T) ● label-to-sub L
label-to-sub-map-pshift {U = U} L = begin
  < label-to-sub (map-pshift {S = U} L) >s
    ≈⟨ label-to-sub-≃ (map-pshift {S = U} L) (label-sub L (connect-susp-inc-right (tree-size U) _)) [ (λ P → [ refl≃tm ]) ] (map-sty-pshift-prop {S = U} (lty L)) ⟩
  < label-to-sub (label-sub L (connect-susp-inc-right (tree-size U) _)) >s
    ≈⟨ label-sub-to-sub L (connect-susp-inc-right (tree-size U) _) ⟩
  < connect-susp-inc-right (tree-size U) _ ● label-to-sub L >s ∎
  where
    open Reasoning sub-setoid

map-sty-pext-prop : (A : STy (someTree S)) → (sty-sub (susp-sty A)) (connect-susp-inc-left (tree-size S) (tree-size T)) ≃sty map-sty-pext {T = T} A
map-sty-pext-prop S⋆ = ≃SArr [ (connect-inc-left-fst-var getSnd _) ] [ refl≃ty ] [ connect-inc-fst-var getSnd _ ]
map-sty-pext-prop (SArr s A t) = ≃SArr [ sub-action-≃-tm (id-on-tm (suspTm (stm-to-term s))) refl≃s ] (map-sty-pext-prop A) [ sub-action-≃-tm (id-on-tm (suspTm (stm-to-term t))) refl≃s ]

label-to-sub-map-pext : (L : Label-WT (someTree T) S) → label-to-sub (map-pext {T = U} L) ≃s connect-susp-inc-left (tree-size T) (tree-size U) ● suspSubRes (label-to-sub L)
label-to-sub-map-pext {U = U} L = begin
  < label-to-sub (map-pext {T = U} L) >s
    ≈˘⟨ label-to-sub-≃ (label-sub (susp-label L) (connect-susp-inc-left _ (tree-size U)))
                       (map-pext {T = U} L)
                       [ (λ P → [ sub-action-≃-tm (id-on-tm (suspTm (stm-to-term (ap L P)))) refl≃s ]) ]
                       (map-sty-pext-prop (lty L)) ⟩
  < label-to-sub (label-sub (susp-label L) (connect-susp-inc-left _ (tree-size U))) >s
    ≈⟨ label-sub-to-sub (susp-label L) (connect-susp-inc-left _ (tree-size U)) ⟩
  < connect-susp-inc-left _ (tree-size U) ● label-to-sub (susp-label L) >s
    ≈⟨ sub-action-≃-sub (susp-label-to-sub L) refl≃s ⟩
  < connect-susp-inc-left _ (tree-size U) ● suspSubRes (label-to-sub L) >s ∎
  where
    open Reasoning sub-setoid

lift-stm-to-term : (a : STm (Other n)) → stm-to-term (lift-stm a) ≃tm liftTerm (stm-to-term a)
lift-sty-to-type : (A : STy (Other n)) → sty-to-type (lift-sty A) ≃ty liftType (sty-to-type A)
lift-label-to-sub′ : (L : Label-WT (Other n) S) → ((P : Path S) → apt (lift-label L) P ≃tm liftTerm (apt L P)) → sty-to-type (lift-sty (lty L)) ≃ty liftType (sty-to-type (lty L)) → label-to-sub (lift-label L) ≃s liftSub (label-to-sub L)
lift-label-to-sub : (L : Label-WT (Other n) S) → label-to-sub (lift-label L) ≃s liftSub (label-to-sub L)

lift-stm-to-term (SCoh S A L) = begin
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub (lift-label L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type A) idSub}) (lift-label-to-sub L) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ liftSub (label-to-sub L) ]tm >tm
    ≈⟨ apply-lifted-sub-tm-≃ (Coh (tree-to-ctx S ) (sty-to-type A) idSub) (label-to-sub L) ⟩
  < liftTerm (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) >tm ∎
  where
    open Reasoning tm-setoid
lift-stm-to-term (SOther t) = refl≃tm

lift-sty-to-type S⋆ = refl≃ty
lift-sty-to-type (SArr s A t) = Arr≃ (lift-stm-to-term s) (lift-sty-to-type A) (lift-stm-to-term t)

lift-label-to-sub′ {S = Sing} L f p = Ext≃ (Null≃ p) (f PHere)
lift-label-to-sub′ {S = Join S T} L f p = begin
  < sub-from-connect (unrestrict (label-to-sub (lift-label (label₁ L)))) (label-to-sub (lift-label (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (lift-label-to-sub′ (label₁ L) (λ P → f (PExt P)) (Arr≃ (f PHere) p (f (PShift PHere))))) (lift-label-to-sub′ (label₂ L) (λ P → f (PShift P)) p) ⟩
  < sub-from-connect (unrestrict (liftSub (label-to-sub (label₁ L)))) (liftSub (label-to-sub (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-lift (label-to-sub (label₁ L))) (refl≃s {σ = liftSub (label-to-sub (label₂ L))}) ⟩
  < sub-from-connect (liftSub (unrestrict (label-to-sub (label₁ L)))) (liftSub (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-lift (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < liftSub (sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))) >s ∎
  where
    open Reasoning sub-setoid

lift-label-to-sub L = lift-label-to-sub′ L (λ P → lift-stm-to-term (ap L P)) (lift-sty-to-type (lty L))

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
      < unrestrict (label-to-sub (map-pext {T = T} (id-label-wt S))) >s
        ≈⟨ unrestrict-≃ (label-to-sub-map-pext {U = T} (id-label-wt S)) ⟩
      < unrestrict (connect-susp-inc-left (tree-size S) (tree-size T)
                   ● suspSubRes (label-to-sub (id-label-wt S))) >s
        ≈⟨ unrestrict-comp-higher (connect-susp-inc-left (tree-size S) (tree-size T)) (suspSubRes (label-to-sub (id-label-wt S))) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● suspSub (label-to-sub (id-label-wt S)) >s
        ≈⟨ sub-action-≃-sub (susp-sub-≃ (id-label-to-sub S)) refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● suspSub idSub >s
        ≈⟨ sub-action-≃-sub susp-functorial-id refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-left (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) >s ∎

    l2 : label-to-sub (label₂ (id-label-wt (Join S T))) ≃s connect-susp-inc-right (tree-size S) (tree-size T)
    l2 = begin
      < label-to-sub (map-pshift {S = S} (id-label-wt T)) >s
        ≈⟨ label-to-sub-map-pshift {U = S} (id-label-wt T) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ● label-to-sub (id-label-wt T) >s
        ≈⟨ sub-action-≃-sub (id-label-to-sub T) refl≃s ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ● idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) >s ∎

sub-to-label-to-sub : (S : Tree n) → (σ : Sub (suc n) m A) → label-to-sub (to-label S σ ,, to-sty A) ≃s σ
sub-to-label-to-sub {A = A} S σ = begin
  < label-to-sub (to-label S σ ,, to-sty A) >s
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
                       → (A : STy X)
                       → (label-comp (ap (connect-tree-inc-left S T)) (connect-label L M ,, A)) ≃l L
connect-label-inc-left {S = Sing} L M A .get PHere = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get PHere = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get (PExt Q) = refl≃stm
connect-label-inc-left {S = Join S₁ S₂} L M A .get (PShift Q) = connect-label-inc-left (L ∘ PShift) M A .get Q

connect-label-inc-right : (L : Label X S)
                        → (M : Label X T)
                        → (A : STy X)
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

label-≃-sym : (p : S ≃′ T) → L ≃l label-≃ p M → label-≃ (sym≃′ p) L ≃l M
label-≃-sym {L = L} {M = M} p q .get Z = begin
  < L (ppath-≃ (sym≃′ p) Z) >stm
    ≈⟨ q .get (ppath-≃ (sym≃′ p) Z) ⟩
  < M (ppath-≃ p (ppath-≃ (sym≃′ p) Z)) >stm
    ≈˘⟨ ap-≃ (refl≃l {L = M}) (trans≃p (ppath-≃-≃p (sym≃′ p) Z) (ppath-≃-≃p p (ppath-≃ (sym≃′ p) Z))) ⟩
  < M Z >stm ∎
  where
    open Reasoning stm-setoid

_≃l′_ : Label X S → Label Y T → Set
_≃l′_ {S = S} {T = T} L M = Σ[ p ∈ S ≃′ T ] L ≃l label-≃ p M

label-to-sub-≃′ : (L : Label-WT X S) → (M : Label-WT Y T) → ap L ≃l′ ap M → lty L ≃sty lty M → label-to-sub L ≃s label-to-sub M
label-to-sub-≃′ L M (p ,, [ q ]) r with ≃-to-same-n (≃′-to-≃ p)
... | refl with ≃-to-≡ (≃′-to-≃ p)
... | refl = label-to-sub-≃ L M [ (λ P → trans≃stm (q P) (ap-≃ (refl≃l {L = ap M}) (sym≃p (ppath-≃-≃p p P)))) ] r

extend-≃′ : {L : Label-WT X S} → {M : Label-WT Y T} → a ≃stm b → ap L ≃l′ ap M → lty L ≃sty lty M → (a >>= L) ≃stm (b >>= M)
extend-≃′ {M = M} p (q ,, q′) r with ≃-to-same-n (≃′-to-≃ q)
... | refl with ≃-to-≡ (≃′-to-≃ q)
... | refl = extend-≃ p (trans≃l q′ [ (λ P → ap-≃ (refl≃l {L = ap M}) (sym≃p (ppath-≃-≃p q P))) ]) r

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

SCoh-shift : (S : Tree n) → (A : STy (someTree S)) → (L : Label-WT (someTree T) S) → SCoh S A (map-pshift {S = U} L) ≃stm SShift {S = U} (SCoh S A L)
SCoh-shift {U = U} S A L .get = begin
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub (map-pshift {S = U} L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type A) idSub}) (label-to-sub-map-pshift {U = U} L) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ connect-susp-inc-right _ _ ● label-to-sub L ]tm
    >tm
    ≈⟨ assoc-tm (connect-susp-inc-right _ _) (label-to-sub L) (Coh (tree-to-ctx S) (sty-to-type A) idSub) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm [ connect-susp-inc-right _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

SCoh-ext : (S : Tree n) → (A : STy (someTree S)) → (L : Label-WT (someTree T) S) → SCoh S A (map-pext {T = U} L) ≃stm SExt {T = U} (SCoh S A L)
SCoh-ext {U = U} S A L .get = begin
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub (map-pext {T = U} L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type A) idSub}) (label-to-sub-map-pext {U = U} L) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ connect-susp-inc-left _ (tree-size U)
                                ● suspSubRes (label-to-sub L) ]tm >tm
    ≈⟨ assoc-tm (connect-susp-inc-left _ (tree-size U)) (suspSubRes (label-to-sub L)) (Coh (tree-to-ctx S) (sty-to-type A) idSub) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ suspSubRes (label-to-sub L) ]tm
                                [ connect-susp-inc-left _ (tree-size U) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (susp-res-comp-tm (Coh (tree-to-ctx S) (sty-to-type A) idSub) (label-to-sub L)) refl≃s ⟩
  < suspTm (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) [ connect-susp-inc-left _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

susp-label-full-to-sub : (L : Label X S) → label-to-sub (susp-label-full L ,, S⋆) ≃s suspSub (label-to-sub (L ,, S⋆))
susp-label-full-to-sub L = unrestrict-≃ (susp-label-to-sub (L ,, S⋆))

SCoh-unrestrict : (S : Tree n) → (A : STy (someTree S)) → (L : Label (someTree T) S) → SCoh S A (map-pext {T = Sing} (L ,, S⋆)) ≃stm SCoh (suspTree S) (susp-sty A) (susp-label-full L ,, S⋆)
SCoh-unrestrict S A L = [ sym≃tm (Coh≃ refl≃c (susp-sty-to-type A) (sub-action-≃-sub (sym≃s susp-functorial-id) (trans≃s (susp-label-full-to-sub L) (unrestrict-≃ (sym≃s (susp-label-to-sub (L ,, S⋆))))))) ]

id-label-susp-full : (T : Tree n) → susp-label-full (id-label T) ≃l id-label (suspTree T)
id-label-susp-full T .get PHere = refl≃stm
id-label-susp-full T .get (PExt Z) = compute-≃ refl≃stm
id-label-susp-full T .get (PShift PHere) = compute-≃ refl≃stm

extend-map-pshift : (a : STm (someTree S)) → (L : Label-WT (someTree T) S) → (a >>= map-pshift {S = U} L) ≃stm SShift {S = U} (a >>= L)
label-on-sty-pshift : (A : STy (someTree S)) → (L : Label-WT (someTree T) S) → (label-on-sty A (map-pshift {S = U} L)) ≃sty map-sty-pshift {S = U} (label-on-sty A L)
map-pshift-comp : (L : Label (someTree T) S) → (M : Label-WT (someTree U) T)
                → label-comp L (map-pshift {S = U′} M) ≃l (SShift {S = U′} ∘ label-comp L M)
map-pshift-comp L M .get Z = extend-map-pshift (L Z) M

extend-map-pshift (SExt a) L = extend-map-pshift a (label₁ L)
extend-map-pshift (SShift a) L = extend-map-pshift a (label₂ L)
extend-map-pshift (SPath P) l = refl≃stm
extend-map-pshift {U = U} (SCoh S A M) L = begin
  < SCoh S A (label-wt-comp M (map-pshift L)) >stm
    ≈⟨ ≃SCoh S refl≃sty (map-pshift-comp (ap M) L) (label-on-sty-pshift (lty M) L) ⟩
  < SCoh S A (map-pshift (label-wt-comp M L)) >stm
    ≈⟨ SCoh-shift S A (label-wt-comp M L) ⟩
  < SShift (SCoh S A (label-wt-comp M L)) >stm ∎
  where
    open Reasoning stm-setoid

label-on-sty-pshift S⋆ L = refl≃sty
label-on-sty-pshift (SArr s A t) L = ≃SArr (extend-map-pshift s L) (label-on-sty-pshift A L) (extend-map-pshift t L)

extend-map-pext : (a : STm (someTree S)) → (L : Label-WT (someTree T) S) → (a >>= map-pext {T = U} L) ≃stm SExt {T = U} (a >>= L)
label-on-sty-pext : (A : STy (someTree S)) → (L : Label-WT (someTree T) S) → (label-on-sty A (map-pext {T = U} L)) ≃sty map-sty-pext {T = U} (label-on-sty A L)
map-pext-comp : (L : Label (someTree T) S) → (M : Label-WT (someTree U) T)
                → label-comp L (map-pext {T = U′} M) ≃l (SExt {T = U′} ∘ label-comp L M)
map-pext-comp L M .get Z = extend-map-pext (L Z) M

extend-map-pext (SExt a) L = extend-map-pext a (label₁ L)
extend-map-pext (SShift a) L = extend-map-pext a (label₂ L)
extend-map-pext (SPath a) L = refl≃stm
extend-map-pext {U = U} (SCoh S A M) L = begin
  < SCoh S A (label-wt-comp M (map-pext L)) >stm
    ≈⟨ ≃SCoh S refl≃sty (map-pext-comp (ap M) L) (label-on-sty-pext (lty M) L) ⟩
  < SCoh S A (map-pext (label-wt-comp M L)) >stm
    ≈⟨ SCoh-ext S A (label-wt-comp M L) ⟩
  < SExt (SCoh S A (label-wt-comp M L)) >stm ∎
  where
    open Reasoning stm-setoid

label-on-sty-pext S⋆ L = refl≃sty
label-on-sty-pext (SArr s A t) L = ≃SArr (extend-map-pext s L) (label-on-sty-pext A L) (extend-map-pext t L)

connect-tree-inc-left-unit : (T : Tree n)
                           → connect-tree-inc-left′ T Sing ≃lp (λ Z → Z)
connect-tree-inc-left-unit Sing .get PHere = refl≃p
connect-tree-inc-left-unit (Join S T) .get PHere = ≃Here (≃′-to-≃ (Join≃′ Refl≃′ (connect-tree-right-unit T)))
connect-tree-inc-left-unit (Join S T) .get (PExt Z) = ≃Ext refl≃p (≃′-to-≃ (connect-tree-right-unit T))
connect-tree-inc-left-unit (Join S T) .get (PShift Z) = ≃Shift refl≃ (connect-tree-inc-left-unit T .get Z)

connect-label-right-unit : (L : Label X S)
                         → (M : Label X Sing)
                         → connect-label L M ≃l label-≃ (connect-tree-right-unit S) L
connect-label-right-unit {S = Sing} L M .get PHere = refl≃stm
connect-label-right-unit {S = Join S T} L M .get PHere = refl≃stm
connect-label-right-unit {S = Join S T} L M .get (PExt Z) = refl≃stm
connect-label-right-unit {S = Join S T} L M .get (PShift Z) = connect-label-right-unit (L ∘ PShift) M .get Z

stm-≃-spath : (p : S ≃′ T)
            → (P : Path S)
            → stm-≃ p (SPath P) ≃stm SPath (ppath-≃ p P)
stm-≃-spath Refl≃′ P = refl≃stm
stm-≃-spath (Join≃′ p q) P = refl≃stm
