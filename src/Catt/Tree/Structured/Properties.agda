module Catt.Tree.Structured.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured

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

≃S⋆ : S ≃ T → S⋆ {X = someTree S} ≃sty S⋆ {X = someTree T}
≃S⋆ p = [ (Star≃ (cong suc (≃-to-same-n p))) ]

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

compute-to-term : (a : STm X) → compute-stm a ≃stm a
compute-to-term (SExt a) = refl≃stm
compute-to-term (SShift a) = refl≃stm
compute-to-term (SPath PHere) = refl≃stm
compute-to-term (SPath (PExt x)) = [ refl≃tm ]
compute-to-term (SPath (PShift x)) = [ refl≃tm ]
compute-to-term (SCoh S A L) = refl≃stm
compute-to-term (SOther t) = refl≃stm

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

≃SCoh : (S : Tree n) → {A A′ : STy (someTree S)} → A ≃sty A′ → ∀ {L : Label-WT X S} {M : Label-WT Y S} → ap L ≃l ap M → lty L ≃sty lty M → SCoh S A L ≃stm SCoh S A′ M
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
label-to-sub-lem : (L : Label-WT X (Join S T)) → get-snd [ unrestrict (label-to-sub (label₁ L)) ]tm ≃tm Var (fromℕ m) [ label-to-sub (label₂ L) ]tm

label-to-sub-phere : (L : Label-WT X S) → Var (fromℕ (tree-size S)) [ label-to-sub L ]tm ≃tm apt L PHere
label-to-sub-phere {S = Sing} L = refl≃tm
label-to-sub-phere {S = Join S₁ S₂} L = begin
  < Var (fromℕ _) [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]tm >tm
    ≈⟨ sub-from-connect-fst-var (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < get-fst [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
    ≈⟨ unrestrict-fst (label-to-sub (label₁ L)) ⟩
  < apt L PHere >tm ∎
  where
    open Reasoning tm-setoid

label-to-sub-path : (L : Label-WT X S) → (P : Path S) → path-to-term P [ label-to-sub L ]tm ≃tm apt L P
label-to-sub-path L PHere = label-to-sub-phere L
label-to-sub-path L (PExt P) = begin
  < susp-tm (path-to-term P) [ connect-susp-inc-left _ _ ]tm
                            [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (susp-tm (path-to-term P)) ⟩
  < susp-tm (path-to-term P) [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L))
                            ● connect-susp-inc-left _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = susp-tm (path-to-term P)}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) get-snd (label-to-sub (label₂ L))) ⟩
  < susp-tm (path-to-term P) [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
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
    ≈⟨ sub-action-≃-tm (refl≃tm {s = path-to-term P}) (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) get-snd (label-to-sub (label₂ L)) (label-to-sub-lem L)) ⟩
  < path-to-term P [ label-to-sub (label₂ L) ]tm >tm
    ≈⟨ label-to-sub-path (label₂ L) P ⟩
  < apt L (PShift P) >tm ∎
  where
    open Reasoning tm-setoid

label-to-sub-stm L (SExt a) = begin
  < susp-tm (stm-to-term a) [ connect-susp-inc-left _ _ ]tm
                            [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L)) ]tm >tm
    ≈˘⟨ assoc-tm _ _ (susp-tm (stm-to-term a)) ⟩
  < susp-tm (stm-to-term a) [ sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                               (label-to-sub (label₂ L))
                            ● connect-susp-inc-left _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = susp-tm (stm-to-term a)}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) get-snd (label-to-sub (label₂ L))) ⟩
  < susp-tm (stm-to-term a) [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
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
    ≈⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) get-snd (label-to-sub (label₂ L)) (label-to-sub-lem L)) ⟩
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
  < get-snd [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
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

label-on-sty-≃ : As ≃sty Bs → L ≃l M → As′ ≃sty Bs′ → label-on-sty As (L ,, As′) ≃sty label-on-sty Bs (M ,, Bs′)
label-on-sty-≃ {As = S⋆} {S⋆} {L = L} {M} {As′ = As′} {Bs′} p q r = r
label-on-sty-≃ {As = SArr s As t} {SArr s′ Bs t′} {L = L} {M} {As′ = As′} {Bs′} [ Arr≃ x y z ] q r
  = ≃SArr (extend-≃ {a = s} {b = s′} [ x ] q r)
          (label-on-sty-≃ [ y ] q r)
          (extend-≃ {a = t} {b = t′} [ z ] q r)

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

susp-stm-to-term : (a : STm X) → stm-to-term (susp-stm a) ≃tm susp-tm (stm-to-term a)
susp-sty-to-type : (A : STy X) → sty-to-type (susp-sty A) ≃ty susp-ty (sty-to-type A)
susp-label-to-sub′ : (L : Label-WT X S) → ((P : Path S) → apt (susp-label L) P ≃tm susp-tm (apt L P)) → sty-to-type (susp-sty (lty L)) ≃ty susp-ty (sty-to-type (lty L)) → label-to-sub (susp-label L) ≃s susp-sub-res (label-to-sub L)
susp-label-to-sub : (L : Label-WT X S) → label-to-sub (susp-label L) ≃s susp-sub-res (label-to-sub L)

susp-stm-to-term {X = someTree x} a = id-on-tm (susp-tm (stm-to-term a))
susp-stm-to-term {X = Other _} (SCoh S A L) = begin
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub (susp-label L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type A) idSub}) (susp-label-to-sub L) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ susp-sub-res (label-to-sub L) ]tm >tm
    ≈˘⟨ susp-res-comp-tm (Coh (tree-to-ctx S) (sty-to-type A) idSub) (label-to-sub L) ⟩
  < susp-tm (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) >tm ∎
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
  < sub-from-connect (unrestrict (susp-sub-res (label-to-sub (label₁ L)))) (susp-sub-res (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-≃ (sub-res-unrestrict-comm (label-to-sub (label₁ L))) refl≃s ⟩
  < sub-from-connect (susp-sub-res (unrestrict (label-to-sub (label₁ L)))) (susp-sub-res (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-susp-res (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < susp-sub-res (sub-from-connect (unrestrict (label-to-sub (label₁ L)))
                                             (label-to-sub (label₂ L))) >s ∎
  where
    open Reasoning sub-setoid

susp-label-to-sub L = susp-label-to-sub′ L (λ P → susp-stm-to-term (ap L P)) (susp-sty-to-type (lty L))

susp-stm-≃ : a ≃stm b → susp-stm a ≃stm susp-stm b
susp-stm-≃ {a = a} {b = b} [ p ] .get = begin
  < stm-to-term (susp-stm a) >tm
    ≈⟨ susp-stm-to-term a ⟩
  < susp-tm (stm-to-term a) >tm
    ≈⟨ susp-tm-≃ p ⟩
  < susp-tm (stm-to-term b) >tm
    ≈˘⟨ susp-stm-to-term b ⟩
  < stm-to-term (susp-stm b) >tm ∎
  where
    open Reasoning tm-setoid

susp-sty-≃ : As ≃sty Bs → susp-sty As ≃sty susp-sty Bs
susp-sty-≃ {As = As} {Bs = Bs} [ p ] .get = begin
  < sty-to-type (susp-sty As) >ty
    ≈⟨ susp-sty-to-type As ⟩
  < susp-ty (sty-to-type As) >ty
    ≈⟨ susp-ty-≃ p ⟩
  < susp-ty (sty-to-type Bs) >ty
    ≈˘⟨ susp-sty-to-type Bs ⟩
  < sty-to-type (susp-sty Bs) >ty ∎
  where
    open Reasoning ty-setoid

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
map-sty-pext-prop S⋆ = ≃SArr [ (connect-inc-left-fst-var get-snd _) ] [ refl≃ty ] [ connect-inc-fst-var get-snd _ ]
map-sty-pext-prop (SArr s A t) = ≃SArr [ sub-action-≃-tm (id-on-tm (susp-tm (stm-to-term s))) refl≃s ] (map-sty-pext-prop A) [ sub-action-≃-tm (id-on-tm (susp-tm (stm-to-term t))) refl≃s ]

label-to-sub-map-pext : (L : Label-WT (someTree T) S) → label-to-sub (map-pext {T = U} L) ≃s connect-susp-inc-left (tree-size T) (tree-size U) ● susp-sub-res (label-to-sub L)
label-to-sub-map-pext {U = U} L = begin
  < label-to-sub (map-pext {T = U} L) >s
    ≈˘⟨ label-to-sub-≃ (label-sub (susp-label L) (connect-susp-inc-left _ (tree-size U)))
                       (map-pext {T = U} L)
                       [ (λ P → [ sub-action-≃-tm (id-on-tm (susp-tm (stm-to-term (ap L P)))) refl≃s ]) ]
                       (map-sty-pext-prop (lty L)) ⟩
  < label-to-sub (label-sub (susp-label L) (connect-susp-inc-left _ (tree-size U))) >s
    ≈⟨ label-sub-to-sub (susp-label L) (connect-susp-inc-left _ (tree-size U)) ⟩
  < connect-susp-inc-left _ (tree-size U) ● label-to-sub (susp-label L) >s
    ≈⟨ sub-action-≃-sub (susp-label-to-sub L) refl≃s ⟩
  < connect-susp-inc-left _ (tree-size U) ● susp-sub-res (label-to-sub L) >s ∎
  where
    open Reasoning sub-setoid

map-sty-pext-≃ : {As Bs : STy (someTree S)} → As ≃sty Bs → map-sty-pext {T = T} As ≃sty map-sty-pext {T = T} Bs
map-sty-pext-≃ {As = S⋆} {Bs = S⋆} [ p ] = refl≃sty
map-sty-pext-≃ {As = SArr s As t} {Bs = SArr s₁ Bs t₁} [ Arr≃ p q r ] = ≃SArr (≃SExt [ p ] refl≃) (map-sty-pext-≃ [ q ]) (≃SExt [ r ] refl≃)

map-sty-pshift-≃ : {As Bs : STy (someTree T)} → As ≃sty Bs → map-sty-pshift {S = S} As ≃sty map-sty-pshift {S = S} Bs
map-sty-pshift-≃ {As = S⋆} {Bs = S⋆} [ p ] = refl≃sty
map-sty-pshift-≃ {As = SArr s As t} {Bs = SArr s₁ Bs t₁} [ Arr≃ p q r ] = ≃SArr (≃SShift refl≃ [ p ]) (map-sty-pshift-≃ [ q ]) (≃SShift refl≃ [ r ])

lift-stm-to-term : (a : STm (Other n)) → stm-to-term (lift-stm a) ≃tm lift-tm (stm-to-term a)
lift-sty-to-type : (A : STy (Other n)) → sty-to-type (lift-sty A) ≃ty lift-ty (sty-to-type A)
lift-label-to-sub′ : (L : Label-WT (Other n) S) → ((P : Path S) → apt (lift-label L) P ≃tm lift-tm (apt L P)) → sty-to-type (lift-sty (lty L)) ≃ty lift-ty (sty-to-type (lty L)) → label-to-sub (lift-label L) ≃s lift-sub (label-to-sub L)
lift-label-to-sub : (L : Label-WT (Other n) S) → label-to-sub (lift-label L) ≃s lift-sub (label-to-sub L)

lift-stm-to-term (SCoh S A L) = begin
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub (lift-label L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type A) idSub}) (lift-label-to-sub L) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ lift-sub (label-to-sub L) ]tm >tm
    ≈⟨ apply-lifted-sub-tm-≃ (Coh (tree-to-ctx S ) (sty-to-type A) idSub) (label-to-sub L) ⟩
  < lift-tm (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) >tm ∎
  where
    open Reasoning tm-setoid
lift-stm-to-term (SOther t) = refl≃tm

lift-sty-to-type S⋆ = refl≃ty
lift-sty-to-type (SArr s A t) = Arr≃ (lift-stm-to-term s) (lift-sty-to-type A) (lift-stm-to-term t)

lift-label-to-sub′ {S = Sing} L f p = Ext≃ (Null≃ p) (f PHere)
lift-label-to-sub′ {S = Join S T} L f p = begin
  < sub-from-connect (unrestrict (label-to-sub (lift-label (label₁ L)))) (label-to-sub (lift-label (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-≃ (lift-label-to-sub′ (label₁ L) (λ P → f (PExt P)) (Arr≃ (f PHere) p (f (PShift PHere))))) (lift-label-to-sub′ (label₂ L) (λ P → f (PShift P)) p) ⟩
  < sub-from-connect (unrestrict (lift-sub (label-to-sub (label₁ L)))) (lift-sub (label-to-sub (label₂ L))) >s
    ≈⟨ sub-from-connect-≃ (unrestrict-lift (label-to-sub (label₁ L))) (refl≃s {σ = lift-sub (label-to-sub (label₂ L))}) ⟩
  < sub-from-connect (lift-sub (unrestrict (label-to-sub (label₁ L)))) (lift-sub (label-to-sub (label₂ L))) >s
    ≈˘⟨ sub-from-connect-lift (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ⟩
  < lift-sub (sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))) >s ∎
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
    ≈⟨ sub-from-connect-prop get-snd ⟩
  < idSub >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (label₁ (id-label-wt (Join S T)))) ≃s connect-susp-inc-left (tree-size S) (tree-size T)
    l1 = begin
      < unrestrict (label-to-sub (map-pext {T = T} (id-label-wt S))) >s
        ≈⟨ unrestrict-≃ (label-to-sub-map-pext {U = T} (id-label-wt S)) ⟩
      < unrestrict (connect-susp-inc-left (tree-size S) (tree-size T)
                   ● susp-sub-res (label-to-sub (id-label-wt S))) >s
        ≈⟨ unrestrict-comp-higher (connect-susp-inc-left (tree-size S) (tree-size T)) (susp-sub-res (label-to-sub (id-label-wt S))) ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● susp-sub (label-to-sub (id-label-wt S)) >s
        ≈⟨ sub-action-≃-sub (susp-sub-≃ (id-label-to-sub S)) refl≃s ⟩
      < connect-susp-inc-left (tree-size S) (tree-size T) ● susp-sub idSub >s
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

sub-to-label-to-sub : (S : Tree n) → (σ : Sub (suc n) m A) → label-to-sub (to-label-wt S σ) ≃s σ
sub-to-label-to-sub {A = A} S σ = begin
  < label-to-sub (to-label-wt S σ) >s
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

label-to-sub-to-label : (L : Label-WT X S) → ap (to-label-wt S (label-to-sub L)) ≃l ap L
label-to-sub-to-label L .get Z .get = label-to-sub-stm L (SPath Z)

sty-to-type-to-sty : (As : STy X) → to-sty (sty-to-type As) ≃sty As
sty-to-type-to-sty As .get = to-sty-to-type (sty-to-type As)

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

id-label-on-sty : (As : STy (someTree T)) → label-on-sty As (id-label-wt T) ≃sty As
id-label-on-sty {T = T} As = [ begin
  < sty-to-type (label-on-sty As (id-label-wt T)) >ty
    ≈˘⟨ label-to-sub-sty (id-label-wt T) As ⟩
  < sty-to-type As [ label-to-sub (id-label-wt T) ]ty >ty
    ≈⟨ sub-action-≃-ty (refl≃ty {A = sty-to-type As}) (id-label-to-sub T) ⟩
  < sty-to-type As [ idSub ]ty >ty
    ≈⟨ id-on-ty (sty-to-type As) ⟩
  < sty-to-type As >ty ∎ ]
  where
    open Reasoning ty-setoid

comp-right-unit : (L : Label (someTree T) S) → label-comp L (id-label-wt T) ≃l L
comp-right-unit L .get Z = extend-id (L Z)

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
connect-label-≃m {S = Join S₁ Sing} {L = L} {M} {L′} {M′} p q .get (PShift Z) = begin
  < replace-label M (L (PShift PHere)) Z >stm
    ≈⟨ replace-not-here M (L (PShift PHere)) Z ⟩
  < M Z >stm
    ≈⟨ q .get Z ⟩
  < M′ Z >stm
    ≈˘⟨ replace-not-here M′ (L′ (PShift PHere)) Z ⟩
  < replace-label M′ (L′ (PShift PHere)) Z >stm ∎
  where
    open Reasoning stm-setoid
connect-label-≃m {S = Join S₁ (Join S₂ S₃)} {L = L} {M} {L′} p q .get (PShift Z) = connect-label-≃m {L = L ∘ PShift} {L′ = L′ ∘ PShift} [ (λ Q → p .get (PShift Q) ⦃ build ⦃ maximal-join-not-here Q ⦄ ⦄) ] q .get Z

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

label-≃-sym-max : (p : S ≃′ T) → L ≃lm label-≃ p M → label-≃ (sym≃′ p) L ≃lm M
label-≃-sym-max {L = L} {M = M} p q .get Z = begin
  < L (ppath-≃ (sym≃′ p) Z) >stm
    ≈⟨ q .get (ppath-≃ (sym≃′ p) Z) ⦃ maximal-≃ (ppath-≃-≃p (sym≃′ p) Z) ⦄ ⟩
  < M (ppath-≃ p (ppath-≃ (sym≃′ p) Z)) >stm
    ≈˘⟨ ap-≃ (refl≃l {L = M}) (trans≃p (ppath-≃-≃p (sym≃′ p) Z) (ppath-≃-≃p p (ppath-≃ (sym≃′ p) Z))) ⟩
  < M Z >stm ∎
  where
    open Reasoning stm-setoid

ppath-≃l : (p : S ≃′ T) → (SPath ∘ ppath-≃ p) ≃l id-label S
ppath-≃l p .get P = ≃SPath (sym≃p (ppath-≃-≃p p P))

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
  < susp-tm (stm-to-term (a >>= L)) >tm
    ≈˘⟨ susp-tm-≃ (label-to-sub-stm L a) ⟩
  < susp-tm (stm-to-term a [ label-to-sub L ]tm) >tm
    ≈⟨ susp-res-comp-tm (stm-to-term a) (label-to-sub L) ⟩
  < stm-to-term a [ susp-sub-res (label-to-sub L) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (susp-label-to-sub L) ⟩
  < stm-to-term a [ label-to-sub (susp-label L) ]tm >tm
    ≈⟨ label-to-sub-stm (susp-label L) a ⟩
  < stm-to-term (a >>= susp-label L) >tm ∎ ]
  where
    open Reasoning tm-setoid

susp-label-on-sty : (As : STy (someTree S)) → (L : Label-WT X S) → susp-sty (label-on-sty As L) ≃sty label-on-sty As (susp-label L)
susp-label-on-sty S⋆ L = refl≃sty
susp-label-on-sty (SArr s As t) L = ≃SArr (extend-susp-label s L) (susp-label-on-sty As L) (extend-susp-label t L)

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
                                ● susp-sub-res (label-to-sub L) ]tm >tm
    ≈⟨ assoc-tm (connect-susp-inc-left _ (tree-size U)) (susp-sub-res (label-to-sub L)) (Coh (tree-to-ctx S) (sty-to-type A) idSub) ⟩
  < Coh (tree-to-ctx S) (sty-to-type A) idSub [ susp-sub-res (label-to-sub L) ]tm
                                [ connect-susp-inc-left _ (tree-size U) ]tm >tm
    ≈˘⟨ sub-action-≃-tm (susp-res-comp-tm (Coh (tree-to-ctx S) (sty-to-type A) idSub) (label-to-sub L)) refl≃s ⟩
  < susp-tm (Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm) [ connect-susp-inc-left _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

susp-label-full-to-sub : (L : Label X S) → label-to-sub (susp-label-full L ,, S⋆) ≃s susp-sub (label-to-sub (L ,, S⋆))
susp-label-full-to-sub L = unrestrict-≃ (susp-label-to-sub (L ,, S⋆))

SCoh-unrestrict : (S : Tree n) → (As : STy (someTree S)) → (L : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → SCoh S As L ≃stm SCoh (susp-tree S) (susp-sty As) (unrestrict-label L ,, sty-base (lty L))
SCoh-unrestrict S As (L ,, SArr s Bs t) .get
  = sub-action-≃-tm (Coh≃ refl≃c (sym≃ty (susp-sty-to-type As)) susp-functorial-id)
                    (refl≃s {σ = unrestrict (label-to-sub′ (λ P → stm-to-term (L P))
                                                           (stm-to-term s ─⟨ sty-to-type Bs ⟩⟶ stm-to-term t))})

extend-unrestrict : (a : STm (someTree S)) → (L : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → (susp-stm a >>= unrestrict-label L ,, sty-base (lty L)) ≃stm (a >>= L)
extend-unrestrict a (L ,, SArr s As t) = refl≃stm

label-on-sty-unrestrict : (As : STy (someTree S)) → (L : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → label-on-sty (susp-sty As) (unrestrict-label L ,, sty-base (lty L)) ≃sty label-on-sty As L
label-on-sty-unrestrict S⋆ (L ,, SArr s Bs t) = refl≃sty
label-on-sty-unrestrict (SArr s As t) L = ≃SArr (extend-unrestrict s L) (label-on-sty-unrestrict As L) (extend-unrestrict t L)

extend-susp-label-full : (a : STm (someTree S)) → (L : Label X S) → susp-stm (a >>= L ,, S⋆) ≃stm (susp-stm a >>= susp-label-full L ,, S⋆)
extend-susp-label-full a L = begin
  < susp-stm (a >>= L ,, S⋆) >stm
    ≈⟨ extend-susp-label a (L ,, S⋆) ⟩
  < a >>= susp-label (L ,, S⋆) >stm
    ≈˘⟨ extend-unrestrict a (susp-label (L ,, S⋆)) ⟩
  < susp-stm a >>= susp-label-full L ,, S⋆ >stm ∎
  where
    open Reasoning stm-setoid

susp-label-full-on-sty : (As : STy (someTree S)) → (L : Label X S) → susp-sty (label-on-sty As (L ,, S⋆)) ≃sty label-on-sty (susp-sty As) (susp-label-full L ,, S⋆)
susp-label-full-on-sty As L = begin
  < susp-sty (label-on-sty As (L ,, S⋆)) >sty
    ≈⟨ susp-label-on-sty As (L ,, S⋆) ⟩
  < label-on-sty As (susp-label (L ,, S⋆)) >sty
    ≈˘⟨ label-on-sty-unrestrict As (susp-label (L ,, S⋆)) ⟩
  < label-on-sty (susp-sty As) (susp-label-full L ,, S⋆) >sty ∎
  where
    open Reasoning sty-setoid

id-label-susp-full : (T : Tree n) → susp-label-full (id-label T) ≃l id-label (susp-tree T)
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

extend-lift : (a : STm (someTree S)) → (L : Label-WT (Other n) S) → (a >>= lift-label L) ≃stm lift-stm (a >>= L)
label-on-sty-lift : (As : STy (someTree S)) → (L : Label-WT (Other n) S) → label-on-sty As (lift-label L) ≃sty lift-sty (label-on-sty As L)
label-comp-lift : (L : Label (someTree S) U) → (M : Label-WT (Other n) S) → label-comp L (lift-label M) ≃l (lift-stm ∘ (label-comp L M))

extend-lift (SExt a) L = extend-lift a (label₁ L)
extend-lift (SShift a) L = extend-lift a (label₂ L)
extend-lift (SPath x) L = refl≃stm
extend-lift (SCoh S A M) L = ≃SCoh S refl≃sty (label-comp-lift (ap M) L) (label-on-sty-lift (lty M) L)

label-on-sty-lift S⋆ L = refl≃sty
label-on-sty-lift (SArr s As t) L = ≃SArr (extend-lift s L) (label-on-sty-lift As L) (extend-lift t L)

label-comp-lift L M .get Z = extend-lift (L Z) M

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

connect-tree-inc-left-assoc : (S : Tree n)
                            → (T : Tree m)
                            → (U : Tree l)
                            → (connect-tree-inc-left′ (connect-tree S T) U ∘ connect-tree-inc-left′ S T)
                            ≃lp connect-tree-inc-left′ S (connect-tree T U)
connect-tree-inc-left-assoc Sing T U .get Z = connect-tree-inc-left-phere T U
connect-tree-inc-left-assoc (Join S₁ S₂) T U .get PHere = ≃Here (≃′-to-≃ (sym≃′ (connect-tree-assoc (Join S₁ S₂) T U)))
connect-tree-inc-left-assoc (Join S₁ S₂) T U .get (PExt Z) = ≃Ext refl≃p (sym≃ (≃′-to-≃ (connect-tree-assoc S₂ T U)))
connect-tree-inc-left-assoc (Join S₁ S₂) T U .get (PShift Z) = ≃Shift refl≃ (connect-tree-inc-left-assoc S₂ T U .get Z)

connect-tree-inc-right-assoc : (S : Tree n)
                             → (T : Tree m)
                             → (U : Tree l)
                             → (connect-tree-inc-right′ S (connect-tree T U) ∘ connect-tree-inc-right′ T U)
                             ≃lp connect-tree-inc-right′ (connect-tree S T) U
connect-tree-inc-right-assoc Sing T U .get Z = refl≃p
connect-tree-inc-right-assoc (Join S₁ S₂) T U .get Z = ≃Shift refl≃ (connect-tree-inc-right-assoc S₂ T U .get Z)

connect-tree-inc-assoc : (S : Tree n)
                       → (T : Tree m)
                       → (U : Tree l)
                       → (connect-tree-inc-right′ S (connect-tree T U) ∘ connect-tree-inc-left′ T U)
                       ≃lp (connect-tree-inc-left′ (connect-tree S T) U ∘ connect-tree-inc-right′ S T)
connect-tree-inc-assoc Sing T U .get Z = refl≃p
connect-tree-inc-assoc (Join S₁ S₂) T U .get Z = ≃Shift refl≃ (connect-tree-inc-assoc S₂ T U .get Z)

replace-connect-label : (L : Label X S)
                      → (M : Label X T)
                      → (a : STm X)
                      → replace-label (connect-label L M) a ≃l connect-label (replace-label L a) M
replace-connect-label {S = Sing} L M a .get PHere = refl≃stm
replace-connect-label {S = Sing} L M a .get (PExt Z) = refl≃stm
replace-connect-label {S = Sing} L M a .get (PShift Z) = refl≃stm
replace-connect-label {S = Join S₁ S₂} L M a .get PHere = refl≃stm
replace-connect-label {S = Join S₁ S₂} L M a .get (PExt Z) = refl≃stm
replace-connect-label {S = Join S₁ S₂} L M a .get (PShift Z) = refl≃stm

connect-label-assoc : (L : Label X S)
                    → (M : Label X T)
                    → (N : Label X U)
                    → connect-label L (connect-label M N)
                    ≃l label-≃ (connect-tree-assoc S T U) (connect-label (connect-label L M) N)
connect-label-assoc {S = Sing} L M N = replace-connect-label M N (L PHere)
connect-label-assoc {S = Join S₁ S₂} L M N .get PHere = refl≃stm
connect-label-assoc {S = Join S₁ S₂} L M N .get (PExt Z) = refl≃stm
connect-label-assoc {S = Join S₁ S₂} L M N .get (PShift Z) = connect-label-assoc (L ∘ PShift) M N .get Z

stm-≃-≃stm : (p : S ≃′ T) → (a : STm (someTree S)) → a ≃stm stm-≃ p a
sty-≃-≃sty : (p : S ≃′ T) → (A : STy (someTree S)) → A ≃sty sty-≃ p A
≃-label-≃l : (p : S ≃′ T) → (L : Label (someTree S) U) → L ≃l ≃-label p L

stm-≃-≃stm Refl≃′ a = refl≃stm
stm-≃-≃stm (Join≃′ p q) (SExt a) = ≃SExt (stm-≃-≃stm p a) (≃′-to-≃ q)
stm-≃-≃stm (Join≃′ p q) (SShift a) = ≃SShift (≃′-to-≃ p) (stm-≃-≃stm q a)
stm-≃-≃stm (Join≃′ p q) (SPath P) = ≃SPath (ppath-≃-≃p (Join≃′ p q) P)
stm-≃-≃stm (Join≃′ p q) (SCoh S A L) = ≃SCoh S refl≃sty (≃-label-≃l (Join≃′ p q) (ap L)) (sty-≃-≃sty (Join≃′ p q) (lty L))

sty-≃-≃sty p S⋆ = ≃S⋆ (≃′-to-≃ p)
sty-≃-≃sty p (SArr s A t) = ≃SArr (stm-≃-≃stm p s) (sty-≃-≃sty p A) (stm-≃-≃stm p t)

≃-label-≃l p L .get Z = stm-≃-≃stm p (L Z)

stm-≃-≃ : (p : S ≃′ T) → a ≃stm b → stm-≃ p a ≃stm stm-≃ p b
stm-≃-≃ {a = a} {b = b} p q = begin
  < stm-≃ p a >stm
    ≈˘⟨ stm-≃-≃stm p a ⟩
  < a >stm
    ≈⟨ q ⟩
  < b >stm
    ≈⟨ stm-≃-≃stm p b ⟩
  < stm-≃ p b >stm ∎
  where
    open Reasoning stm-setoid

map-sty-pext-susp-compat : (As : STy (someTree S)) → map-sty-pext {T = Sing} As ≃sty susp-sty As
map-sty-pext-susp-compat S⋆ = ≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm)
map-sty-pext-susp-compat (SArr s As t) = ≃SArr refl≃stm (map-sty-pext-susp-compat As) refl≃stm

sty-dim-≃ : As ≃sty Bs → sty-dim As ≡ sty-dim Bs
sty-dim-≃ {As = S⋆} {Bs = S⋆} p = refl
sty-dim-≃ {As = SArr _ As _} {Bs = SArr _ Bs _} [ Arr≃ _ p _ ] = cong suc (sty-dim-≃ [ p ])

sty-src-≃ : (p : As ≃sty Bs) → .⦃ _ : NonZero (sty-dim As) ⦄ → sty-src As ≃stm sty-src Bs ⦃ NonZero-subst (sty-dim-≃ p) it ⦄
sty-src-≃ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≃ p _ _ ] = [ p ]

sty-tgt-≃ : (p : As ≃sty Bs) → .⦃ _ : NonZero (sty-dim As) ⦄ → sty-tgt As ≃stm sty-tgt Bs ⦃ NonZero-subst (sty-dim-≃ p) it ⦄
sty-tgt-≃ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≃ _ _ p ] = [ p ]

sty-base-≃ : (p : As ≃sty Bs) → sty-base As ≃sty sty-base Bs
sty-base-≃ {As = S⋆} {Bs = S⋆} [ Star≃ x ] = [ Star≃ x ]
sty-base-≃ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≃ _ p _ ] = [ p ]

sty-prop : (As : STy X) → .⦃ _ : NonZero (sty-dim As) ⦄ → SArr (sty-src As) (sty-base As) (sty-tgt As) ≃sty As
sty-prop (SArr s As t) = refl≃sty

sty-dim-label : (As : STy (someTree S)) → (L : Label-WT X S) → sty-dim (label-on-sty As L) ≡ sty-dim As + sty-dim (lty L)
sty-dim-label S⋆ L = refl
sty-dim-label (SArr s As t) L = cong suc (sty-dim-label As L)

susp-sty-dim : (As : STy X) → sty-dim (susp-sty As) ≡ suc (sty-dim As)
susp-sty-dim S⋆ = refl
susp-sty-dim (SArr s As t) = cong suc (susp-sty-dim As)

sty-to-type-dim : (As : STy X) → ty-dim (sty-to-type As) ≡ sty-dim As
sty-to-type-dim S⋆ = refl
sty-to-type-dim (SArr s As t) = cong suc (sty-to-type-dim As)

susp-unrestrict-label : (L : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → (susp-stm ∘ unrestrict-label L) ≃l unrestrict-label (susp-label L) ⦃ NonZero-subst (sym (susp-sty-dim (lty L))) it ⦄
susp-unrestrict-label (L ,, SArr s As t) .get PHere = refl≃stm
susp-unrestrict-label (L ,, SArr s As t) .get (PExt Z) = refl≃stm
susp-unrestrict-label (L ,, SArr s As t) .get (PShift Z) = refl≃stm

truncate-sty′-≃ : d ≡ d′ → As ≃sty Bs → truncate-sty′ d As ≃sty truncate-sty′ d′ Bs
truncate-sty′-≃ {d = zero} refl q = q
truncate-sty′-≃ {d = suc d} refl q = truncate-sty′-≃ {d = d} refl (sty-base-≃ q)

truncate-sty-≃ : d ≡ d′ → As ≃sty Bs → truncate-sty d As ≃sty truncate-sty d′ Bs
truncate-sty-≃ {d = d} refl q = truncate-sty′-≃ (cong (_∸ d) (sty-dim-≃ q)) q

truncate-sty-1-map-pext : (As : STy (someTree S)) → truncate-sty 1 (map-sty-pext {T = T} As) ≃sty SArr SHere S⋆ (SPath (PShift {T = T} {S = S} PHere))
truncate-sty-1-map-pext S⋆ = ≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm)
truncate-sty-1-map-pext (SArr s S⋆ t) = ≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm)
truncate-sty-1-map-pext (SArr _ (SArr s As t) _) = truncate-sty-1-map-pext (SArr s As t)

truncate-sty′-label : (d : ℕ) → (As : STy (someTree S)) → (L : Label-WT X S) → d ≤ sty-dim As → truncate-sty′ d (label-on-sty As L) ≃sty label-on-sty (truncate-sty′ d As) L
truncate-sty′-label zero As L p = refl≃sty
truncate-sty′-label (suc d) (SArr s As t) L p = truncate-sty′-label d As L (≤-pred p)

truncate-sty-label : (d : ℕ) → (As : STy (someTree S)) → (L : Label-WT X S) → truncate-sty (d + sty-dim (lty L)) (label-on-sty As L) ≃sty label-on-sty (truncate-sty d As) L
truncate-sty-label d As L = begin
  < truncate-sty (d + sty-dim (lty L)) (label-on-sty As L) >sty
    ≡⟨⟩
  < truncate-sty′ (sty-dim (label-on-sty As L) ∸ (d + sty-dim (lty L))) (label-on-sty As L) >sty
    ≈⟨ truncate-sty′-≃ lem refl≃sty ⟩
  < truncate-sty′ (sty-dim As ∸ d) (label-on-sty As L) >sty
    ≈⟨ truncate-sty′-label (sty-dim As ∸ d) As L (m∸n≤m (sty-dim As) d) ⟩
  < label-on-sty (truncate-sty′ (sty-dim As ∸ d) As) L >sty
    ≡⟨⟩
  < label-on-sty (truncate-sty d As) L >sty ∎
  where
    lem : sty-dim (label-on-sty As L) ∸ (d + sty-dim (lty L)) ≡ sty-dim As ∸ d
    lem = begin
      sty-dim (label-on-sty As L) ∸ (d + sty-dim (lty L))
        ≡⟨ cong (_∸ (d + sty-dim (lty L))) (sty-dim-label As L) ⟩
      (sty-dim As + sty-dim (lty L)) ∸ (d + sty-dim (lty L))
        ≡⟨ cong (sty-dim As + sty-dim (lty L) ∸_) (+-comm d (sty-dim (lty L))) ⟩
      sty-dim As + sty-dim (lty L) ∸ (sty-dim (lty L) + d)
        ≡˘⟨ ∸-+-assoc (sty-dim As + sty-dim (lty L)) (sty-dim (lty L)) d ⟩
      sty-dim As + sty-dim (lty L) ∸ sty-dim (lty L) ∸ d
        ≡⟨ cong (_∸ d) (m+n∸n≡m (sty-dim As) (sty-dim (lty L))) ⟩
      sty-dim As ∸ d ∎
      where
        open ≡-Reasoning
    open Reasoning sty-setoid

truncate-sty-≤ : (d : ℕ) → (As : STy X) → (d < sty-dim As) → truncate-sty d As ≃sty truncate-sty d (sty-base As)
truncate-sty-≤ d (SArr s As t) p
  rewrite +-∸-assoc 1 p = refl≃sty

map-sty-pext-label : (As : STy (someTree S)) → (L : Label-WT X (Join S T)) → label-on-sty (map-sty-pext As) L ≃sty label-on-sty As (label₁ L)
map-sty-pext-label S⋆ L = refl≃sty
map-sty-pext-label (SArr s As t) L = ≃SArr refl≃stm (map-sty-pext-label As L) refl≃stm

map-sty-pshift-label : (As : STy (someTree T)) → (L : Label-WT X (Join S T)) → label-on-sty (map-sty-pshift As) L ≃sty label-on-sty As (label₂ L)
map-sty-pshift-label S⋆ L = refl≃sty
map-sty-pshift-label (SArr s As t) L = ≃SArr refl≃stm (map-sty-pshift-label As L) refl≃stm

susp-stm-SCoh : (S : Tree n) → (As : STy (someTree S)) → (L : Label-WT X S) → susp-stm (SCoh S As L) ≃stm SCoh S As (susp-label L)
susp-stm-SCoh {X = someTree x} S As L = begin
  < susp-stm (SCoh S As L) >stm
    ≈˘⟨ SCoh-ext S As L ⟩
  < SCoh S As (map-pext L) >stm
    ≈⟨ ≃SCoh S refl≃sty refl≃l (map-sty-pext-susp-compat (lty L)) ⟩
  < SCoh S As (susp-label L) >stm ∎
  where open Reasoning stm-setoid
susp-stm-SCoh {X = Other _} S As L = refl≃stm

stm-sub-SCoh : {X : MaybeTree m} → (S : Tree n) → (As : STy (someTree S)) → (L : Label-WT X S) → (σ : Sub m l A) → stm-sub (SCoh S As L) σ ≃stm SCoh S As (label-sub L σ)
stm-sub-SCoh S As L σ .get = begin
  < Coh (tree-to-ctx S) (sty-to-type As) idSub [ label-to-sub L ]tm [ σ ]tm >tm
    ≈˘⟨ assoc-tm σ (label-to-sub L) (Coh (tree-to-ctx S) (sty-to-type As) idSub) ⟩
  < Coh (tree-to-ctx S) (sty-to-type As) idSub [ σ ● label-to-sub L ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type As) idSub}) (label-sub-to-sub L σ) ⟩
  < Coh (tree-to-ctx S) (sty-to-type As) idSub [ label-to-sub (label-sub L σ) ]tm >tm ∎
  where
    open Reasoning tm-setoid

stm-sub-extend : (a : STm (someTree S)) → (L : Label-WT X S) → (σ : Sub m n A) → stm-sub (a >>= L) σ ≃stm (a >>= label-sub L σ)
stm-sub-extend a L σ .get = begin
  < stm-to-term (a >>= L) [ σ ]tm >tm
    ≈˘⟨ sub-action-≃-tm (label-to-sub-stm L a) refl≃s ⟩
  < stm-to-term a [ label-to-sub L ]tm [ σ ]tm >tm
    ≈˘⟨ assoc-tm σ (label-to-sub L) (stm-to-term a) ⟩
  < stm-to-term a [ σ ● label-to-sub L ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (label-sub-to-sub L σ) ⟩
  < stm-to-term a [ label-to-sub (label-sub L σ) ]tm >tm
    ≈⟨ label-to-sub-stm (label-sub L σ) a ⟩
  < stm-to-term (a >>= label-sub L σ) >tm ∎
  where
    open Reasoning tm-setoid

stm-sub-≃ : a ≃stm b → (σ : Sub n m A) → stm-sub a σ ≃stm stm-sub b σ
stm-sub-≃ {a = a} {b = b} [ p ] σ .get = sub-action-≃-tm p refl≃s

label-sub-comp : (M : Label (someTree S) T) → (L : Label-WT (Other m) S) → (σ : Sub m n A) → ((λ a → stm-sub a σ) ∘ label-comp M L) ≃l label-comp M (label-sub L σ)
label-sub-comp M L σ .get Z = stm-sub-extend (M Z) L σ

unrestrict-label-≃ : (L M : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → ap L ≃l ap M → (q : lty L ≃sty lty M) → unrestrict-label L ≃l unrestrict-label M ⦃ NonZero-subst (sty-dim-≃ q) it ⦄
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get PHere = [ x ]
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get (PExt Z) = p .get Z
unrestrict-label-≃ (L ,, SArr s As t) (M ,, SArr s′ Bs t′) p [ Arr≃ x q y ] .get (PShift PHere) = [ y ]

lift-stm-≃ : a ≃stm b → lift-stm a ≃stm lift-stm b
lift-stm-≃ {a = a} {b = b} [ p ] .get = begin
  < stm-to-term (lift-stm a) >tm
    ≈⟨ lift-stm-to-term a ⟩
  < lift-tm (stm-to-term a) >tm
    ≈⟨ lift-tm-≃ p ⟩
  < lift-tm (stm-to-term b) >tm
    ≈˘⟨ lift-stm-to-term b ⟩
  < stm-to-term (lift-stm b) >tm ∎
  where
    open Reasoning tm-setoid

label-linear-0V : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → stm-to-term (ap L (is-linear-max-path S)) ≃tm 0V [ label-to-sub L ]tm
label-linear-0V {S = S} L = begin
  < stm-to-term (ap L (is-linear-max-path S)) >tm
    ≈˘⟨ label-to-sub-stm L (SPath (is-linear-max-path S)) ⟩
  < path-to-term (is-linear-max-path S) [ label-to-sub L ]tm >tm
    ≈⟨ sub-action-≃-tm (is-linear-max-path-is-0V S) refl≃s ⟩
  < 0V [ label-to-sub L ]tm >tm ∎
  where
    open Reasoning tm-setoid

stm-to-other-prop : (a : STm X) → stm-to-other a ≃stm a
sty-to-other-prop : (As : STy X) → sty-to-other As ≃sty As
label-to-other-prop : (L : Label X S) → label-to-other L ≃l L

stm-to-other-prop a@(SExt _) = [ refl≃tm ]
stm-to-other-prop a@(SShift _) = [ refl≃tm ]
stm-to-other-prop a@(SPath _) = [ refl≃tm ]
stm-to-other-prop (SCoh S A L) = ≃SCoh S refl≃sty (label-to-other-prop (ap L)) (sty-to-other-prop (lty L))
stm-to-other-prop (SOther t) = refl≃stm

sty-to-other-prop S⋆ = [ refl≃ty ]
sty-to-other-prop (SArr s As t) = ≃SArr (stm-to-other-prop s)
                                        (sty-to-other-prop As)
                                        (stm-to-other-prop t)

label-to-other-prop L .get P = stm-to-other-prop (L P)
