module Catt.Tree.Structured.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

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

≃stm-dec : (a : STm X) → (b : STm Y) → Dec (a ≃stm b)
≃stm-dec a b with ≃tm-dec (stm-to-term a) (stm-to-term b)
... | yes p = yes [ p ]
... | no p = no (λ where [ x ] → p x)

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

SArr≃ : {A : STy X} → {B : STy Y} → (a ≃stm a′) → A ≃sty B → b ≃stm b′ → SArr a A b ≃sty SArr a′ B b′
SArr≃ [ p ] [ q ] [ r ] = [ Arr≃ p q r ]

SArr≃-proj₁ : SArr a As b ≃sty SArr a′ Bs b′ → a ≃stm a′
SArr≃-proj₁ [ Arr≃ p _ _ ] = [ p ]

SArr≃-proj₂ : SArr a As b ≃sty SArr a′ Bs b′ → As ≃sty Bs
SArr≃-proj₂ [ Arr≃ _ p _ ] = [ p ]

SArr≃-proj₃ : SArr a As b ≃sty SArr a′ Bs b′ → b ≃stm b′
SArr≃-proj₃ [ Arr≃ _ _ p ] = [ p ]

S⋆-≃ : S ≃ T → S⋆ {X = someTree S} ≃sty S⋆ {X = someTree T}
S⋆-≃ p = [ (Star≃ (cong suc (≃-to-same-n p))) ]

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

SExt≃ : a ≃stm b → S ≃ T → SExt {T = S} a ≃stm SExt {T = T} b
SExt≃ [ p ] q = [ sub-action-≃-tm (susp-tm-≃ p) (connect-susp-inc-left-≃ (cong pred (≃tm-to-same-length p)) (≃-to-same-n q)) ]

SShift≃ : S ≃ T → a ≃stm b → SShift {S = S} a ≃stm SShift {S = T} b
SShift≃ p [ q ] = [ sub-action-≃-tm q (connect-susp-inc-right-≃ (≃-to-same-n p) (cong pred (≃tm-to-same-length q))) ]

SPath≃ : P ≃p Q → SPath P ≃stm SPath Q
SPath≃ p = [ path-to-term-≃ p ]

label-to-sub-≃ : (L : Label-WT X S) → (M : Label-WT Y S) → (ap L ≃l ap M) → lty L ≃sty lty M → label-to-sub L ≃s label-to-sub M
label-to-sub-≃ {S = Sing} L M [ p ] q = Ext≃ (Null≃ (q .get)) (p PHere .get)
label-to-sub-≃ {S = Join S T} L M [ p ] q
  = sub-from-connect-≃ (unrestrict-≃ (label-to-sub-≃ (label₁ L) (label₁ M) ([ (λ P → p (PExt P)) ]) (SArr≃ (p PHere) q (p (PShift PHere)))))
                       (label-to-sub-≃ (label₂ L) (label₂ M) ([ (λ P → p (PShift P)) ]) q)

SCoh≃ : (S : Tree n) → {A A′ : STy (someTree S)} → A ≃sty A′ → {L : Label-WT X S} → {M : Label-WT Y S} → ap L ≃l ap M → lty L ≃sty lty M → SCoh S A L ≃stm SCoh S A′ M
SCoh≃ S p q r .get = sub-action-≃-tm (Coh≃ refl≃c (p .get) refl≃s) (label-to-sub-≃ _ _ q r)

to-sty-to-type : (A : Ty n) → sty-to-type (to-sty A) ≃ty A
to-sty-to-type ⋆ = refl≃ty
to-sty-to-type (s ─⟨ A ⟩⟶ t) = Arr≃ refl≃tm (to-sty-to-type A) refl≃tm

sty-sub-to-type : (A : STy X) → (σ : Sub n m B) → sty-to-type (A [ σ ]sty) ≃ty sty-to-type A [ σ ]ty
sty-sub-to-type S⋆ σ = to-sty-to-type (sub-type σ)
sty-sub-to-type (SArr s A t) σ = Arr≃ refl≃tm (sty-sub-to-type A σ) refl≃tm

label-sub-to-sub : {X : MaybeTree n} → (L : Label-WT X S) → (σ : Sub n m B) → label-to-sub (L [ σ ]l) ≃s σ ● label-to-sub L
label-sub-to-sub {S = Sing} L σ = Ext≃ (Null≃ (sty-sub-to-type (lty L) σ)) refl≃tm
label-sub-to-sub {S = Join S T} L σ = begin
  < sub-from-connect (unrestrict (label-to-sub (label₁ (L [ σ ]l))))
                     (label-to-sub (label₂ (L [ σ ]l))) >s
    ≈⟨ sub-from-connect-≃ l1 l2 ⟩
  < sub-from-connect (σ ● unrestrict (label-to-sub (label₁ L)))
                     (σ ● label-to-sub (label₂ L)) >s
    ≈˘⟨ sub-from-connect-sub (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) σ ⟩
  < σ ● label-to-sub L >s ∎
  where
    open Reasoning sub-setoid

    l1 : unrestrict (label-to-sub (label₁ (L [ σ ]l))) ≃s (σ ● unrestrict (label-to-sub (label₁ L)))
    l1 = begin
      < unrestrict (label-to-sub (label₁ (L [ σ ]l))) >s
        ≡⟨⟩
      < unrestrict (label-to-sub (label₁ L [ σ ]l)) >s
        ≈⟨ unrestrict-≃ (label-sub-to-sub (label₁ L) σ) ⟩
      < unrestrict (σ ● label-to-sub (label₁ L)) >s
        ≈⟨ unrestrict-comp-higher σ (label-to-sub (label₁ L)) ⟩
      < σ ● unrestrict (label-to-sub (label₁ L)) >s ∎

    l2 : label-to-sub (label₂ (L [ σ ]l)) ≃s (σ ● label-to-sub (label₂ L))
    l2 = begin
      < label-to-sub (label₂ (L [ σ ]l)) >s
        ≡⟨⟩
      < label-to-sub (label₂ L [ σ ]l) >s
        ≈⟨ label-sub-to-sub (label₂ L) σ ⟩
      < σ ● label-to-sub (label₂ L) >s ∎

label-to-sub-stm : (L : Label-WT X S) → (a : STm (someTree S)) → stm-to-term a [ label-to-sub L ]tm ≃tm stm-to-term (a >>= L)
label-comp-to-sub : (L : Label-WT (someTree T) S) → (M : Label-WT X T) → label-to-sub M ● label-to-sub L ≃s label-to-sub (L ●lt M)
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
  < Coh (tree-to-ctx U) (sty-to-type A) idSub [ label-to-sub (M ●lt L) ]tm >tm ∎
  where
    open Reasoning tm-setoid

label-to-sub-sty : (L : Label-WT X S) → (A : STy (someTree S)) → sty-to-type A [ label-to-sub L ]ty ≃ty sty-to-type (A >>=′ L)
label-to-sub-sty L S⋆ = refl≃ty
label-to-sub-sty L (SArr s A t) = Arr≃ (label-to-sub-stm L s) (label-to-sub-sty L A) (label-to-sub-stm L t)

stm-label-to-sub : (L : Label-WT X S) → (a : STm (someTree S)) → a [ label-to-sub L ]stm ≃stm a >>= L
stm-label-to-sub L a .get = label-to-sub-stm L a

sty-label-to-sub : (L : Label-WT X S) → (A : STy (someTree S)) → A [ label-to-sub L ]sty ≃sty A >>=′ L
sty-label-to-sub L As .get = begin
  < sty-to-type (As [ label-to-sub L ]sty) >ty
    ≈⟨ sty-sub-to-type As (label-to-sub L) ⟩
  < sty-to-type As [ label-to-sub L ]ty >ty
    ≈⟨ label-to-sub-sty L As ⟩
  < sty-to-type (As >>=′ L) >ty ∎
  where
    open Reasoning ty-setoid

label-comp-to-sub L M = begin
  < label-to-sub M ● label-to-sub L >s
    ≈˘⟨ label-sub-to-sub L (label-to-sub M) ⟩
  < label-to-sub (L [ label-to-sub M ]l) >s
    ≈⟨ label-to-sub-≃ (L [ label-to-sub M ]l) (L ●lt M) [ (λ P → stm-label-to-sub M (ap L P)) ] (sty-label-to-sub M (lty L)) ⟩
  < label-to-sub (L ●lt M) >s ∎
  where
    open Reasoning sub-setoid

label-to-sub-lem L = begin
  < get-snd [ unrestrict (label-to-sub (label₁ L)) ]tm >tm
    ≈⟨ unrestrict-snd (label-to-sub (label₁ L)) ⟩
  < apt L (PShift PHere) >tm
    ≡⟨⟩
  < apt (label₂ L) PHere >tm
    ≈˘⟨ label-to-sub-path (label₂ L) PHere ⟩
  < Var (fromℕ _) [ label-to-sub (label₂ L) ]tm >tm ∎
    where
      open Reasoning tm-setoid

>>=-≃ : (a ≃stm b) → ∀ {L : Label-WT X S} {M : Label-WT Y S} → ap L ≃l ap M → lty L ≃sty lty M → a >>= L ≃stm b >>= M
>>=-≃ {a = a} {b = b} p {L = L} {M = M} q r .get = begin
  < stm-to-term (a >>= L) >tm
    ≈˘⟨ label-to-sub-stm L a ⟩
  < stm-to-term a [ label-to-sub L ]tm >tm
    ≈⟨ sub-action-≃-tm (p .get) (label-to-sub-≃ _ _ q r) ⟩
  < stm-to-term b [ label-to-sub M ]tm >tm
    ≈⟨ label-to-sub-stm M b ⟩
  < stm-to-term (b >>= M) >tm ∎
  where
    open Reasoning tm-setoid

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

compute-1 : compute-stm a ≃stm b → a ≃stm b
compute-1 {a = a} {b = b} p = begin
  < a >stm
    ≈˘⟨ compute-to-term a ⟩
  < compute-stm a >stm
    ≈⟨ p ⟩
  < b >stm ∎
  where
    open Reasoning stm-setoid

compute-2 : a ≃stm compute-stm b → a ≃stm b
compute-2 {a = a} {b = b} p = begin
  < a >stm
    ≈⟨ p ⟩
  < compute-stm b >stm
    ≈⟨ compute-to-term b ⟩
  < b >stm ∎
  where
    open Reasoning stm-setoid

compute-≃ : compute-stm a ≃stm compute-stm b → a ≃stm b
compute-≃ p = compute-1 (compute-2 p)

ap-≃ : {L : Label X S} → {M : Label Y S} → L ≃l M → P ≃p Q → L P ≃stm M Q
ap-≃ p (Here≃ x) = p .get PHere
ap-≃ p (Ext≃ q x) = ap-≃ [ (λ P → p .get (PExt P)) ] q
ap-≃ p (Shift≃ x q) = ap-≃ [ (λ P → p .get (PShift P)) ] q

ap′-≃ : (L : Label′ T S) → P ≃p Q → L P ≃p L Q
ap′-≃ L (Here≃ x) = refl≃p
ap′-≃ L (Ext≃ q x) = ap′-≃ (L ∘ PExt) q
ap′-≃ L (Shift≃ x q) = ap′-≃ (L ∘ PShift) q

label-comp-≃ : {L L′ : Label (someTree T) S} → {M : Label-WT X T} → {M′ : Label-WT Y T} → L ≃l L′ → ap M ≃l ap M′ → lty M ≃sty lty M′ → L ●l M ≃l L′ ●l M′
label-comp-≃ p q r .get Z = >>=-≃ (p .get Z) q r

>>=′-≃ : As ≃sty Bs → L ≃l M → As′ ≃sty Bs′ → As >>=′ (L ,, As′) ≃sty Bs >>=′ (M ,, Bs′)
>>=′-≃ {As = S⋆} {S⋆} {L = L} {M} {As′ = As′} {Bs′} p q r = r
>>=′-≃ {As = SArr s As t} {SArr s′ Bs t′} {L = L} {M} {As′ = As′} {Bs′} [ Arr≃ x y z ] q r
  = SArr≃ (>>=-≃ {a = s} {b = s′} [ x ] q r)
          (>>=′-≃ [ y ] q r)
          (>>=-≃ {a = t} {b = t′} [ z ] q r)

label-comp-assoc : (L : Label-WT (someTree S) U) → (M : Label-WT (someTree T) S) → (N : Label-WT X T) → ap (L ●lt M ●lt N) ≃l ap (L ●lt (M ●lt N))
>>=′-assoc : (A : STy (someTree S)) → (L : Label-WT (someTree T) S) → (M : Label-WT X T) → A >>=′ L >>=′ M ≃sty A >>=′ L ●lt M
>>=-assoc : (a : STm (someTree S)) → (L : Label-WT (someTree T) S) → (M : Label-WT X T) → a >>= L >>= M ≃stm a >>= L ●lt M

label-comp-assoc L M N .get Z = >>=-assoc (ap L Z) M N

>>=′-assoc S⋆ L M = refl≃sty
>>=′-assoc (SArr s A t) L M = SArr≃ (>>=-assoc s L M) (>>=′-assoc A L M) (>>=-assoc t L M)

>>=-assoc (SExt a) L M = >>=-assoc a (label₁ L) M
>>=-assoc (SShift a) L M = >>=-assoc a (label₂ L) M
>>=-assoc (SPath x) L M = refl≃stm
>>=-assoc (SCoh S A L′) L M = SCoh≃ S refl≃sty (label-comp-assoc L′ L M) (>>=′-assoc (lty L′) L M)

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

map-sty-ext-≃ : {As Bs : STy (someTree S)} → As ≃sty Bs → map-sty-ext {T = T} As ≃sty map-sty-ext {T = T} Bs
map-sty-ext-≃ {As = S⋆} {Bs = S⋆} [ p ] = refl≃sty
map-sty-ext-≃ {As = SArr s As t} {Bs = SArr s₁ Bs t₁} [ Arr≃ p q r ] = SArr≃ (SExt≃ [ p ] refl≃) (map-sty-ext-≃ [ q ]) (SExt≃ [ r ] refl≃)

map-sty-shift-≃ : {As Bs : STy (someTree T)} → As ≃sty Bs → map-sty-shift {S = S} As ≃sty map-sty-shift {S = S} Bs
map-sty-shift-≃ {As = S⋆} {Bs = S⋆} [ p ] = refl≃sty
map-sty-shift-≃ {As = SArr s As t} {Bs = SArr s₁ Bs t₁} [ Arr≃ p q r ] = SArr≃ (SShift≃ refl≃ [ p ]) (map-sty-shift-≃ [ q ]) (SShift≃ refl≃ [ r ])

map-sty-shift-prop : (A : STy (someTree T)) → map-sty-shift {S = S} A ≃sty A [ connect-susp-inc-right (tree-size S) (tree-size T) ]sty
map-sty-shift-prop S⋆ = [ refl≃ty ]
map-sty-shift-prop (SArr s A t) = SArr≃ [ refl≃tm ] (map-sty-shift-prop A) [ refl≃tm ]

label-to-sub-map-shift : (L : Label-WT (someTree T) S) → label-to-sub (map-shift {S = U} L) ≃s connect-susp-inc-right (tree-size U) (tree-size T) ● label-to-sub L
label-to-sub-map-shift {U = U} L = begin
  < label-to-sub (map-shift {S = U} L) >s
    ≈⟨ label-to-sub-≃ (map-shift {S = U} L) (L [ connect-susp-inc-right (tree-size U) _ ]l) [ (λ P → [ refl≃tm ]) ] (map-sty-shift-prop {S = U} (lty L)) ⟩
  < label-to-sub (L [ connect-susp-inc-right (tree-size U) _ ]l) >s
    ≈⟨ label-sub-to-sub L (connect-susp-inc-right (tree-size U) _) ⟩
  < connect-susp-inc-right (tree-size U) _ ● label-to-sub L >s ∎
  where
    open Reasoning sub-setoid

map-sty-ext-prop : (A : STy (someTree S)) → susp-sty A [ connect-susp-inc-left (tree-size S) (tree-size T) ]sty ≃sty map-sty-ext {T = T} A
map-sty-ext-prop S⋆ = SArr≃ [ (connect-inc-left-fst-var get-snd _) ] [ refl≃ty ] [ connect-inc-fst-var get-snd _ ]
map-sty-ext-prop (SArr s A t) = SArr≃ [ sub-action-≃-tm (id-on-tm (susp-tm (stm-to-term s))) refl≃s ] (map-sty-ext-prop A) [ sub-action-≃-tm (id-on-tm (susp-tm (stm-to-term t))) refl≃s ]

label-to-sub-map-ext : (L : Label-WT (someTree T) S) → label-to-sub (map-ext {T = U} L) ≃s connect-susp-inc-left (tree-size T) (tree-size U) ● susp-sub-res (label-to-sub L)
label-to-sub-map-ext {U = U} L = begin
  < label-to-sub (map-ext {T = U} L) >s
    ≈˘⟨ label-to-sub-≃ (susp-label L [ connect-susp-inc-left _ (tree-size U) ]l)
                       (map-ext {T = U} L)
                       [ (λ P → [ sub-action-≃-tm (id-on-tm (susp-tm (stm-to-term (ap L P)))) refl≃s ]) ]
                       (map-sty-ext-prop (lty L)) ⟩
  < label-to-sub (susp-label L [ connect-susp-inc-left _ (tree-size U) ]l) >s
    ≈⟨ label-sub-to-sub (susp-label L) (connect-susp-inc-left _ (tree-size U)) ⟩
  < connect-susp-inc-left _ (tree-size U) ● label-to-sub (susp-label L) >s
    ≈⟨ sub-action-≃-sub (susp-label-to-sub L) refl≃s ⟩
  < connect-susp-inc-left _ (tree-size U) ● susp-sub-res (label-to-sub L) >s ∎
  where
    open Reasoning sub-setoid

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
      < unrestrict (label-to-sub (map-ext {T = T} (id-label-wt S))) >s
        ≈⟨ unrestrict-≃ (label-to-sub-map-ext {U = T} (id-label-wt S)) ⟩
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
      < label-to-sub (map-shift {S = S} (id-label-wt T)) >s
        ≈⟨ label-to-sub-map-shift {U = S} (id-label-wt T) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ● label-to-sub (id-label-wt T) >s
        ≈⟨ sub-action-≃-sub (id-label-to-sub T) refl≃s ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) ● idSub >s
        ≈⟨ id-right-unit (connect-susp-inc-right (tree-size S) (tree-size T)) ⟩
      < connect-susp-inc-right (tree-size S) (tree-size T) >s ∎

sub-to-label-to-sub : (S : Tree n) → (σ : Sub (suc n) m A) → label-to-sub (to-label-wt S σ) ≃s σ
sub-to-label-to-sub {A = A} S σ = begin
  < label-to-sub (to-label-wt S σ) >s
    ≡⟨⟩
  < label-to-sub (id-label-wt S [ σ ]l) >s
    ≈⟨ label-sub-to-sub (id-label-wt S) σ ⟩
  < σ ● label-to-sub (id-label-wt S) >s
    ≈⟨ sub-action-≃-sub (id-label-to-sub S) refl≃s ⟩
  < σ ● idSub >s
    ≈⟨ id-right-unit σ ⟩
  < σ >s ∎
  where
    open Reasoning sub-setoid

label-to-sub-to-label : (L : Label-WT X S) → ap (to-label-wt S (label-to-sub L)) ≃l ap L
label-to-sub-to-label L .get Z .get = label-to-sub-path L Z

sty-to-type-to-sty : (As : STy X) → to-sty (sty-to-type As) ≃sty As
sty-to-type-to-sty As .get = to-sty-to-type (sty-to-type As)

>>=-id : (a : STm (someTree T)) → a >>= id-label-wt T ≃stm a
>>=-id {T = T} a .get = begin
  < stm-to-term (a >>= id-label-wt T) >tm
    ≈˘⟨ label-to-sub-stm (id-label-wt T) a ⟩
  < stm-to-term a [ label-to-sub (id-label-wt T) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (id-label-to-sub T) ⟩
  < stm-to-term a [ idSub ]tm >tm
    ≈⟨ id-on-tm (stm-to-term a) ⟩
  < stm-to-term a >tm ∎
  where
    open Reasoning tm-setoid

>>=′-id : (As : STy (someTree T)) → As >>=′ id-label-wt T ≃sty As
>>=′-id {T = T} As = [ begin
  < sty-to-type (As >>=′ id-label-wt T) >ty
    ≈˘⟨ label-to-sub-sty (id-label-wt T) As ⟩
  < sty-to-type As [ label-to-sub (id-label-wt T) ]ty >ty
    ≈⟨ sub-action-≃-ty (refl≃ty {A = sty-to-type As}) (id-label-to-sub T) ⟩
  < sty-to-type As [ idSub ]ty >ty
    ≈⟨ id-on-ty (sty-to-type As) ⟩
  < sty-to-type As >ty ∎ ]
  where
    open Reasoning ty-setoid

comp-right-unit : (L : Label (someTree T) S) → L ●l id-label-wt T ≃l L
comp-right-unit L .get Z = >>=-id (L Z)

_≃lm_ : (L : Label X S) → (M : Label Y S) → Set
_≃lm_ {S = S} L M = Wrap (λ L M → ∀ (Q : Path S) → .⦃ is-maximal Q ⦄ → L Q ≃stm M Q) L M

refl≃lm : L ≃lm L
refl≃lm = [ (λ Q → refl≃stm ) ]

sym≃lm : L ≃lm M → M ≃lm L
sym≃lm p .get Z = sym≃stm (p .get Z)

≃l-to-≃lm : L ≃l M → L ≃lm M
≃l-to-≃lm p .get Z = p .get Z

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
ppath-≃l p .get P = SPath≃ (sym≃p (ppath-≃-≃p p P))

_≃l′_ : Label X S → Label Y T → Set
_≃l′_ {S = S} {T = T} L M = Σ[ p ∈ S ≃′ T ] L ≃l label-≃ p M

label-to-sub-≃′ : (L : Label-WT X S) → (M : Label-WT Y T) → ap L ≃l′ ap M → lty L ≃sty lty M → label-to-sub L ≃s label-to-sub M
label-to-sub-≃′ L M (p ,, [ q ]) r with ≃-to-same-n (≃′-to-≃ p)
... | refl with ≃-to-≡ (≃′-to-≃ p)
... | refl = label-to-sub-≃ L M [ (λ P → trans≃stm (q P) (ap-≃ (refl≃l {L = ap M}) (sym≃p (ppath-≃-≃p p P)))) ] r

>>=-≃′ : {L : Label-WT X S} → {M : Label-WT Y T} → a ≃stm b → ap L ≃l′ ap M → lty L ≃sty lty M → a >>= L ≃stm b >>= M
>>=-≃′ {M = M} p (q ,, q′) r with ≃-to-same-n (≃′-to-≃ q)
... | refl with ≃-to-≡ (≃′-to-≃ q)
... | refl = >>=-≃ p (trans≃l q′ [ (λ P → ap-≃ (refl≃l {L = ap M}) (sym≃p (ppath-≃-≃p q P))) ]) r

>>=-susp-label : (a : STm (someTree S)) → (L : Label-WT X S) → susp-stm (a >>= L) ≃stm (a >>= susp-label L)
>>=-susp-label a L .get = begin
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
  < stm-to-term (a >>= susp-label L) >tm ∎
  where
    open Reasoning tm-setoid

>>=′-susp-label : (As : STy (someTree S)) → (L : Label-WT X S) → susp-sty (As >>=′ L) ≃sty As >>=′ susp-label L
>>=′-susp-label S⋆ L = refl≃sty
>>=′-susp-label (SArr s As t) L = SArr≃ (>>=-susp-label s L) (>>=′-susp-label As L) (>>=-susp-label t L)

>>=-shift : (a : STm (someTree U)) → (L : Label-WT (someTree T) U) → a >>= map-shift {S = S} L ≃stm SShift {S = S} (a >>= L)
>>=-shift a L .get = begin
  < stm-to-term (a >>= map-shift L) >tm
    ≈˘⟨ label-to-sub-stm (map-shift L) a ⟩
  < stm-to-term a [ label-to-sub (map-shift L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (label-to-sub-map-shift L) ⟩
  < stm-to-term a [ connect-susp-inc-right _ _ ● label-to-sub L ]tm >tm
    ≈⟨ assoc-tm _ _ (stm-to-term a) ⟩
  < stm-to-term a [ label-to-sub L ]tm [ connect-susp-inc-right _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (label-to-sub-stm L a) refl≃s ⟩
  < stm-to-term (a >>= L) [ connect-susp-inc-right _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

SCoh-shift : (U : Tree n) → (As : STy (someTree U)) → (L : Label-WT (someTree T) U) → SCoh U As (map-shift {S = S} L) ≃stm SShift {S = S} (SCoh U As L)
SCoh-shift U As L = >>=-shift (SCoh U As (id-label-wt U)) L

>>=′-shift : (As : STy (someTree U)) -> (L : Label-WT (someTree T) U) → As >>=′ map-shift {S = S} L ≃sty map-sty-shift {S = S} (As >>=′ L)
>>=′-shift S⋆ L = refl≃sty
>>=′-shift (SArr s As t) L = SArr≃ (>>=-shift s L) (>>=′-shift As L) (>>=-shift t L)

comp-shift : (M : Label (someTree U) U′) -> (L : Label-WT (someTree T) U) → M ●l map-shift {S = S} L ≃l (SShift {S = S} ∘ (M ●l L))
comp-shift M L .get Z = >>=-shift (M Z) L

>>=-ext : (a : STm (someTree U)) → (L : Label-WT (someTree S) U) → a >>= map-ext {T = T} L ≃stm SExt {T = T} (a >>= L)
>>=-ext a L .get = begin
  < stm-to-term (a >>= map-ext L) >tm
    ≈˘⟨ label-to-sub-stm (map-ext L) a ⟩
  < stm-to-term a [ label-to-sub (map-ext L) ]tm >tm
    ≈⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (label-to-sub-map-ext L) ⟩
  < stm-to-term a [ connect-susp-inc-left _ _ ● susp-sub-res (label-to-sub L) ]tm >tm
    ≈⟨ assoc-tm _ _ (stm-to-term a) ⟩
  < stm-to-term a [ susp-sub-res (label-to-sub L) ]tm [ connect-susp-inc-left _ _ ]tm >tm
    ≈˘⟨ sub-action-≃-tm (susp-res-comp-tm (stm-to-term a) (label-to-sub L)) refl≃s ⟩
  < susp-tm (stm-to-term a [ label-to-sub L ]tm) [ connect-susp-inc-left _ _ ]tm >tm
    ≈⟨ sub-action-≃-tm (susp-tm-≃ (label-to-sub-stm L a)) refl≃s ⟩
  < susp-tm (stm-to-term (a >>= L)) [ connect-susp-inc-left _ _ ]tm >tm ∎
  where
    open Reasoning tm-setoid

SCoh-ext : (U : Tree n) → (As : STy (someTree U)) → (L : Label-WT (someTree S) U) → SCoh U As (map-ext {T = T} L) ≃stm SExt {T = T} (SCoh U As L)
SCoh-ext U As L = >>=-ext (SCoh U As (id-label-wt U)) L

>>=′-ext : (As : STy (someTree U)) -> (L : Label-WT (someTree S) U) → As >>=′ map-ext {T = T} L ≃sty map-sty-ext {T = T} (As >>=′ L)
>>=′-ext S⋆ L = refl≃sty
>>=′-ext (SArr s As t) L = SArr≃ (>>=-ext s L) (>>=′-ext As L) (>>=-ext t L)

comp-ext : (M : Label (someTree U) U′) -> (L : Label-WT (someTree S) U) → M ●l map-ext {T = T} L ≃l (SExt {T = T} ∘ (M ●l L))
comp-ext M L .get Z = >>=-ext (M Z) L

susp-label-full-to-sub : (L : Label X S) → label-to-sub (susp-label-full L ,, S⋆) ≃s susp-sub (label-to-sub (L ,, S⋆))
susp-label-full-to-sub L = unrestrict-≃ (susp-label-to-sub (L ,, S⋆))

SCoh-unrestrict : (S : Tree n) → (As : STy (someTree S)) → (L : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → SCoh S As L ≃stm SCoh (Susp S) (susp-sty As) (unrestrict-label L ,, sty-base (lty L))
SCoh-unrestrict S As (L ,, SArr s Bs t) .get
  = sub-action-≃-tm (Coh≃ refl≃c (sym≃ty (susp-sty-to-type As)) susp-functorial-id)
                    (refl≃s {σ = unrestrict (label-to-sub′ (λ P → stm-to-term (L P))
                                                           (stm-to-term s ─⟨ sty-to-type Bs ⟩⟶ stm-to-term t))})

>>=-unrestrict : (a : STm (someTree S)) → (L : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → susp-stm a >>= (unrestrict-label L ,, sty-base (lty L)) ≃stm a >>= L
>>=-unrestrict a (L ,, SArr s As t) = refl≃stm

>>=′-unrestrict : (As : STy (someTree S)) → (L : Label-WT X S) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → susp-sty As >>=′ (unrestrict-label L ,, sty-base (lty L)) ≃sty As >>=′ L
>>=′-unrestrict S⋆ (L ,, SArr s Bs t) = refl≃sty
>>=′-unrestrict (SArr s As t) L = SArr≃ (>>=-unrestrict s L) (>>=′-unrestrict As L) (>>=-unrestrict t L)

susp-stm-functorial : (a : STm (someTree S)) → (L : Label X S) → susp-stm (a >>= (L ,, S⋆)) ≃stm susp-stm a >>= (susp-label-full L ,, S⋆)
susp-stm-functorial a L = begin
  < susp-stm (a >>= (L ,, S⋆)) >stm
    ≈⟨ >>=-susp-label a (L ,, S⋆) ⟩
  < a >>= susp-label (L ,, S⋆) >stm
    ≈˘⟨ >>=-unrestrict a (susp-label (L ,, S⋆)) ⟩
  < susp-stm a >>= (susp-label-full L ,, S⋆) >stm ∎
  where
    open Reasoning stm-setoid

susp-sty-functorial : (As : STy (someTree S)) → (L : Label X S) → susp-sty (As >>=′ (L ,, S⋆)) ≃sty susp-sty As >>=′ (susp-label-full L ,, S⋆)
susp-sty-functorial As L = begin
  < susp-sty (As >>=′ (L ,, S⋆)) >sty
    ≈⟨ >>=′-susp-label As (L ,, S⋆) ⟩
  < As >>=′ susp-label (L ,, S⋆) >sty
    ≈˘⟨ >>=′-unrestrict As (susp-label (L ,, S⋆)) ⟩
  < susp-sty As >>=′ (susp-label-full L ,, S⋆) >sty ∎
  where
    open Reasoning sty-setoid

id-label-susp-full : (T : Tree n) → susp-label-full (id-label T) ≃l id-label (Susp T)
id-label-susp-full T .get PHere = refl≃stm
id-label-susp-full T .get (PExt Z) = compute-≃ refl≃stm
id-label-susp-full T .get (PShift PHere) = compute-≃ refl≃stm

>>=-lift : (a : STm (someTree S)) → (L : Label-WT (Other n) S) → (a >>= lift-label L) ≃stm lift-stm (a >>= L)
>>=′-lift : (As : STy (someTree S)) → (L : Label-WT (Other n) S) → As >>=′ lift-label L ≃sty lift-sty (As >>=′ L)
comp-lift : (L : Label (someTree S) U) → (M : Label-WT (Other n) S) → L ●l lift-label M ≃l (lift-stm ∘ L ●l M)

>>=-lift (SExt a) L = >>=-lift a (label₁ L)
>>=-lift (SShift a) L = >>=-lift a (label₂ L)
>>=-lift (SPath x) L = refl≃stm
>>=-lift (SCoh S A M) L = SCoh≃ S refl≃sty (comp-lift (ap M) L) (>>=′-lift (lty M) L)

>>=′-lift S⋆ L = refl≃sty
>>=′-lift (SArr s As t) L = SArr≃ (>>=-lift s L) (>>=′-lift As L) (>>=-lift t L)

comp-lift L M .get Z = >>=-lift (L Z) M

map-sty-ext-susp-compat : (As : STy (someTree S)) → map-sty-ext {T = Sing} As ≃sty susp-sty As
map-sty-ext-susp-compat S⋆ = refl≃sty
map-sty-ext-susp-compat (SArr s As t) = SArr≃ refl≃stm (map-sty-ext-susp-compat As) refl≃stm

map-sty-ext-label : (As : STy (someTree S)) → (L : Label-WT X (Join S T)) → map-sty-ext As >>=′ L ≃sty As >>=′ label₁ L
map-sty-ext-label S⋆ L = refl≃sty
map-sty-ext-label (SArr s As t) L = SArr≃ refl≃stm (map-sty-ext-label As L) refl≃stm

map-sty-shift-label : (As : STy (someTree T)) → (L : Label-WT X (Join S T)) → map-sty-shift As >>=′ L ≃sty As >>=′ label₂ L
map-sty-shift-label S⋆ L = refl≃sty
map-sty-shift-label (SArr s As t) L = SArr≃ refl≃stm (map-sty-shift-label As L) refl≃stm

susp-stm-SCoh : (S : Tree n) → (As : STy (someTree S)) → (L : Label-WT X S) → susp-stm (SCoh S As L) ≃stm SCoh S As (susp-label L)
susp-stm-SCoh {X = someTree x} S As L = begin
  < susp-stm (SCoh S As L) >stm
    ≈˘⟨ SCoh-ext S As L ⟩
  < SCoh S As (map-ext L) >stm
    ≈⟨ SCoh≃ S refl≃sty refl≃l (map-sty-ext-susp-compat (lty L)) ⟩
  < SCoh S As (susp-label L) >stm ∎
  where open Reasoning stm-setoid
susp-stm-SCoh {X = Other _} S As L = refl≃stm

stm-sub-SCoh : {X : MaybeTree m} → (S : Tree n) → (As : STy (someTree S)) → (L : Label-WT X S) → (σ : Sub m l A) → SCoh S As L [ σ ]stm ≃stm SCoh S As (L [ σ ]l)
stm-sub-SCoh S As L σ .get = begin
  < Coh (tree-to-ctx S) (sty-to-type As) idSub [ label-to-sub L ]tm [ σ ]tm >tm
    ≈˘⟨ assoc-tm σ (label-to-sub L) (Coh (tree-to-ctx S) (sty-to-type As) idSub) ⟩
  < Coh (tree-to-ctx S) (sty-to-type As) idSub [ σ ● label-to-sub L ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = Coh (tree-to-ctx S) (sty-to-type As) idSub}) (label-sub-to-sub L σ) ⟩
  < Coh (tree-to-ctx S) (sty-to-type As) idSub [ label-to-sub (L [ σ ]l) ]tm >tm ∎
  where
    open Reasoning tm-setoid

stm-sub->>= : (a : STm (someTree S)) → (L : Label-WT X S) → (σ : Sub m n A) → (a >>= L) [ σ ]stm ≃stm (a >>= L [ σ ]l)
stm-sub->>= a L σ .get = begin
  < stm-to-term (a >>= L) [ σ ]tm >tm
    ≈˘⟨ sub-action-≃-tm (label-to-sub-stm L a) refl≃s ⟩
  < stm-to-term a [ label-to-sub L ]tm [ σ ]tm >tm
    ≈˘⟨ assoc-tm σ (label-to-sub L) (stm-to-term a) ⟩
  < stm-to-term a [ σ ● label-to-sub L ]tm >tm
    ≈˘⟨ sub-action-≃-tm (refl≃tm {s = stm-to-term a}) (label-sub-to-sub L σ) ⟩
  < stm-to-term a [ label-to-sub (L [ σ ]l) ]tm >tm
    ≈⟨ label-to-sub-stm (L [ σ ]l) a ⟩
  < stm-to-term (a >>= L [ σ ]l) >tm ∎
  where
    open Reasoning tm-setoid

stm-sub-≃ : a ≃stm b → (σ : Sub n m A) → a [ σ ]stm ≃stm b [ σ ]stm
stm-sub-≃ {a = a} {b = b} [ p ] σ .get = sub-action-≃-tm p refl≃s

label-linear-0V : (L : Label-WT X S) → .⦃ _ : is-linear S ⦄ → stm-to-term (ap L (is-linear-max-path S)) ≃tm 0V [ label-to-sub L ]tm
label-linear-0V {S = S} L = begin
  < stm-to-term (ap L (is-linear-max-path S)) >tm
    ≈˘⟨ label-to-sub-path L (is-linear-max-path S) ⟩
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
stm-to-other-prop (SCoh S A L) = SCoh≃ S refl≃sty (label-to-other-prop (ap L)) (sty-to-other-prop (lty L))
stm-to-other-prop (SOther t) = refl≃stm

sty-to-other-prop S⋆ = [ refl≃ty ]
sty-to-other-prop (SArr s As t) = SArr≃ (stm-to-other-prop s)
                                        (sty-to-other-prop As)
                                        (stm-to-other-prop t)

label-to-other-prop L .get P = stm-to-other-prop (L P)

1-Full : STy (someTree T) → Set
1-Full S⋆ = ⊥
1-Full {T = T} (SArr s S⋆ t) = s ≃stm (SHere {S = T}) ×′ t ≃stm SPath (last-path T)
1-Full (SArr s As@(SArr _ _ _) t) = WrapInst (1-Full As)

SExt-proj : SExt {T = Sing} a ≃stm SExt {T = Sing} b → a ≃stm b
SExt-proj {a = a} {b = b} [ p ] = [ (susp-tm-proj lem) ]
  where
    lem : susp-tm (stm-to-term a) ≃tm susp-tm (stm-to-term b)
    lem = begin
      < susp-tm (stm-to-term a) >tm
        ≈˘⟨ id-on-tm (susp-tm (stm-to-term a)) ⟩
      < susp-tm (stm-to-term a) [ idSub ]tm >tm
        ≈⟨ p ⟩
      < susp-tm (stm-to-term b) [ idSub ]tm >tm
        ≈⟨ id-on-tm (susp-tm (stm-to-term b)) ⟩
      < susp-tm (stm-to-term b) >tm ∎
      where
        open Reasoning tm-setoid

map-sty-ext-proj : {As Bs : STy (someTree S)} → map-sty-ext {T = Sing} As ≃sty map-sty-ext {T = Sing} Bs → As ≃sty Bs
map-sty-ext-proj {As = S⋆} {Bs = S⋆} p = refl≃sty
map-sty-ext-proj {As = S⋆} {Bs = SArr _ S⋆ _} [ Arr≃ _ () _ ]
map-sty-ext-proj {As = S⋆} {Bs = SArr _ (SArr _ _ _) _} [ Arr≃ _ () _ ]
map-sty-ext-proj {As = SArr s As t} {Bs = SArr s₁ Bs t₁} p
  = SArr≃ (SExt-proj (SArr≃-proj₁ p)) (map-sty-ext-proj (SArr≃-proj₂ p)) (SExt-proj (SArr≃-proj₃ p))
map-sty-ext-proj {As = SArr _ S⋆ _} {Bs = S⋆} [ Arr≃ _ () _ ]
map-sty-ext-proj {As = SArr _ (SArr _ _ _) _} {Bs = S⋆} [ Arr≃ _ () _ ]

unrestrict-label₁ : (L : Label-WT X (Susp S)) → unrestrict-label (label₁ L) ≃l ap L
unrestrict-label₁ L .get PHere = refl≃stm
unrestrict-label₁ L .get (PExt Z) = refl≃stm
unrestrict-label₁ L .get (PShift PHere) = refl≃stm
