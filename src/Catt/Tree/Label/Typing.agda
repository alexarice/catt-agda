open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Label.Typing {index : Set}
                              (rule : index → Rule) where

open import Catt.Prelude.Properties
open import Catt.Typing rule
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Support
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing.Properties.Base rule

stm-eq : {X : MaybeTree n} → (Γ : Ctx n) → STm X → STm X → Set
stm-eq Γ = Wrap (λ a b → stm-to-term a ≈[ Γ ]tm stm-to-term b)

sty-eq : {X : MaybeTree n} → (Γ : Ctx n) → STy X → STy X → Set
sty-eq Γ = Wrap (λ A B → sty-to-type A ≈[ Γ ]ty sty-to-type B)

syntax stm-eq ΓS a b = a ≈[ ΓS ]stm b
syntax sty-eq ΓS A B = A ≈[ ΓS ]sty B

refl≈stm : a ≈[ Γ ]stm a
refl≈stm = [ refl≈tm ]

sym≈stm : a ≈[ Γ ]stm b → b ≈[ Γ ]stm a
sym≈stm [ p ] = [ sym≈tm p ]

trans≈stm : a ≈[ Γ ]stm b → b ≈[ Γ ]stm c → a ≈[ Γ ]stm c
trans≈stm [ p ] [ q ] = [ trans≈tm p q ]

reflexive≈stm : a ≃stm b → a ≈[ Γ ]stm b
reflexive≈stm [ p ] = [ reflexive≈tm p ]

stm-setoid-≈ : {Γ : Ctx n} → {X : MaybeTree n} → Setoid _ _
stm-setoid-≈ {Γ = Γ} {X = X} = record { Carrier = STm X
                         ; _≈_ = λ x y → x ≈[ Γ ]stm y
                         ; isEquivalence = record { refl = refl≈stm
                                                  ; sym = sym≈stm
                                                  ; trans = trans≈stm
                                                  }
                         }

refl≈sty : As ≈[ Γ ]sty As
refl≈sty = [ refl≈ty ]

sym≈sty : As ≈[ Γ ]sty Bs → Bs ≈[ Γ ]sty As
sym≈sty [ p ] = [ sym≈ty p ]

trans≈sty : As ≈[ Γ ]sty Bs → Bs ≈[ Γ ]sty Cs → As ≈[ Γ ]sty Cs
trans≈sty [ p ] [ q ] = [ trans≈ty p q ]

reflexive≈sty : As ≃sty Bs → As ≈[ Γ ]sty Bs
reflexive≈sty [ p ] = [ reflexive≈ty p ]

sty-setoid-≈ : {Γ : Ctx n} → {X : MaybeTree n} → Setoid _ _
sty-setoid-≈ {Γ = Γ} {X = X} = record { Carrier = STy X
                         ; _≈_ = λ x y → x ≈[ Γ ]sty y
                         ; isEquivalence = record { refl = refl≈sty
                                                  ; sym = sym≈sty
                                                  ; trans = trans≈sty
                                                  }
                         }

≈SArr : a ≈[ Γ ]stm a′ → As ≈[ Γ ]sty Bs → b ≈[ Γ ]stm b′ → SArr a As b ≈[ Γ ]sty SArr a′ Bs b′
≈SArr [ p ] [ q ] [ r ] = [ Arr≈ p q r ]

≈SArr-proj₁ : SArr a As b ≈[ Γ ]sty SArr a′ Bs b′ → a ≈[ Γ ]stm a′
≈SArr-proj₁ [ Arr≈ p _ _ ] = [ p ]

≈SArr-proj₃ : SArr a As b ≈[ Γ ]sty SArr a′ Bs b′ → b ≈[ Γ ]stm b′
≈SArr-proj₃ [ Arr≈ _ _ p ] = [ p ]

label-max-equality : {X : MaybeTree n} → (ΓS : Ctx n) → (L M : Label X S) → Set
label-max-equality {S = S} Γ L M = Wrap (λ L M → ∀ (Q : Path S) → .⦃ is-Maximal Q ⦄ → L Q ≈[ Γ ]stm M Q) L M

syntax label-max-equality Γ L M = L ≈[ Γ ]lm M

refl≈lm : L ≈[ Γ ]lm L
refl≈lm .get Z = refl≈stm

label-equality : {X : MaybeTree n} → (Γ : Ctx n) → (L M : Label X S) → Set
label-equality {S = S} Γ L M = Wrap (λ L M → ∀ (Q : Path S) → L Q ≈[ Γ ]stm M Q) L M

syntax label-equality Γ L M = L ≈[ Γ ]l M

refl≈l : L ≈[ Γ ]l L
refl≈l .get Z = refl≈stm

reflexive≈l : L ≃l M → L ≈[ Γ ]l M
reflexive≈l [ p ] .get Z = reflexive≈stm (p Z)

compute-≈ : {a b : STm (someTree S)} → compute-stm a ≈[ tree-to-ctx S ]stm compute-stm b → a ≈[ tree-to-ctx S ]stm b
compute-≈ {a = a} {b = b} p = begin
  a
    ≈˘⟨ reflexive≈stm (compute-to-term a) ⟩
  compute-stm a
    ≈⟨ p ⟩
  compute-stm b
    ≈⟨ reflexive≈stm (compute-to-term b) ⟩
  b ∎
  where
    open Reasoning stm-setoid-≈

fixup-reflexive≈stm : {a : STm (someTree S)} → {b : STm (someTree T)} → a ≃stm b → (p : S ≃′ T) → a ≈[ tree-to-ctx S ]stm stm-≃ (sym≃′ p) b
fixup-reflexive≈stm {a = a} {b} q p = reflexive≈stm (begin
  < a >stm
    ≈⟨ q ⟩
  < b >stm
    ≈⟨ stm-≃-≃stm (sym≃′ p) b ⟩
  < stm-≃ (sym≃′ p) b >stm ∎)
  where
    open Reasoning stm-setoid

stm-≃-≈ : (p : S ≃′ T) → a ≈[ tree-to-ctx S ]stm b → stm-≃ p a ≈[ tree-to-ctx T ]stm stm-≃ p b
stm-≃-≈ {a = a} {b = b} p q with ≃-to-same-n (≃′-to-≃ p)
... | refl with ≃-to-≡ (≃′-to-≃ p)
... | refl = begin
  stm-≃ p a
    ≈˘⟨ reflexive≈stm (stm-≃-≃stm p a) ⟩
  a
    ≈⟨ q ⟩
  b
    ≈⟨ reflexive≈stm (stm-≃-≃stm p b) ⟩
  stm-≃ p b ∎
  where
    open Reasoning stm-setoid-≈

sty-dim-≈ : As ≈[ Γ ]sty Bs → sty-dim As ≡ sty-dim Bs
sty-dim-≈ {As = S⋆} {Bs = S⋆} [ p ] = refl
sty-dim-≈ {As = SArr _ As _} {Bs = SArr _ Bs _} [ Arr≈ _ p _ ] = cong suc (sty-dim-≈ [ p ])

sty-base-≈ : As ≈[ Γ ]sty Bs → sty-base As ≈[ Γ ]sty sty-base Bs
sty-base-≈ {As = S⋆} {Bs = S⋆} [ p ] = [ Star≈ ]
sty-base-≈ {As = SArr _ As _} {Bs = SArr _ Bs _} [ Arr≈ _ p _ ] = [ p ]

sty-src-≈ : {As Bs : STy X} → (p : As ≈[ Γ ]sty Bs) → .⦃ _ : NonZero (sty-dim As) ⦄ → sty-src As ≈[ Γ ]stm sty-src Bs ⦃ NonZero-subst (sty-dim-≈ p) it ⦄
sty-src-≈ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≈ p _ _ ] = [ p ]

sty-tgt-≈ : {As Bs : STy X} → (p : As ≈[ Γ ]sty Bs) → .⦃ _ : NonZero (sty-dim As) ⦄ → sty-tgt As ≈[ Γ ]stm sty-tgt Bs ⦃ NonZero-subst (sty-dim-≈ p) it ⦄
sty-tgt-≈ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≈ _ _ p ] = [ p ]

{-
data Typing-STm : (ΓS : CtxOrTree m) → STm (COT-to-MT ΓS) → STy (COT-to-MT ΓS) → Set
data Typing-Label : (ΓS : CtxOrTree m) → Label-WT (COT-to-MT ΓS) S → Set
data Typing-STy : (ΓS : CtxOrTree m) → STy (COT-to-MT ΓS) → Set

data Typing-STm where
  TySConv : Typing-STm ΓS a As → (As ≈[ ΓS ]sty Bs) → Typing-STm ΓS a Bs
  TySPath : (P : Path S) → Typing-STm (incTree S) (SPath P) (getPathType P)
  TySExt : Typing-STm (incTree S) a As → Typing-STm (incTree (Join S T)) (SExt a) (map-sty-pext As)
  TySShift : Typing-STm (incTree T) a As → Typing-STm (incTree (Join S T)) (SShift a) (map-sty-pshift As)
  TySCoh : (S : Tree n) → {As : STy (someTree S)} → {L : Label-WT (COT-to-MT ΓS) S}
         → Typing-STy (incTree S) As
         → Typing-Label ΓS L
         → Typing-STy ΓS (lty L)
         → (b : Bool)
         → supp-condition-s b S As
         → Typing-STm ΓS (SCoh S As L) (label-on-sty As L)
  TySOther : Typing-Tm Γ s (sty-to-type As) → Typing-STm (incCtx Γ) (SOther s) As

data Typing-Label where
  TySing : {L : Label-WT (COT-to-MT ΓS) Sing} → Typing-STm ΓS (ap L PHere) (lty L) → Typing-Label ΓS L
  TyJoin : {L : Label-WT (COT-to-MT ΓS) (Join S T)}
         → Typing-STm ΓS (ap L PHere) (lty L)
         → Typing-Label ΓS (label₁ L)
         → Typing-Label ΓS (label₂ L)
         → Typing-Label ΓS L

data Typing-STy where
  TySStar : Typing-STy ΓS S⋆
  TySArr : Typing-STm ΓS a As → Typing-STy ΓS As → Typing-STm ΓS b As → Typing-STy ΓS (SArr a As b)


ap-phere-Ty : {L : Label-WT (COT-to-MT ΓS) S} → Typing-Label ΓS L → Typing-Tm (COT-to-Ctx ΓS) (apt L PHere) (sty-to-type (lty L))
stm-to-term-Ty : Typing-STm ΓS a As → Typing-Tm (COT-to-Ctx ΓS) (stm-to-term a) (sty-to-type As)
sty-to-type-Ty : Typing-STy ΓS As → Typing-Ty (COT-to-Ctx ΓS) (sty-to-type As)
label-to-sub-Ty′ : {L : Label-WT (COT-to-MT ΓS) S} → Typing-Label ΓS L → Typing-Ty (COT-to-Ctx ΓS) (sty-to-type (lty L)) → Typing-Sub (tree-to-ctx S) (COT-to-Ctx ΓS) (label-to-sub L)
label-to-sub-Ty : {L : Label-WT (COT-to-MT ΓS) S} → Typing-Label ΓS L → Typing-STy ΓS (lty L) → Typing-Sub (tree-to-ctx S) (COT-to-Ctx ΓS) (label-to-sub L)

ap-phere-Ty (TySing x) = stm-to-term-Ty x
ap-phere-Ty (TyJoin x Lty Mty) = stm-to-term-Ty x

stm-to-term-Ty (TySConv aTy [ x ]) = TyConv (stm-to-term-Ty aTy) x
stm-to-term-Ty (TySPath P) = path-to-term-Ty P
stm-to-term-Ty (TySExt {As = As} {T = T} aTy) = TyConv (apply-sub-tm-typing (suspTmTy (stm-to-term-Ty aTy)) (connect-susp-inc-left-Ty (tree-to-ctx T))) (reflexive≈ty (begin
  < suspTy (sty-to-type As) [ connect-susp-inc-left _ _ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (susp-sty-to-type As) refl≃s ⟩
  < sty-to-type (susp-sty As) [ connect-susp-inc-left _ (tree-size T) ]ty >ty
    ≈˘⟨ sty-sub-prop (susp-sty As) (connect-susp-inc-left _ (tree-size T)) ⟩
  < sty-to-type (sty-sub (susp-sty As) (connect-susp-inc-left _ (tree-size T))) >ty
    ≈⟨ map-sty-pext-prop As .get  ⟩
  < sty-to-type (map-sty-pext As) >ty ∎))
  where
    open Reasoning ty-setoid
stm-to-term-Ty (TySShift {As = As} {S = S} aTy) = TyConv (apply-sub-tm-typing (stm-to-term-Ty aTy) (connect-susp-inc-right-Ty (tree-to-ctx S))) (reflexive≈ty (begin
  < sty-to-type As [ connect-susp-inc-right _ _ ]ty >ty
    ≈˘⟨ sty-sub-prop As (connect-susp-inc-right (tree-size S) _) ⟩
  < sty-to-type (sty-sub As (connect-susp-inc-right (tree-size S) _)) >ty
    ≈˘⟨ map-sty-pshift-prop As .get ⟩
  < sty-to-type (map-sty-pshift As) >ty ∎))
  where
    open Reasoning ty-setoid
stm-to-term-Ty (TySCoh S {As = As} {L = L} AsTy LTy LTyTy b sc) = TyConv (apply-sub-tm-typing (TyCoh ⦃ tree-to-pd S ⦄ (sty-to-type-Ty AsTy) id-Ty b (supp-condition-compat b S As sc)) (label-to-sub-Ty LTy LTyTy)) (reflexive≈ty (begin
  < sty-to-type As [ idSub ]ty [ label-to-sub L ]ty >ty
    ≈⟨ sub-action-≃-ty (id-on-ty (sty-to-type As)) refl≃s ⟩
  < sty-to-type As [ label-to-sub L ]ty >ty
    ≈⟨ label-to-sub-sty L As ⟩
  < sty-to-type (label-on-sty As L) >ty ∎))
  where
    open Reasoning ty-setoid
stm-to-term-Ty (TySOther tty) = tty

sty-to-type-Ty TySStar = TyStar
sty-to-type-Ty (TySArr aTy AsTy bTy) = TyArr (stm-to-term-Ty aTy) (sty-to-type-Ty AsTy) (stm-to-term-Ty bTy)

label-to-sub-Ty′ (TySing x) LTyTy = TyExt (TyNull LTyTy) (stm-to-term-Ty x)
label-to-sub-Ty′ (TyJoin {L = L} x LTy MTy) LTyTy = sub-from-connect-Ty (unrestrictTy (label-to-sub-Ty′ LTy (TyArr (stm-to-term-Ty x) LTyTy (ap-phere-Ty MTy)))) getSndTy (label-to-sub-Ty′ MTy LTyTy) (reflexive≈tm (label-to-sub-lem L))

label-to-sub-Ty LTy LTyTy = label-to-sub-Ty′ LTy (sty-to-type-Ty LTyTy)

map-sty-pext-Ty : Typing-STy (incTree S) As → Typing-STy (incTree (Join S T)) (map-sty-pext As)
map-sty-pext-Ty TySStar = TySArr (TySPath PHere) TySStar (TySShift (TySPath PHere))
map-sty-pext-Ty (TySArr aty AsTy bty) = TySArr (TySExt aty) (map-sty-pext-Ty AsTy) (TySExt bty)

map-pext-Ty : Typing-Label (incTree S) Lt → Typing-Label (incTree (Join S T)) (map-pext Lt)
map-pext-Ty (TySing x) = TySing (TySExt x)
map-pext-Ty (TyJoin x Lty Mty) = TyJoin (TySExt x) (map-pext-Ty Lty) (map-pext-Ty Mty)

map-sty-pshift-Ty : Typing-STy (incTree T) As → Typing-STy (incTree (Join S T)) (map-sty-pshift As)
map-sty-pshift-Ty TySStar = TySStar
map-sty-pshift-Ty (TySArr aty AsTy bty) = TySArr (TySShift aty) (map-sty-pshift-Ty AsTy) (TySShift bty)

map-pshift-Ty : Typing-Label (incTree T) Lt → Typing-Label (incTree (Join S T)) (map-pshift Lt)
map-pshift-Ty (TySing x) = TySing (TySShift x)
map-pshift-Ty (TyJoin x Lty Mty) = TyJoin (TySShift x) (map-pshift-Ty Lty) (map-pshift-Ty Mty)

lift-stm-Ty : Typing-STm (incCtx Γ) a As → Typing-STm (incCtx (Γ , A)) (lift-stm a) (lift-sty As)
lift-sty-Ty : Typing-STy (incCtx Γ) As → Typing-STy (incCtx (Γ , A)) (lift-sty As)
lift-label-Ty : Typing-Label (incCtx Γ) Lt → Typing-Label (incCtx (Γ , A)) (lift-label Lt)

lift-sty-equality : As ≈[ incCtx Γ ]sty Bs → lift-sty As ≈[ incCtx (Γ , A) ]sty lift-sty Bs
lift-sty-equality {As = As} {Bs = Bs} [ x ] .get = begin
  sty-to-type (lift-sty As)
    ≈⟨ reflexive≈ty (lift-sty-to-type As) ⟩
  liftType (sty-to-type As)
    ≈⟨ lift-ty-equality x ⟩
  liftType (sty-to-type Bs)
    ≈˘⟨ reflexive≈ty (lift-sty-to-type Bs) ⟩
  sty-to-type (lift-sty Bs) ∎
  where
    open Reasoning (ty-setoid-≈ _)

lift-stm-Ty (TySConv aty x) = TySConv (lift-stm-Ty aty) (lift-sty-equality x)
lift-stm-Ty (TySCoh S {As} {L} Asty Lty LTyty b sc) = TySConv (TySCoh S Asty (lift-label-Ty Lty) (lift-sty-Ty LTyty) b sc) (reflexive≈sty (label-on-sty-lift As L))
lift-stm-Ty (TySOther {As = As} x) = TySOther (TyConv (lift-tm-typing x) (reflexive≈ty (sym≃ty (lift-sty-to-type As))))

lift-sty-Ty TySStar = TySStar
lift-sty-Ty (TySArr aty Asty bty) = TySArr (lift-stm-Ty aty) (lift-sty-Ty Asty) (lift-stm-Ty bty)

lift-label-Ty (TySing x) = TySing (lift-stm-Ty x)
lift-label-Ty (TyJoin x Lty Mty) = TyJoin (lift-stm-Ty x) (lift-label-Ty Lty) (lift-label-Ty Mty)
-}
Typing-STm : {X : MaybeTree m} → (Γ : Ctx m) → STm X → STy X → Set
Typing-STy : {X : MaybeTree m} → (Γ : Ctx m) → STy X → Set
data Typing-Label : {X : MaybeTree m} → (Γ : Ctx m) → Label-WT X S → Set

Typing-STm Γ = Wrap (λ a As → Typing-Tm Γ (stm-to-term a) (sty-to-type As))

Typing-STy Γ = Wrap (λ As → Typing-Ty Γ (sty-to-type As))

data Typing-Label where
  TySing : {L : Label-WT X Sing} → Typing-STm Γ (ap L PHere) (lty L) → Typing-Label Γ L
  TyJoin : {L : Label-WT X (Join S T)}
         → Typing-STm Γ (ap L PHere) (lty L)
         → Typing-Label Γ (label₁ L)
         → Typing-Label Γ (label₂ L)
         → Typing-Label Γ L

TySStar : Typing-STy Γ (S⋆ {X = X})
TySStar .get = TyStar

TySConv : Typing-STm Γ a As → As ≈[ Γ ]sty Bs → Typing-STm Γ a Bs
TySConv [ aty ] [ p ] = [ TyConv aty p ]

TySArr : Typing-STm Γ a As → Typing-STy Γ As → Typing-STm Γ b As → Typing-STy Γ (SArr a As b)
TySArr [ aty ] [ Asty ] [ bty ] .get = TyArr aty Asty bty

TySArr-proj₁ : Typing-STy Γ (SArr a As b) → Typing-STm Γ a As
TySArr-proj₁ [ TyArr x _ _ ] = [ x ]

TySArr-proj₂ : Typing-STy Γ As → Typing-STy Γ (sty-base As)
TySArr-proj₂ {As = S⋆} [ TyStar ] = TySStar
TySArr-proj₂ {As = SArr _ _ _} [ TyArr _ x _ ] = [ x ]

TySArr-proj₃ : Typing-STy Γ (SArr a As b) → Typing-STm Γ b As
TySArr-proj₃ [ TyArr _ _ x ] = [ x ]

ap-phere-Ty : {L : Label-WT X S} → Typing-Label Γ L → Typing-STm Γ (ap L PHere) (lty L)
ap-phere-Ty (TySing x) = x
ap-phere-Ty (TyJoin x Lty Mty) = x

transport-stm-typing : Typing-STm Γ a As → a ≃stm b → As ≃sty Bs → Typing-STm Γ b Bs
transport-stm-typing [ aty ] [ p ] [ q ] = [ transport-typing-full aty p q ]

transport-label-typing : {L M : Label-WT X S} → Typing-Label Γ L → proj₁ L ≃l proj₁ M → proj₂ L ≃sty proj₂ M → Typing-Label Γ M
transport-label-typing (TySing x) [ p ] q = TySing (transport-stm-typing x (p PHere) q)
transport-label-typing (TyJoin x Lty Lty′) [ p ] q
  = TyJoin (transport-stm-typing x (p PHere) q)
           (transport-label-typing Lty [ p ∘ PExt ] (≃SArr (p PHere) q (p (PShift PHere))))
           (transport-label-typing Lty′ [ p ∘ PShift ] q)

label-typing-conv : Typing-Label Γ (L ,, As) → As ≈[ Γ ]sty Bs → Typing-Label Γ (L ,, Bs)
label-typing-conv (TySing x) p = TySing (TySConv x p)
label-typing-conv (TyJoin x LTy LTy′) p = TyJoin (TySConv x p) (label-typing-conv LTy (≈SArr refl≈stm p refl≈stm)) (label-typing-conv LTy′ p)

{-
ap-pphere-Ty : Typing-Label ΓS L → Typing-Path ΓS (ap L PPHere) (lty L)
ap-pphere-Ty (TySing xty) = xty
ap-pphere-Ty (TyJoin xty Lty Mty) = xty

apt-pphere-Ty : Typing-Label ΓS L → Typing-Tm (COT-to-Ctx ΓS) (apt L PPHere) (lty L)
apt-pphere-Ty Lty = path-to-term-Ty (ap-pphere-Ty Lty)

label₁-Ty : Typing-Label ΓS L → Typing-Label ΓS (label₁ L)
label₁-Ty (TyJoin x Lty Mty) = Lty

label₂-Ty : Typing-Label ΓS L → Typing-Label ΓS (label₂ L)
label₂-Ty (TyJoin x Lty Mty) = Mty

convert-type-Ty : Typing-Label ΓS L
                → lty L ≈[ COT-to-Ctx ΓS ]ty B
                → Typing-Label ΓS (convert-type L B)
convert-type-Ty (TySing x) p = TySing (TyPConv x p)
convert-type-Ty (TyJoin x Lty Mty) p = TyJoin (TyPConv x p) (convert-type-Ty Lty (Arr≈ refl≈tm p refl≈tm)) (convert-type-Ty Mty p)

label-to-sub-Ty : Typing-Label ΓS L
                → Typing-Ty (COT-to-Ctx ΓS) (lty L)
                → Typing-Sub (tree-to-ctx (ltree L)) (COT-to-Ctx ΓS) (label-to-sub L)
label-to-sub-Ty (TySing xty) Aty = TyExt (TyNull Aty) (path-to-term-Ty xty)
label-to-sub-Ty {L = L} (TyJoin xty Lty Mty) Aty
  = sub-from-connect-Ty (unrestrictTy (label-to-sub-Ty Lty (TyArr (path-to-term-Ty xty) Aty (apt-pphere-Ty Mty))))
                        getSndTy
                        (label-to-sub-Ty Mty Aty)
                        (reflexive≈tm (label-to-sub-lem L))

map-pext-Ty : Typing-Label (incTree S) L
            → Typing-Label (incTree (Join S T)) (map-pext L)
map-pext-Ty (TySing xty) = TySing (TyExt xty)
map-pext-Ty (TyJoin xty Lty Mty) = TyJoin (TyExt xty) (map-pext-Ty Lty) (map-pext-Ty Mty)

map-pshift-Ty : Typing-Label (incTree T) L
              → Typing-Label (incTree (Join S T)) (map-pshift L)
map-pshift-Ty (TySing xty) = TySing (TyShift xty)
map-pshift-Ty (TyJoin xty Lty Mty) = TyJoin (TyShift xty) (map-pshift-Ty Lty) (map-pshift-Ty Mty)

id-label-Ty : (S : Tree n) → Typing-Label (incTree S) (id-label S)
id-label-Ty Sing = TySing TyHere
id-label-Ty (Join S₁ S₂) = TyJoin TyHere
                                  (convert-type-Ty (map-pext-Ty (id-label-Ty S₁)) (reflexive≈ty (Arr≃ (connect-inc-left-fst-var getSnd (tree-size S₂))
                                                                                                      refl≃ty
                                                                                                      (connect-inc-fst-var getSnd (tree-size S₂)))))
                                  (map-pshift-Ty (id-label-Ty S₂))

label-sub-Ty : Typing-Label ΓS L
                  → Typing-Sub (COT-to-Ctx ΓS) (COT-to-Ctx ΔT) σ
                  → Typing-Label ΔT (label-sub L (COT-to-MT ΔT) σ)
label-sub-Ty (TySing xty) σty = TySing (TyOther (apply-sub-tm-typing (path-to-term-Ty xty) σty))
label-sub-Ty (TyJoin xty Lty Mty) σty = TyJoin (TyOther (apply-sub-tm-typing (path-to-term-Ty xty) σty)) (label-sub-Ty Lty σty) (label-sub-Ty Mty σty)

to-label-Ty : (S : Tree n) → (ΓS : CtxOrTree m) → Typing-Sub (tree-to-ctx S) (COT-to-Ctx ΓS) σ → Typing-Label ΓS (to-label S σ (COT-to-MT ΓS))
to-label-Ty S ΓS σty = label-sub-Ty (id-label-Ty S) σty

{-
transport-label-typing : Typing-Label ΓS L A → L ≃l M → A ≈[ COT-to-Ctx ΓS ]ty B → Typing-Label ΓS M B
transport-label-typing (TySing x) (LSing≃ y) q = TySing (transport-path-typing x y q)
transport-label-typing (TyJoin x Lty Mty) (LJoin≃ y p p′) q
  = TyJoin (transport-path-typing x y q)
           (transport-label-typing Lty p (Arr≈ (reflexive≈tm (path-to-term-≃ y)) q (reflexive≈tm (path-to-term-≃ (first-label-≃ p′)))))
           (transport-label-typing Mty p′ q)

label-eq-conv : (L : Label X S) → A ≈[ Γ ]ty B → label-to-sub L A ≈[ Γ ]s label-to-sub L B
label-eq-conv (LSing x) p = Ext≈ (Null≈ p) refl≈tm
label-eq-conv (LJoin x L M) p = sub-from-connect-≈ (unrestrictEq (label-eq-conv L (Arr≈ refl≈tm p refl≈tm))) (label-eq-conv M p)
-}
connect-label-Ty : (Lty : Typing-Label ΓS L)
                 → (Mty : Typing-Label ΓS M)
                 → apt L (last-path S) ≈[ COT-to-Ctx ΓS ]tm apt M PPHere
                 → Typing-Label ΓS (connect-label L M)
connect-label-Ty (TySing x) (TySing y) p = TySing x
connect-label-Ty (TySing x) (TyJoin y Mty Mty′) p = TyJoin x (convert-type-Ty Mty (Arr≈ (sym≈tm p) refl≈ty refl≈tm)) Mty′
connect-label-Ty {L = L} {M = M} (TyJoin x Lty Lty′) Mty p = TyJoin x (convert-type-Ty Lty (reflexive≈ty (Arr≃ refl≃tm refl≃ty (sym≃tm (path-to-term-≃ (connect-label-pphere (label₂ L) M)))))) (connect-label-Ty Lty′ Mty p)

connect-tree-inc-left-Ty : (S : Tree n)
                         → (T : Tree m)
                         → Typing-Label (incTree (connect-tree S T)) (connect-tree-inc-left S T)
connect-tree-inc-left-Ty Sing T = TySing TyHere
connect-tree-inc-left-Ty (Join S₁ S₂) T
  = TyJoin TyHere (convert-type-Ty (map-pext-Ty (id-label-Ty S₁)) (reflexive≈ty (Arr≃ (connect-inc-left-fst-var getSnd (connect-tree-length S₂ T))
                                                                                      refl≃ty
                                                                                      lem)))
                  (map-pshift-Ty (connect-tree-inc-left-Ty S₂ T))
    where
      open Reasoning tm-setoid
      lem : getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm
          ≃tm apt (connect-tree-inc-left (Join S₁ S₂) T) (PPShift PPHere)
      lem = begin
        < getSnd [ connect-susp-inc-left (tree-size S₁) (tree-size (connect-tree S₂ T)) ]tm >tm
          ≈⟨ connect-inc-fst-var getSnd (connect-tree-length S₂ T) ⟩
        < Var (fromℕ (connect-tree-length S₂ T)) [ connect-susp-inc-right (tree-size S₁) (connect-tree-length S₂ T) ]tm >tm
          ≈˘⟨ sub-action-≃-tm (path-to-term-≃ (connect-tree-inc-left-pphere S₂ T)) refl≃s ⟩
        < apt (connect-tree-inc-left S₂ T) PPHere
          [ connect-susp-inc-right (tree-size S₁) (connect-tree-length S₂ T) ]tm >tm ∎

connect-tree-inc-right-Ty : (S : Tree n)
                          → (T : Tree m)
                          → Typing-Label (incTree (connect-tree S T)) (connect-tree-inc-right S T)
connect-tree-inc-right-Ty Sing T = id-label-Ty T
connect-tree-inc-right-Ty (Join S₁ S₂) T = map-pshift-Ty (connect-tree-inc-right-Ty S₂ T)

{-
-- label-index-Ty : Typing-Label ΓS L A
--                → Typing-Ty (COT-to-Ctx ΓS) A
--                → Typing-Path (incTree (label-to-tree L)) P B
--                → Typing-Path ΓS (L ‼< A > P) (B [ label-to-sub L A ]ty)
-- label-index-Ty Lty Aty (TyPConv Pty p) = TyPConv (label-index-Ty Lty Aty Pty) (apply-sub-ty-eq (label-typing-to-sub Lty Aty) p)
-- label-index-Ty Lty Aty (TyOther tty) = TyOther (apply-sub-tm-typing tty (label-typing-to-sub Lty Aty))
-- label-index-Ty Lty Aty TyHere = first-label-Ty Lty
-- label-index-Ty {A = A} (TyJoin {P = P} {L = L} {M = M} x Lty Mty) Aty (TyExt {A = B} Pty)
--   = TyPConv (label-index-Ty Lty (TyArr (path-to-term-Ty x) Aty (first-label-term-Ty Mty)) Pty) (reflexive≈ty lem)
--   where
--     open Reasoning ty-setoid

--     lem : B [ label-to-sub L (path-to-term P ─⟨ A ⟩⟶ path-to-term (first-label M)) ]ty
--           ≃ty suspTy B [ connect-susp-inc-left _ _ ]ty
--                        [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A) ]ty
--     lem = begin
--       < B [ label-to-sub L (path-to-term P ─⟨ A ⟩⟶ path-to-term (first-label M)) ]ty >ty
--         ≈˘⟨ unrestrict-comp-ty B (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M)) ⟩
--       < suspTy B [ unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M)) ]ty >ty
--         ≈˘⟨ sub-action-≃-ty refl≃ty (sub-from-connect-inc-left (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) getSnd (label-to-sub M A)) ⟩
--       < suspTy B [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A)
--                  ∘ connect-susp-inc-left _ _ ]ty >ty
--         ≈⟨ assoc-ty _ _ (suspTy B) ⟩
--       < suspTy B [ connect-susp-inc-left _ _ ]ty
--                  [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A) ]ty >ty ∎

-- label-index-Ty {A = A} (TyJoin {P = P} {L = L} {M = M} x Lty Mty) Aty (TyShift {A = B} Pty)
--   = TyPConv (label-index-Ty Mty Aty Pty) (reflexive≈ty lem)
--   where
--     open Reasoning ty-setoid

--     lem : (B [ label-to-sub M A ]ty) ≃ty
--           B [ connect-susp-inc-right _ _ ]ty
--             [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A) ]ty
--     lem = begin
--       < B [ label-to-sub M A ]ty >ty
--         ≈˘⟨ sub-action-≃-ty refl≃ty (sub-from-connect-inc-right (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) getSnd (label-to-sub M A) (trans≃tm (unrestrict-snd (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (first-label-prop M A))) ⟩
--       < B [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A)
--           ∘ connect-susp-inc-right _ _ ]ty >ty
--         ≈⟨ assoc-ty _ _ B ⟩
--       < B [ connect-susp-inc-right _ _ ]ty
--           [ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term M))) (label-to-sub M A) ]ty >ty ∎
-}

extend-Ty : Typing-Path (incTree S) P A → Typing-Label ΓS L → Typing-Ty (COT-to-Ctx ΓS) (lty L) → Typing-Path ΓS (P >>= L) (A [ label-to-sub L ]ty)
extend-Ty (TyPConv Pty x) Lty Aty = TyPConv (extend-Ty Pty Lty Aty) (apply-sub-ty-eq (label-to-sub-Ty Lty Aty) x)
extend-Ty TyHere Lty Aty = ap-pphere-Ty Lty
extend-Ty {L = L} (TyExt {A = A} Pty) Lty Aty = TyPConv (extend-Ty Pty (label₁-Ty Lty) (TyArr (apt-pphere-Ty Lty) Aty (apt-pphere-Ty (label₂-Ty Lty)))) (reflexive≈ty lem)
  where
    open Reasoning ty-setoid
    lem : A [ label-to-sub (label₁ L) ]ty
      ≃ty suspTy A [ connect-susp-inc-left _ _ ]ty
                   [ label-to-sub L ]ty
    lem = begin
      < A [ label-to-sub (label₁ L) ]ty >ty
        ≈˘⟨ unrestrict-comp-ty A (label-to-sub (label₁ L)) ⟩
      < suspTy A [ unrestrict (label-to-sub (label₁ L)) ]ty >ty
        ≈˘⟨ sub-action-≃-ty (refl≃ty {A = suspTy A}) (sub-from-connect-inc-left (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L))) ⟩
      < suspTy A [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))
                 ∘ connect-susp-inc-left _ _ ]ty >ty
        ≈⟨ assoc-ty _ _ (suspTy A) ⟩
      < suspTy A [ connect-susp-inc-left _ _ ]ty
                 [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]ty >ty ∎
extend-Ty {L = L} (TyShift {A = A} Pty) Lty Aty = TyPConv (extend-Ty Pty (label₂-Ty Lty) Aty) (reflexive≈ty lem)
  where
    open Reasoning ty-setoid
    lem : A [ label-to-sub (label₂ L) ]ty
      ≃ty A [ connect-susp-inc-right _ _ ]ty
            [ label-to-sub L ]ty
    lem = begin
      < A [ label-to-sub (label₂ L) ]ty >ty
        ≈˘⟨ sub-action-≃-ty (refl≃ty {A = A}) (sub-from-connect-inc-right (unrestrict (label-to-sub (label₁ L))) getSnd (label-to-sub (label₂ L)) (label-to-sub-lem L)) ⟩
      < A [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L))
          ∘ connect-susp-inc-right _ _ ]ty >ty
        ≈⟨ assoc-ty _ _ A ⟩
      < A [ connect-susp-inc-right _ _ ]ty
          [ sub-from-connect (unrestrict (label-to-sub (label₁ L))) (label-to-sub (label₂ L)) ]ty >ty ∎
extend-Ty (TyOther x) Lty Aty = TyOther (apply-sub-tm-typing x (label-to-sub-Ty Lty Aty))

label-comp-Ty : Typing-Label (incTree T) L
              → Typing-Label ΓS M
              → Typing-Ty (COT-to-Ctx ΓS) (lty M)
              → Typing-Label ΓS (label-comp L M)
label-comp-Ty (TySing x) Mty Aty = TySing (extend-Ty x Mty Aty)
label-comp-Ty {L = L} {M = M} (TyJoin x Lty Lty′) Mty Aty
  = TyJoin (extend-Ty x Mty Aty)
           (convert-type-Ty (label-comp-Ty Lty Mty Aty) (reflexive≈ty (Arr≃ (label-to-sub-path M (ap L PPHere)) refl≃ty (label-to-sub-path M (ap L (PPShift PPHere))))))
           (label-comp-Ty Lty′ Mty Aty)


label-between-connect-trees-Ty : Typing-Label (incTree S′) L
                               → Typing-Label (incTree T′) M
                               → apt L (last-path S) ≈[ tree-to-ctx S′ ]tm tree-last-var S′
                               → apt M PPHere ≈[ tree-to-ctx T′ ]tm Var (fromℕ (tree-size T′))
                               → Typing-Label (incTree (connect-tree S′ T′)) (label-between-connect-trees L M)
label-between-connect-trees-Ty {S′ = S′} {S = S} {L = L} {T′ = T′} {M = M} Lty Mty p q
  = connect-label-Ty (label-comp-Ty Lty (connect-tree-inc-left-Ty _ _) TyStar)
                     (label-comp-Ty Mty (connect-tree-inc-right-Ty _ _) TyStar)
                     lem
  where
    open Reasoning (tm-setoid-≈ _)

    lem : path-to-term (ap L (last-path S) >>= connect-tree-inc-left S′ T′)
        ≈[ tree-to-ctx (connect-tree S′ T′) ]tm
          path-to-term (ap M ⟦ PHere ⟧ >>= connect-tree-inc-right S′ T′)
    lem = begin
      path-to-term (ap L (last-path S) >>= connect-tree-inc-left S′ T′)
        ≈˘⟨ reflexive≈tm (label-to-sub-path (connect-tree-inc-left S′ T′) (ap L (last-path S))) ⟩
      apt L (last-path S) [ label-to-sub (connect-tree-inc-left S′ T′) ]tm
        ≈⟨ apply-sub-tm-eq (label-to-sub-Ty (connect-tree-inc-left-Ty S′ T′) TyStar) p ⟩
      tree-last-var S′ [ label-to-sub (connect-tree-inc-left S′ T′) ]tm
        ≈˘⟨ reflexive≈tm (sub-action-≃-tm (last-path-to-term S′) refl≃s) ⟩
      path-to-term (carrier (last-path S′)) [ label-to-sub (connect-tree-inc-left S′ T′) ]tm
        ≈⟨ reflexive≈tm (label-to-sub-ppath (connect-tree-inc-left S′ T′) (last-path S′)) ⟩
      apt (connect-tree-inc-left S′ T′) (last-path S′)
        ≈⟨ reflexive≈tm (path-to-term-≃ (connect-tree-inc-pphere S′ T′)) ⟩
      apt (connect-tree-inc-right S′ T′) PPHere
        ≈˘⟨ reflexive≈tm (label-to-sub-ppath (connect-tree-inc-right S′ T′) PPHere) ⟩
      Var (fromℕ (tree-size T′)) [ label-to-sub (connect-tree-inc-right S′ T′) ]tm
        ≈˘⟨ apply-sub-tm-eq (label-to-sub-Ty (connect-tree-inc-right-Ty S′ T′) TyStar) q ⟩
      apt M PPHere [ label-to-sub (connect-tree-inc-right S′ T′) ]tm
        ≈⟨ reflexive≈tm (label-to-sub-path (connect-tree-inc-right S′ T′) (ap M PPHere)) ⟩
      path-to-term (ap M PPHere >>= connect-tree-inc-right S′ T′) ∎

label-between-joins-Ty : Typing-Label (incTree S′) L
                       → Typing-Label (incTree T′) M
                       → apt M PPHere ≈[ tree-to-ctx T′ ]tm Var (fromℕ (tree-size T′))
                       → Typing-Label (incTree (Join S′ T′)) (label-between-joins L M)
label-between-joins-Ty {S′ = S′} {L = L} {T′ = T′} {M = M} Lty Mty p
  = TyJoin TyHere (convert-type-Ty (map-pext-Ty Lty) (Arr≈ (reflexive≈tm (connect-inc-left-fst-var getSnd _)) refl≈ty lem)) (map-pshift-Ty Mty)
  where
    open Reasoning (tm-setoid-≈ _)
    lem : (getSnd [ connect-susp-inc-left (tree-size S′) (tree-size T′) ]tm) ≈[ _ ]tm apt (label-between-joins L M) (PPShift PPHere)
    lem = begin
      getSnd [ connect-susp-inc-left (tree-size S′) (tree-size T′) ]tm
        ≈⟨ reflexive≈tm (connect-inc-fst-var getSnd (tree-size T′)) ⟩
      Var (fromℕ _) [ connect-susp-inc-right (tree-size S′) (tree-size T′) ]tm
        ≈˘⟨ apply-sub-tm-eq (connect-susp-inc-right-Ty (tree-to-ctx S′)) p ⟩
      apt M ⟦ PHere ⟧ [ connect-susp-inc-right (tree-size S′) (tree-size T′) ]tm ∎

replace-label-Ty : Typing-Label ΓS L
                 → Typing-Path ΓS P (lty L)
                 → apt L PPHere ≈[ COT-to-Ctx ΓS ]tm path-to-term P
                 → Typing-Label ΓS (replace-label L P)
replace-label-Ty (TySing x) Pty p = TySing Pty
replace-label-Ty (TyJoin x Lty Mty) Pty p = TyJoin Pty (convert-type-Ty Lty (Arr≈ p refl≈ty refl≈tm)) Mty

label-to-sub-convert-type : (L : Label (COT-to-MT ΓS) S A) → B ≈[ COT-to-Ctx ΓS ]ty A → label-to-sub (convert-type L B) ≈[ COT-to-Ctx ΓS ]s label-to-sub L
label-to-sub-convert-type {S = Sing} L p = Ext≈ (Null≈ p) refl≈tm
label-to-sub-convert-type {S = Join S T} L p = sub-from-connect-≈ (unrestrictEq (label-to-sub-convert-type (label₁ L) (Arr≈ refl≈tm p refl≈tm))) (label-to-sub-convert-type (label₂ L) p)

{-

data _≃Ml<_>_ : Label X S → Bool → Label Y T → Set where
  MlSingf : LSing P ≃Ml< false > LSing Q
  MlSingt : path-to-term P ≃tm path-to-term Q → LSing P ≃Ml< true > LSing Q
  MlJoin : {b : Bool} → L ≃Ml< true > L′ → M ≃Ml< false > M′ → LJoin P L M ≃Ml< b > LJoin Q L′ M′

max-eq-to-eq : {L : Label (COT-to-MT ΓS) S}
             → {M : Label (COT-to-MT ΔT) T}
             → L ≃Ml< true > M
             → Typing-Label ΓS L A
             → Typing-Label ΔT M B
             → (p : COT-to-Ctx ΓS ≃c COT-to-Ctx ΔT)
             → idSub≃ p ∘ label-to-sub L A ≈[ COT-to-Ctx ΔT ]s label-to-sub M B
max-eq-to-eq (MlSingt {P = P} x) (TySing Pty) (TySing Qty) p = let
  eq = trans≃tm (idSub≃-on-tm p (path-to-term P)) x
  in Ext≈ (Null≈ (Ty-unique-≃ eq (apply-sub-tm-typing (path-to-term-Ty Pty) (idSub≃-Ty p)) (path-to-term-Ty Qty))) (reflexive≈tm eq)
max-eq-to-eq {A = A} {B = B} (MlJoin q MlSingf) (TyJoin {P = P} {L = L} Pty Lty (TySing {P = P′} Pty′)) (TyJoin {P = Q} {L = M} Qty Mty (TySing {P = Q′} QTy′)) p = begin
  < idSub≃ p ∘
       unrestrict
       (label-to-sub L
        (path-to-term P ─⟨ A ⟩⟶ first-label-term (LSing P′))) >s′
    ≈˘⟨ reflexive≈s (unrestrict-comp-higher (idSub≃ p) (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ path-to-term P′))) ⟩
  < unrestrict (idSub≃ p ∘ label-to-sub L (path-to-term P ─⟨ A ⟩⟶ path-to-term P′)) >s′
    ≈⟨ unrestrictEq (max-eq-to-eq q Lty Mty p) ⟩
  < unrestrict (label-to-sub M (path-to-term Q ─⟨ B ⟩⟶ first-label-term (LSing Q′))) >s′ ∎
  where
    open Reasoning (sub-setoid-≈ _)
max-eq-to-eq {A = A} {B = B} (MlJoin q q′@(MlJoin a b)) (TyJoin {P = P} {L = L} {M = L′} Pty Lty Lty′) (TyJoin {P = Q} {L = M} {M = M′} Qty Mty Mty′) p = begin
  < idSub≃ p
  ∘ sub-from-connect (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′)))
                     (label-to-sub L′ A) >s′
    ≈⟨ reflexive≈s (sub-from-connect-sub (unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′))) (label-to-sub L′ A) (idSub≃ p)) ⟩
  < sub-from-connect (idSub≃ p ∘ unrestrict (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′)))
                     (idSub≃ p ∘ label-to-sub L′ A) >s′
    ≈˘⟨ reflexive≈s (sub-from-connect-≃ (unrestrict-comp-higher (idSub≃ p) (label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′))) refl≃s) ⟩
  < sub-from-connect
    (unrestrict (idSub≃ p ∘ label-to-sub L (path-to-term P ─⟨ A ⟩⟶ first-label-term L′)))
    (idSub≃ p ∘ label-to-sub L′ A) >s′
    ≈⟨ sub-from-connect-≈ (unrestrictEq (max-eq-to-eq q Lty Mty p)) (max-eq-to-eq (MlJoin a b) Lty′ Mty′ p) ⟩
  < sub-from-connect
    (unrestrict (label-to-sub M (path-to-term Q ─⟨ B ⟩⟶ path-to-term (first-label M′))))
    (label-to-sub M′ B) >s′ ∎
  where
    open Reasoning (sub-setoid-≈ _)

-- connect-label-inc-left : (L : Label X S)
--                        → (M : Label X T)
--                        → label-comp (connect-tree-inc-left S T) (connect-label L M) ≃Ml< true > L
-- connect-label-inc-left (LSing P) M = MlSingt (replace-first-label M P)
-- connect-label-inc-left (LJoin P L L′) M = {!!}
-}
-}

unrestrict-label-Ty : {L : Label-WT X S } → Typing-Label Γ L → Typing-STy Γ (lty L) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → Typing-Label Γ (unrestrict-label L ,, sty-base (lty L))
unrestrict-label-Ty {L = L ,, SArr s As t} LTy AsTy = TyJoin (TySArr-proj₁ AsTy) LTy (TySing (TySArr-proj₃ AsTy))
