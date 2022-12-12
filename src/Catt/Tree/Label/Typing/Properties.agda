open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Label.Typing.Properties (index : ℕ)
                                         (rule : Fin index → Rule)
                                         (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                         (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                         (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Support
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Path.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Tree.Properties
open import Catt.Tree.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Suspension
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing index rule lift-rule
open import Catt.Tree.Label.Typing index rule

≈SExt : a ≈[ incTree S ]stm b → SExt a ≈[ incTree (Join S T) ]stm SExt b
≈SExt {T = T} [ p ] = [ (apply-sub-tm-eq (connect-susp-inc-left-Ty (tree-to-ctx T)) (suspTmEq p)) ]

≈SShift : a ≈[ incTree T ]stm b → SShift a ≈[ incTree (Join S T) ]stm SShift b
≈SShift {S = S} [ q ] = [ (apply-sub-tm-eq (connect-susp-inc-right-Ty (tree-to-ctx S)) q) ]

≈SPath : P ≃p Q → SPath P ≃stm SPath Q
≈SPath p = [ path-to-term-≃ p ]

label-to-sub-Ty : {L : Label-WT (COT-to-MT ΓS) S} → Typing-Label ΓS L → Typing-STy ΓS (lty L) → Typing-Sub (tree-to-ctx S) (COT-to-Ctx ΓS) (label-to-sub L)
label-to-sub-Ty (TySing [ x ]) [ Aty ] = TyExt (TyNull Aty) x
label-to-sub-Ty {L = L} (TyJoin x Lty Mty) Aty = sub-from-connect-Ty (unrestrictTy (label-to-sub-Ty Lty (TySArr x Aty (ap-phere-Ty Mty)))) getSndTy (label-to-sub-Ty Mty Aty) (reflexive≈tm (label-to-sub-lem L) )

TySPath : (P : Path S) → Typing-STm (incTree S) (SPath P) (getPathType P)
TySPath P .get = path-to-term-Ty P

TySExt : Typing-STm (incTree S) a As → Typing-STm (incTree (Join S T)) (SExt a) (map-sty-pext As)
TySExt {As = As} {T = T} [ aty ] .get = TyConv (apply-sub-tm-typing (suspTmTy aty) (connect-susp-inc-left-Ty (tree-to-ctx T))) (reflexive≈ty (begin
  < suspTy (sty-to-type As) [ connect-susp-inc-left _ _ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (susp-sty-to-type As) refl≃s ⟩
  < sty-to-type (susp-sty As) [ connect-susp-inc-left _ (tree-size T) ]ty >ty
    ≈˘⟨ sty-sub-prop (susp-sty As) (connect-susp-inc-left _ (tree-size T)) ⟩
  < sty-to-type (sty-sub (susp-sty As) (connect-susp-inc-left _ (tree-size T))) >ty
    ≈⟨ map-sty-pext-prop As .get  ⟩
  < sty-to-type (map-sty-pext As) >ty ∎))
  where
    open Reasoning ty-setoid

TySShift : Typing-STm (incTree T) a As → Typing-STm (incTree (Join S T)) (SShift a) (map-sty-pshift As)
TySShift {As = As} {S = S} [ aty ] .get = TyConv (apply-sub-tm-typing aty (connect-susp-inc-right-Ty (tree-to-ctx S))) (reflexive≈ty (begin
  < sty-to-type As [ connect-susp-inc-right _ _ ]ty >ty
    ≈˘⟨ sty-sub-prop As (connect-susp-inc-right (tree-size S) _) ⟩
  < sty-to-type (sty-sub As (connect-susp-inc-right (tree-size S) _)) >ty
    ≈˘⟨ map-sty-pshift-prop As .get ⟩
  < sty-to-type (map-sty-pshift As) >ty ∎))
  where
    open Reasoning ty-setoid

TySCoh : (S : Tree n) → {As : STy (someTree S)} → {L : Label-WT (COT-to-MT ΓS) S}
         → Typing-STy (incTree S) As
         → Typing-Label ΓS L
         → Typing-STy ΓS (lty L)
         → (b : Bool)
         → supp-condition-s b S As
         → Typing-STm ΓS (SCoh S As L) (label-on-sty As L)
TySCoh S {As} {L} [ Aty ] Lty Ltyty b sc .get = TyConv (apply-sub-tm-typing (TyCoh ⦃ tree-to-pd S ⦄ Aty id-Ty b (supp-condition-compat b S _ sc)) (label-to-sub-Ty Lty Ltyty)) (reflexive≈ty (begin
  < sty-to-type As [ idSub ]ty [ label-to-sub L ]ty >ty
    ≈⟨ sub-action-≃-ty (id-on-ty (sty-to-type As)) refl≃s ⟩
  < sty-to-type As [ label-to-sub L ]ty >ty
    ≈⟨ label-to-sub-sty L As ⟩
  < sty-to-type (label-on-sty As L) >ty ∎))
  where
    open Reasoning ty-setoid

extend-≈ : a ≈[ incTree S ]stm b → {L : Label-WT (COT-to-MT ΓS) S} → (Lty : Typing-Label ΓS L) → Typing-STy ΓS (lty L) → (a >>= L) ≈[ ΓS ]stm (b >>= L)
extend-≈ {a = a} {b = b} [ p ] {L} Lty AsTy .get = begin
  stm-to-term (a >>= L)
    ≈˘⟨ reflexive≈tm (label-to-sub-stm L a) ⟩
  stm-to-term a [ label-to-sub L ]tm
    ≈⟨ apply-sub-tm-eq (label-to-sub-Ty Lty AsTy) p ⟩
  stm-to-term b [ label-to-sub L ]tm
    ≈⟨ reflexive≈tm (label-to-sub-stm L b) ⟩
  stm-to-term (b >>= L) ∎
  where
    open Reasoning (tm-setoid-≈ _)

extend-Ty : {L : Label-WT (COT-to-MT ΓS) S} → Typing-STm (incTree S) a As → Typing-Label ΓS L → Typing-STy ΓS (lty L) → Typing-STm ΓS (a >>= L) (label-on-sty As L)
extend-Ty {a = a} {As = As} {L = L} [ aty ] Lty Ltyty .get = transport-typing-full (apply-sub-tm-typing aty (label-to-sub-Ty Lty Ltyty)) (label-to-sub-stm L a) (label-to-sub-sty L As)

last-path-Ty : (T : Tree n) → Typing-STm (incTree T) (SPath (last-path T)) S⋆
last-path-Ty T = [ (transport-typing (tree-last-var-Ty T) (sym≃tm (last-path-to-term T))) ]

map-sty-pext-Ty : Typing-STy (incTree S) As → Typing-STy (incTree (Join S T)) (map-sty-pext As)
map-sty-pext-Ty {As = S⋆} AsTy = TySArr (TySPath PHere) TySStar (TySShift (TySPath PHere))
map-sty-pext-Ty {As = SArr s As t} [ TyArr sty AsTy tty ] = TySArr (TySExt [ sty ]) (map-sty-pext-Ty [ AsTy ]) (TySExt [ tty ])

map-pext-Ty : {L : Label-WT (someTree S) U} → Typing-Label (incTree S) L → Typing-Label (incTree (Join S T)) (map-pext L)
map-pext-Ty (TySing x) = TySing (TySExt x)
map-pext-Ty (TyJoin x Lty Mty) = TyJoin (TySExt x) (map-pext-Ty Lty) (map-pext-Ty Mty)

map-sty-pshift-Ty : Typing-STy (incTree T) As → Typing-STy (incTree (Join S T)) (map-sty-pshift As)
map-sty-pshift-Ty {As = S⋆} AsTy = TySStar
map-sty-pshift-Ty {As = SArr s As t} [ TyArr sty AsTy tty ] = TySArr (TySShift [ sty ]) (map-sty-pshift-Ty [ AsTy ]) (TySShift [ tty ])

map-pshift-Ty : {L : Label-WT (someTree T) U} → Typing-Label (incTree T) L → Typing-Label (incTree (Join S T)) (map-pshift L)
map-pshift-Ty (TySing x) = TySing (TySShift x)
map-pshift-Ty (TyJoin x Lty Mty) = TyJoin (TySShift x) (map-pshift-Ty Lty) (map-pshift-Ty Mty)

id-label-Ty : (S : Tree n) → Typing-Label (incTree S) (id-label-wt S)
id-label-Ty Sing = TySing (TySPath PHere)
id-label-Ty (Join S T) = TyJoin (TySPath PHere) (transport-label-typing (map-pext-Ty (id-label-Ty S)) [ (λ P → compute-≃ refl≃stm) ] (≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm))) (transport-label-typing (map-pshift-Ty (id-label-Ty T)) [ (λ P → compute-≃ refl≃stm) ] refl≃sty)

connect-tree-inc-left-Ty : (S : Tree n)
                         → (T : Tree m)
                         → Typing-Label (incTree (connect-tree S T)) (connect-tree-inc-left S T)
connect-tree-inc-left-Ty Sing T = TySing (TySPath PHere)
connect-tree-inc-left-Ty (Join S₁ S₂) T
  = TyJoin (TySPath PHere)
           (transport-label-typing (map-pext-Ty (id-label-Ty S₁))
                                   [ (λ P → compute-≃ refl≃stm) ]
                                   (≃SArr refl≃stm
                                          refl≃sty
                                          (compute-≃ (≃SShift refl≃ (≃SPath (sym≃p (connect-tree-inc-left-phere S₂ T)))))))
           (transport-label-typing (map-pshift-Ty (connect-tree-inc-left-Ty S₂ T))
                                   [ (λ P → compute-≃ refl≃stm) ]
                                   refl≃sty)

connect-tree-inc-right-Ty : (S : Tree n)
                          → (T : Tree m)
                          → Typing-Label (incTree (connect-tree S T)) (connect-tree-inc-right S T)
connect-tree-inc-right-Ty Sing T = id-label-Ty T
connect-tree-inc-right-Ty (Join S₁ S₂) T = transport-label-typing (map-pshift-Ty (connect-tree-inc-right-Ty S₂ T)) [ (λ P → compute-≃ refl≃stm) ] refl≃sty
