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

susp-sty-tree-≈ : As ≈[ incTree S ]sty Bs → susp-sty As ≈[ incTree (suspTree S) ]sty susp-sty Bs
susp-sty-tree-≈ {As = S⋆} {Bs = S⋆} p = refl≈sty
susp-sty-tree-≈ {As = SArr s As t} {Bs = SArr s′ Bs t′} [ Arr≈ x p x′ ] = ≈SArr (≈SExt [ x ]) (susp-sty-tree-≈ [ p ]) (≈SExt [ x′ ])

unrestrict-label-≈ : {ΓS : CtxOrTree n} → {L M : Label-WT (COT-to-MT ΓS) S} → ap L ≈[ ΓS ]l ap M → (q : lty L ≈[ ΓS ]sty lty M) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → unrestrict-label L ≈[ ΓS ]l unrestrict-label M ⦃ NonZero-subst (sty-dim-≈ q) it ⦄
unrestrict-label-≈ p q .get PHere = sty-src-≈ q
unrestrict-label-≈ p q .get (PExt P) = p .get P
unrestrict-label-≈ p q .get (PShift P) = sty-tgt-≈ q

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

label-equality-to-sub : (L M : Label-WT (COT-to-MT ΓS) S) → ap L ≈[ ΓS ]l ap M → lty L ≈[ ΓS ]sty lty M → label-to-sub L ≈[ COT-to-Ctx ΓS ]s label-to-sub M
label-equality-to-sub {S = Sing} L M [ p ] [ q ] = Ext≈ (Null≈ q) (p PHere .get)
label-equality-to-sub {S = Join S T} L M [ p ] q
  = sub-from-connect-≈
      (unrestrictEq (label-equality-to-sub (label₁ L) (label₁ M) [ p ∘ PExt ] (≈SArr (p PHere) q (p (PShift PHere)))))
      (label-equality-to-sub (label₂ L) (label₂ M) [ p ∘ PShift ] q)

≈SCoh : (S : Tree n) → {As Bs : STy (someTree S)} → As ≈[ incTree S ]sty Bs → {L M : Label (COT-to-MT ΓS) S} → L ≈[ ΓS ]l M → {Cs Cs′ : STy (COT-to-MT ΓS)} → Cs ≈[ ΓS ]sty Cs′ → SCoh S As (L ,, Cs) ≈[ ΓS ]stm SCoh S Bs (M ,, Cs′)
≈SCoh S {As} {Bs} [ p ] {L} {M} q {S⋆} {S⋆} r = [ Coh≈ p (apply-sub-eq-sub idSub (label-equality-to-sub (L ,, S⋆) (M ,, S⋆) q r)) ]
≈SCoh S {As} {Bs} p {L} {M} q {SArr s Cs t} {SArr s′ Cs′ t′} r = begin
  SCoh S As (L ,, SArr s Cs t)
    ≈⟨ reflexive≈stm (SCoh-unrestrict S As (L ,, SArr s Cs t)) ⟩
  SCoh (suspTree S) (susp-sty As) (unrestrict-label (L ,, SArr s Cs t) ,, Cs)
    ≈⟨ ≈SCoh (suspTree S) (susp-sty-tree-≈ p) (unrestrict-label-≈ q r) {Cs} {Cs′} (sty-base-≈ r) ⟩
  SCoh (suspTree S) (susp-sty Bs)
    (unrestrict-label (M ,, SArr s′ Cs′ t′) ,, Cs′)
    ≈˘⟨ reflexive≈stm (SCoh-unrestrict S Bs (M ,, SArr s′ Cs′ t′)) ⟩
  SCoh S Bs (M ,, SArr s′ Cs′ t′) ∎
  where
    open Reasoning (stm-setoid-≈ _)

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

≈-extend : (a : STm (someTree S)) → {L M : Label-WT (COT-to-MT ΓS) S} → ap L ≈[ ΓS ]l ap M → lty L ≈[ ΓS ]sty lty M → (a >>= L) ≈[ ΓS ]stm (a >>= M)
≈-extend a {L = L} {M = M} p q .get = begin
  stm-to-term (a >>= L)
    ≈˘⟨ reflexive≈tm (label-to-sub-stm L a) ⟩
  stm-to-term a [ label-to-sub L ]tm
    ≈⟨ apply-sub-eq-tm (stm-to-term a) (label-equality-to-sub L M p q) ⟩
  stm-to-term a [ label-to-sub M ]tm
    ≈⟨ reflexive≈tm (label-to-sub-stm M a) ⟩
  stm-to-term (a >>= M) ∎
  where
    open Reasoning (tm-setoid-≈ _)

label-on-sty-≈ : (As : STy (someTree S)) → {L M : Label-WT (COT-to-MT ΓS) S} → ap L ≈[ ΓS ]l ap M → lty L ≈[ ΓS ]sty lty M → label-on-sty As L ≈[ ΓS ]sty label-on-sty As M
label-on-sty-≈ S⋆ p q = q
label-on-sty-≈ (SArr s As t) p q = ≈SArr (≈-extend s p q) (label-on-sty-≈ As p q) (≈-extend t p q)

extend-Ty : {L : Label-WT (COT-to-MT ΓS) S} → Typing-STm (incTree S) a As → Typing-Label ΓS L → Typing-STy ΓS (lty L) → Typing-STm ΓS (a >>= L) (label-on-sty As L)
extend-Ty {a = a} {As = As} {L = L} [ aty ] Lty Ltyty .get = transport-typing-full (apply-sub-tm-typing aty (label-to-sub-Ty Lty Ltyty)) (label-to-sub-stm L a) (label-to-sub-sty L As)

label-comp-Ty : {L : Label-WT (someTree T) S} {M : Label-WT (COT-to-MT ΓS) T} → Typing-Label (incTree T) L → Typing-Label ΓS M → Typing-STy ΓS (lty M) → Typing-Label ΓS (label-wt-comp L M)
label-comp-Ty (TySing x) MTy AsTy = TySing (extend-Ty x MTy AsTy)
label-comp-Ty (TyJoin x LTy LTy′) MTy AsTy = TyJoin (extend-Ty x MTy AsTy) (label-comp-Ty LTy MTy AsTy) (label-comp-Ty LTy′ MTy AsTy)

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

replace-label-Ty : {L : Label-WT (COT-to-MT ΓS) S}
                 → Typing-Label ΓS L
                 → Typing-STm ΓS a (lty L)
                 → ap L PHere ≈[ ΓS ]stm a
                 → Typing-Label ΓS (replace-label (ap L) a ,, lty L)
replace-label-Ty (TySing x) aTy p = TySing aTy
replace-label-Ty (TyJoin x LTy LTy′) aTy p = TyJoin aTy (label-typing-conv LTy (≈SArr p refl≈sty refl≈stm)) LTy′

connect-label-Ty : Typing-Label ΓS (L ,, As)
                 → Typing-Label ΓS (M ,, As)
                 → L (last-path S) ≈[ ΓS ]stm M PHere
                 → Typing-Label ΓS (connect-label L M ,, As)
connect-label-Ty (TySing x) MTy p = replace-label-Ty MTy x (sym≈stm p)
connect-label-Ty (TyJoin {L = L} x LTy LTy′) MTy p = TyJoin x (label-typing-conv LTy (≈SArr refl≈stm refl≈sty (reflexive≈stm (sym≃stm (connect-label-phere (ap L ∘ PShift) _))))) (connect-label-Ty LTy′ MTy p)

label-between-connect-trees-Ty : Typing-Label (incTree S′) (L ,, S⋆)
                               → Typing-Label (incTree T′) (M ,, S⋆)
                               → L (last-path S) ≈[ incTree S′ ]stm SPath (last-path S′)
                               → M PHere ≈[ incTree T′ ]stm SHere
                               → Typing-Label (incTree (connect-tree S′ T′)) (label-between-connect-trees L M ,, S⋆)
label-between-connect-trees-Ty {S′ = S′} {S = S} {L = L} {T′ = T′} {M = M} LTy MTy p q
  = connect-label-Ty (label-comp-Ty LTy (connect-tree-inc-left-Ty _ _) TySStar)
                     (label-comp-Ty MTy (connect-tree-inc-right-Ty _ _) TySStar)
                     (begin
                       label-comp L (connect-tree-inc-left S′ T′) (last-path S)
                         ≡⟨⟩
                       (L (last-path S) >>= connect-tree-inc-left S′ T′)
                         ≈⟨ extend-≈ p (connect-tree-inc-left-Ty S′ T′) TySStar ⟩
                       (SPath (last-path S′) >>= connect-tree-inc-left S′ T′)
                         ≈⟨ reflexive≈stm (≃SPath (connect-tree-inc-phere S′ T′)) ⟩
                       (SHere >>= connect-tree-inc-right S′ T′)
                         ≈˘⟨ extend-≈ q (connect-tree-inc-right-Ty S′ T′) TySStar ⟩
                       (M PHere >>= connect-tree-inc-right S′ T′)
                         ≡⟨⟩
                       label-comp M (connect-tree-inc-right S′ T′) PHere ∎)
                       where open Reasoning (stm-setoid-≈ (incTree (connect-tree S′ T′)))

label-between-joins-Ty : Typing-Label (incTree S′) (L ,, S⋆)
                       → Typing-Label (incTree T′) (M ,, S⋆)
                       → M PHere ≈[ incTree T′ ]stm SHere
                       → Typing-Label (incTree (Join S′ T′)) (label-between-joins L M ,, S⋆)
label-between-joins-Ty LTy MTy p = TyJoin (TySPath PHere) (label-typing-conv (map-pext-Ty LTy) (≈SArr refl≈stm refl≈sty (sym≈stm (≈SShift p)))) (map-pshift-Ty MTy)

label-max-equality-to-equality : {L M : Label-WT (COT-to-MT ΓS) S} → ap L ≃lm ap M → Typing-Label ΓS L → Typing-Label ΓS M → ap L ≈[ ΓS ]l ap M
label-max-equality-to-type-equality : {L M : Label-WT (COT-to-MT ΓS) S} → ap L ≃lm ap M → Typing-Label ΓS L → Typing-Label ΓS M → lty L ≈[ ΓS ]sty lty M

label-max-equality-to-equality {S = Sing} [ p ] Lty Mty .get PHere = reflexive≈stm (p PHere)
label-max-equality-to-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get PHere with label-max-equality-to-type-equality [ p ∘ PExt ] Lty Mty
... | a = sty-src-≈ a
label-max-equality-to-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PExt P) = label-max-equality-to-equality [ p ∘ PExt ] Lty Mty .get P
label-max-equality-to-equality {S = Join S Sing} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PShift PHere) with label-max-equality-to-type-equality [ p ∘ PExt ] Lty Mty
... | a = sty-tgt-≈ a
label-max-equality-to-equality {S = Join S T@(Join _ _)} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PShift P) = label-max-equality-to-equality [ (λ Q → p (PShift Q) ⦃ build ⦃ maximal-join-not-here Q ⦄ ⦃ it ⦄ ⦄) ] Lty′ Mty′ .get P

label-max-equality-to-type-equality {S = Sing} [ p ] (TySing x) (TySing y) = [ (Ty-unique-≃ (p PHere .get) (x .get) (y .get)) ]
label-max-equality-to-type-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) = sty-base-≈ (label-max-equality-to-type-equality [ p ∘ PExt ] Lty Mty)

label-≃-Ty : (p : S ≃′ T) → {L : Label-WT (COT-to-MT ΓS) T} → Typing-Label ΓS L → Typing-Label ΓS (label-wt-≃ p L)
label-≃-Ty Refl≃′ LTy = LTy
label-≃-Ty (Join≃′ p q) (TyJoin {L = L} x LTy LTy′) = TyJoin x (label-typing-conv (label-≃-Ty p LTy) (reflexive≈sty (≃SArr refl≃stm refl≃sty (ap-≃ (refl≃l {L = ap L}) (≃Shift refl≃ (trans≃p (≃Here (sym≃ (≃′-to-≃ q))) (ppath-≃-≃p q PHere))))))) (label-≃-Ty q LTy′)

truncate-sty′-≈ : d ≡ d′ → As ≈[ ΓS ]sty Bs → truncate-sty′ d As ≈[ ΓS ]sty truncate-sty′ d′ Bs
truncate-sty′-≈ {d = zero} refl q = q
truncate-sty′-≈ {d = suc d} refl q = truncate-sty′-≈ {d = d} refl (sty-base-≈ q)

truncate-sty-≈ : d ≡ d′ → As ≈[ ΓS ]sty Bs → truncate-sty d As ≈[ ΓS ]sty truncate-sty d′ Bs
truncate-sty-≈ {d = d} refl q = truncate-sty′-≈ (cong (_∸ d) (sty-dim-≈ q)) q
