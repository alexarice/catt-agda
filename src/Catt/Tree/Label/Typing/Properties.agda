open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Label.Typing.Properties {index : Set}
                                         (rule : index → Rule)
                                         (lift-rule : ∀ i → P.LiftRule rule (rule i))
                                         (susp-rule : ∀ i → P.SuspRule rule (rule i))
                                         (sub-rule : ∀ i → P.SubRule rule (rule i)) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Typing rule
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Path.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Properties
open import Catt.Tree.Typing rule lift-rule susp-rule sub-rule
open import Catt.Suspension
open import Catt.Suspension.Typing rule lift-rule susp-rule
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Typing rule lift-rule susp-rule sub-rule
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Globular.Typing rule lift-rule
open import Catt.Tree.Label.Typing rule

≈SExt : {a b : STm (someTree S)} → a ≈[ tree-to-ctx S ]stm b → SExt {T = T} a ≈[ tree-to-ctx (Join S T) ]stm SExt b
≈SExt {T = T} [ p ] = [ (apply-sub-tm-eq (connect-susp-inc-left-Ty (tree-to-ctx T)) (susp-tmEq p)) ]

≈SShift : {a b : STm (someTree T)} → a ≈[ tree-to-ctx T ]stm b → SShift {S = S} a ≈[ tree-to-ctx (Join S T) ]stm SShift b
≈SShift {S = S} [ q ] = [ (apply-sub-tm-eq (connect-susp-inc-right-Ty (tree-to-ctx S)) q) ]

≈SPath : P ≃p Q → SPath P ≃stm SPath Q
≈SPath p = [ path-to-term-≃ p ]

susp-sty-tree-≈ : {As Bs : STy (someTree S)} → As ≈[ tree-to-ctx S ]sty Bs → susp-sty As ≈[ tree-to-ctx (suspTree S) ]sty susp-sty Bs
susp-sty-tree-≈ {As = S⋆} {Bs = S⋆} p = refl≈sty
susp-sty-tree-≈ {As = SArr s As t} {Bs = SArr s′ Bs t′} [ Arr≈ x p x′ ] = ≈SArr (≈SExt [ x ]) (susp-sty-tree-≈ [ p ]) (≈SExt [ x′ ])

unrestrict-label-≈ : {L M : Label-WT X S} → ap L ≈[ Γ ]l ap M → (q : lty L ≈[ Γ ]sty lty M) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → unrestrict-label L ≈[ Γ ]l unrestrict-label M ⦃ NonZero-subst (sty-dim-≈ q) it ⦄
unrestrict-label-≈ p q .get PHere = sty-src-≈ q
unrestrict-label-≈ p q .get (PExt P) = p .get P
unrestrict-label-≈ p q .get (PShift P) = sty-tgt-≈ q

label-to-sub-Ty : {L : Label-WT X S} → Typing-Label Γ L → Typing-STy Γ (lty L) → Typing-Sub (tree-to-ctx S) Γ (label-to-sub L)
label-to-sub-Ty (TySing [ x ]) [ Aty ] = TyExt (TyNull Aty) x
label-to-sub-Ty {L = L} (TyJoin x Lty Mty) Aty = sub-from-connect-Ty (unrestrictTy (label-to-sub-Ty Lty (TySArr x Aty (ap-phere-Ty Mty)))) get-sndTy (label-to-sub-Ty Mty Aty) (reflexive≈tm (label-to-sub-lem L) )

TySPath : (P : Path S) → Typing-STm (tree-to-ctx S) (SPath P) (getPathType P)
TySPath P .get = path-to-term-Ty P

TySExt : {a : STm (someTree S)} → Typing-STm (tree-to-ctx S) a As → Typing-STm (tree-to-ctx (Join S T)) (SExt {T = T} a) (map-sty-pext As)
TySExt {As = As} {T = T} [ aty ] .get = TyConv (apply-sub-tm-typing (susp-tmTy aty) (connect-susp-inc-left-Ty (tree-to-ctx T))) (reflexive≈ty (begin
  < susp-ty (sty-to-type As) [ connect-susp-inc-left _ _ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (susp-sty-to-type As) refl≃s ⟩
  < sty-to-type (susp-sty As) [ connect-susp-inc-left _ (tree-size T) ]ty >ty
    ≈˘⟨ sty-sub-prop (susp-sty As) (connect-susp-inc-left _ (tree-size T)) ⟩
  < sty-to-type (sty-sub (susp-sty As) (connect-susp-inc-left _ (tree-size T))) >ty
    ≈⟨ map-sty-pext-prop As .get  ⟩
  < sty-to-type (map-sty-pext As) >ty ∎))
  where
    open Reasoning ty-setoid

TySShift : {a : STm (someTree T)} → Typing-STm (tree-to-ctx T) a As → Typing-STm (tree-to-ctx (Join S T)) (SShift {S = S} a) (map-sty-pshift As)
TySShift {As = As} {S = S} [ aty ] .get = TyConv (apply-sub-tm-typing aty (connect-susp-inc-right-Ty (tree-to-ctx S))) (reflexive≈ty (begin
  < sty-to-type As [ connect-susp-inc-right _ _ ]ty >ty
    ≈˘⟨ sty-sub-prop As (connect-susp-inc-right (tree-size S) _) ⟩
  < sty-to-type (sty-sub As (connect-susp-inc-right (tree-size S) _)) >ty
    ≈˘⟨ map-sty-pshift-prop As .get ⟩
  < sty-to-type (map-sty-pshift As) >ty ∎))
  where
    open Reasoning ty-setoid

TySCoh : (S : Tree n) → {As : STy (someTree S)} → {L : Label-WT X S}
         → Typing-STy (tree-to-ctx S) As
         → Typing-Label Γ L
         → Typing-STy Γ (lty L)
         → Typing-STm Γ (SCoh S As L) (label-on-sty As L)
TySCoh S {As} {L} [ Aty ] Lty Ltyty .get = TyConv (apply-sub-tm-typing (TyCoh ⦃ tree-to-pd S ⦄ Aty id-Ty) (label-to-sub-Ty Lty Ltyty)) (reflexive≈ty (begin
  < sty-to-type As [ idSub ]ty [ label-to-sub L ]ty >ty
    ≈⟨ sub-action-≃-ty (id-on-ty (sty-to-type As)) refl≃s ⟩
  < sty-to-type As [ label-to-sub L ]ty >ty
    ≈⟨ label-to-sub-sty L As ⟩
  < sty-to-type (label-on-sty As L) >ty ∎))
  where
    open Reasoning ty-setoid

label-equality-to-sub : (L M : Label-WT X S) → ap L ≈[ Γ ]l ap M → lty L ≈[ Γ ]sty lty M → label-to-sub L ≈[ Γ ]s label-to-sub M
label-equality-to-sub {S = Sing} L M [ p ] [ q ] = Ext≈ (Null≈ q) (p PHere .get)
label-equality-to-sub {S = Join S T} L M [ p ] q
  = sub-from-connect-≈
      (unrestrictEq (label-equality-to-sub (label₁ L) (label₁ M) [ p ∘ PExt ] (≈SArr (p PHere) q (p (PShift PHere)))))
      (label-equality-to-sub (label₂ L) (label₂ M) [ p ∘ PShift ] q)

≈SCoh : (S : Tree n) → {As Bs : STy (someTree S)} → As ≈[ tree-to-ctx S ]sty Bs → {L M : Label X S} → L ≈[ Γ ]l M → {Cs Cs′ : STy X} → Cs ≈[ Γ ]sty Cs′ → SCoh S As (L ,, Cs) ≈[ Γ ]stm SCoh S Bs (M ,, Cs′)
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
    open Reasoning stm-setoid-≈

extend-≈ : a ≈[ tree-to-ctx S ]stm b → {L : Label-WT X S} → (Lty : Typing-Label Γ L) → Typing-STy Γ (lty L) → (a >>= L) ≈[ Γ ]stm (b >>= L)
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

≈-extend : (a : STm (someTree S)) → {L M : Label-WT X S} → ap L ≈[ Γ ]l ap M → lty L ≈[ Γ ]sty lty M → (a >>= L) ≈[ Γ ]stm (a >>= M)
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

label-on-sty-≈ : (As : STy (someTree S)) → {L M : Label-WT X S} → ap L ≈[ Γ ]l ap M → lty L ≈[ Γ ]sty lty M → label-on-sty As L ≈[ Γ ]sty label-on-sty As M
label-on-sty-≈ S⋆ p q = q
label-on-sty-≈ (SArr s As t) p q = ≈SArr (≈-extend s p q) (label-on-sty-≈ As p q) (≈-extend t p q)

extend-Ty : {L : Label-WT X S} → Typing-STm (tree-to-ctx S) a As → Typing-Label Γ L → Typing-STy Γ (lty L) → Typing-STm Γ (a >>= L) (label-on-sty As L)
extend-Ty {a = a} {As = As} {L = L} [ aty ] Lty Ltyty .get = transport-typing-full (apply-sub-tm-typing aty (label-to-sub-Ty Lty Ltyty)) (label-to-sub-stm L a) (label-to-sub-sty L As)

label-comp-Ty : {L : Label-WT (someTree T) S} {M : Label-WT X T} → Typing-Label (tree-to-ctx T) L → Typing-Label Γ M → Typing-STy Γ (lty M) → Typing-Label Γ (label-wt-comp L M)
label-comp-Ty (TySing x) MTy AsTy = TySing (extend-Ty x MTy AsTy)
label-comp-Ty (TyJoin x LTy LTy′) MTy AsTy = TyJoin (extend-Ty x MTy AsTy) (label-comp-Ty LTy MTy AsTy) (label-comp-Ty LTy′ MTy AsTy)

last-path-Ty : (T : Tree n) → Typing-STm (tree-to-ctx T) (SPath (last-path T)) S⋆
last-path-Ty T = [ (transport-typing (tree-last-var-Ty T) (sym≃tm (last-path-to-term T))) ]

map-sty-pext-Ty : Typing-STy (tree-to-ctx S) As → Typing-STy (tree-to-ctx (Join S T)) (map-sty-pext {S = S} {T = T} As)
map-sty-pext-Ty {As = S⋆} AsTy = TySArr (TySPath PHere) TySStar (TySShift (TySPath PHere))
map-sty-pext-Ty {As = SArr s As t} [ TyArr sty AsTy tty ] = TySArr (TySExt [ sty ]) (map-sty-pext-Ty [ AsTy ]) (TySExt [ tty ])

map-pext-Ty : {L : Label-WT (someTree S) U} → Typing-Label (tree-to-ctx S) L → Typing-Label (tree-to-ctx (Join S T)) (map-pext {T = T} L)
map-pext-Ty (TySing x) = TySing (TySExt x)
map-pext-Ty (TyJoin x Lty Mty) = TyJoin (TySExt x) (map-pext-Ty Lty) (map-pext-Ty Mty)

map-sty-pshift-Ty : Typing-STy (tree-to-ctx T) As → Typing-STy (tree-to-ctx (Join S T)) (map-sty-pshift {T = T} {S = S} As)
map-sty-pshift-Ty {As = S⋆} AsTy = TySStar
map-sty-pshift-Ty {As = SArr s As t} [ TyArr sty AsTy tty ] = TySArr (TySShift [ sty ]) (map-sty-pshift-Ty [ AsTy ]) (TySShift [ tty ])

map-pshift-Ty : {L : Label-WT (someTree T) U} → Typing-Label (tree-to-ctx T) L → Typing-Label (tree-to-ctx (Join S T)) (map-pshift {S = S} L)
map-pshift-Ty (TySing x) = TySing (TySShift x)
map-pshift-Ty (TyJoin x Lty Mty) = TyJoin (TySShift x) (map-pshift-Ty Lty) (map-pshift-Ty Mty)

id-label-Ty : (S : Tree n) → Typing-Label (tree-to-ctx S) (id-label-wt S)
id-label-Ty Sing = TySing (TySPath PHere)
id-label-Ty (Join S T) = TyJoin (TySPath PHere) (transport-label-typing (map-pext-Ty (id-label-Ty S)) [ (λ P → compute-≃ refl≃stm) ] (≃SArr refl≃stm refl≃sty (compute-≃ refl≃stm))) (transport-label-typing (map-pshift-Ty (id-label-Ty T)) [ (λ P → compute-≃ refl≃stm) ] refl≃sty)

stm-sub-Ty : Typing-STm Δ a As → Typing-Sub Δ Γ σ → Typing-STm Γ (stm-sub a σ) (sty-sub As σ)
stm-sub-Ty {As = As} [ aty ] σty = [ TyConv (apply-sub-tm-typing aty σty) (reflexive≈ty (sym≃ty (sty-sub-prop As _))) ]

label-sub-Ty : {L : Label-WT X S} → Typing-Label Δ L → Typing-Sub Δ Γ σ → Typing-Label Γ (label-sub L σ)
label-sub-Ty (TySing xty) σty = TySing (stm-sub-Ty xty σty)
label-sub-Ty (TyJoin xty Lty Mty) σty = TyJoin (stm-sub-Ty xty σty) (label-sub-Ty Lty σty) (label-sub-Ty Mty σty)

to-label-Ty : (S : Tree n) → (Γ : Ctx m) → Typing-Sub (tree-to-ctx S) Γ σ → Typing-Label Γ (to-label-wt S σ)
to-label-Ty S Γ σty = label-sub-Ty (id-label-Ty S) σty

Label′-Ty : {L : Label-WT X S} → Typing-Label Γ L → Typing-STy Γ (lty L) → Typing-Label′ Γ L
Label′-Ty Lty Asty = [ label-to-sub-Ty Lty Asty ]

Label-ty : {L : Label-WT X S} → Typing-Label′ Γ L → Typing-Label Γ L
Label-ty {S = S} {Γ = Γ} {L = L} [ Lty ] = transport-label-typing (to-label-Ty S Γ Lty) (label-to-sub-to-label L) (sty-to-type-to-sty (lty L))

connect-tree-inc-left-Ty : (S : Tree n)
                         → (T : Tree m)
                         → Typing-Label (tree-to-ctx (connect-tree S T)) (connect-tree-inc-left S T)
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
                          → Typing-Label (tree-to-ctx (connect-tree S T)) (connect-tree-inc-right S T)
connect-tree-inc-right-Ty Sing T = id-label-Ty T
connect-tree-inc-right-Ty (Join S₁ S₂) T = transport-label-typing (map-pshift-Ty (connect-tree-inc-right-Ty S₂ T)) [ (λ P → compute-≃ refl≃stm) ] refl≃sty

replace-label-Ty : {L : Label-WT X S}
                 → Typing-Label Γ L
                 → Typing-STm Γ a (lty L)
                 → ap L PHere ≈[ Γ ]stm a
                 → Typing-Label Γ (replace-label (ap L) a ,, lty L)
replace-label-Ty (TySing x) aTy p = TySing aTy
replace-label-Ty (TyJoin x LTy LTy′) aTy p = TyJoin aTy (label-typing-conv LTy (≈SArr p refl≈sty refl≈stm)) LTy′

connect-label-Ty : Typing-Label Γ (L ,, As)
                 → Typing-Label Γ (M ,, As)
                 → L (last-path S) ≈[ Γ ]stm M PHere
                 → Typing-Label Γ (connect-label L M ,, As)
connect-label-Ty (TySing x) MTy p = replace-label-Ty MTy x (sym≈stm p)
connect-label-Ty (TyJoin {L = L} x LTy LTy′) MTy p = TyJoin x (label-typing-conv LTy (≈SArr refl≈stm refl≈sty (reflexive≈stm (sym≃stm (connect-label-phere (ap L ∘ PShift) _))))) (connect-label-Ty LTy′ MTy p)

label-between-connect-trees-lem : (L : Label (someTree S′) S)
                               → (M : Label (someTree T′) T)
                               → L (last-path S) ≈[ tree-to-ctx S′ ]stm SPath (last-path S′)
                               → M PHere ≈[ tree-to-ctx T′ ]stm SHere
                               → (label-comp L (connect-tree-inc-left S′ T′) (last-path S) ≈[ tree-to-ctx (connect-tree S′ T′) ]stm
                                    label-comp M (connect-tree-inc-right S′ T′) PHere)
label-between-connect-trees-lem {S′ = S′} {S = S} {T′ = T′} L M p q = begin
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
  label-comp M (connect-tree-inc-right S′ T′) PHere ∎
  where
    open Reasoning stm-setoid-≈

label-between-connect-trees-Ty : {L : Label (someTree S′) S}
                               → {M : Label (someTree T′) T}
                               → Typing-Label (tree-to-ctx S′) (L ,, S⋆)
                               → Typing-Label (tree-to-ctx T′) (M ,, S⋆)
                               → L (last-path S) ≈[ tree-to-ctx S′ ]stm SPath (last-path S′)
                               → M PHere ≈[ tree-to-ctx T′ ]stm SHere
                               → Typing-Label (tree-to-ctx (connect-tree S′ T′)) (label-between-connect-trees L M ,, S⋆)
label-between-connect-trees-Ty {S′ = S′} {S = S} {T′ = T′} {L = L} {M = M} LTy MTy p q
  = connect-label-Ty (label-comp-Ty LTy (connect-tree-inc-left-Ty _ _) TySStar)
                     (label-comp-Ty MTy (connect-tree-inc-right-Ty _ _) TySStar)
                     (label-between-connect-trees-lem L M p q)

label-between-joins-Ty : {L : Label (someTree S′) S}
                       → {M : Label (someTree T′) T}
                       → Typing-Label (tree-to-ctx S′) (L ,, S⋆)
                       → Typing-Label (tree-to-ctx T′) (M ,, S⋆)
                       → M PHere ≈[ tree-to-ctx T′ ]stm SHere
                       → Typing-Label (tree-to-ctx (Join S′ T′)) (label-between-joins L M ,, S⋆)
label-between-joins-Ty LTy MTy p = TyJoin (TySPath PHere) (label-typing-conv (map-pext-Ty LTy) (≈SArr refl≈stm refl≈sty (sym≈stm (≈SShift p)))) (map-pshift-Ty MTy)

label-max-equality-to-equality : {L M : Label-WT X S} → ap L ≃lm ap M → Typing-Label Γ L → Typing-Label Γ M → ap L ≈[ Γ ]l ap M
label-max-equality-to-type-equality : {L M : Label-WT X S} → ap L ≃lm ap M → Typing-Label Γ L → Typing-Label Γ M → lty L ≈[ Γ ]sty lty M

label-max-equality-to-equality {S = Sing} [ p ] Lty Mty .get PHere = reflexive≈stm (p PHere)
label-max-equality-to-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get PHere with label-max-equality-to-type-equality [ p ∘ PExt ] Lty Mty
... | a = sty-src-≈ a
label-max-equality-to-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PExt P) = label-max-equality-to-equality [ p ∘ PExt ] Lty Mty .get P
label-max-equality-to-equality {S = Join S Sing} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PShift PHere) with label-max-equality-to-type-equality [ p ∘ PExt ] Lty Mty
... | a = sty-tgt-≈ a
label-max-equality-to-equality {S = Join S T@(Join _ _)} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PShift P) = label-max-equality-to-equality [ (λ Q → p (PShift Q) ⦃ build ⦃ maximal-join-not-here Q ⦄ ⦃ it ⦄ ⦄) ] Lty′ Mty′ .get P

label-max-equality-to-type-equality {S = Sing} [ p ] (TySing x) (TySing y) = [ (Ty-unique-≃ (p PHere .get) (x .get) (y .get)) ]
label-max-equality-to-type-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) = sty-base-≈ (label-max-equality-to-type-equality [ p ∘ PExt ] Lty Mty)

label-≃-Ty : (p : S ≃′ T) → {L : Label-WT X T} → Typing-Label Γ L → Typing-Label Γ (label-wt-≃ p L)
label-≃-Ty Refl≃′ LTy = LTy
label-≃-Ty (Join≃′ p q) (TyJoin {L = L} x LTy LTy′) = TyJoin x (label-typing-conv (label-≃-Ty p LTy) (reflexive≈sty (≃SArr refl≃stm refl≃sty (ap-≃ (refl≃l {L = ap L}) (≃Shift refl≃ (trans≃p (≃Here (sym≃ (≃′-to-≃ q))) (ppath-≃-≃p q PHere))))))) (label-≃-Ty q LTy′)

truncate-sty′-≈ : d ≡ d′ → As ≈[ Γ ]sty Bs → truncate-sty′ d As ≈[ Γ ]sty truncate-sty′ d′ Bs
truncate-sty′-≈ {d = zero} refl q = q
truncate-sty′-≈ {d = suc d} refl q = truncate-sty′-≈ {d = d} refl (sty-base-≈ q)

truncate-sty-≈ : d ≡ d′ → As ≈[ Γ ]sty Bs → truncate-sty d As ≈[ Γ ]sty truncate-sty d′ Bs
truncate-sty-≈ {d = d} refl q = truncate-sty′-≈ (cong (_∸ d) (sty-dim-≈ q)) q

SCoh-typing-prop : {L : Label-WT X S} → Typing-STm Γ (SCoh S As L) Bs → label-on-sty As L ≈[ Γ ]sty Bs
SCoh-typing-prop {S = S} {Γ = Γ} {As = As} {L = L} [ tty ] .get = begin
  sty-to-type (label-on-sty As L)
    ≈˘⟨ reflexive≈ty (label-to-sub-sty L As) ⟩
  sty-to-type As [ label-to-sub L ]ty
    ≈˘⟨ reflexive≈ty (sub-action-≃-ty (refl≃ty {A = sty-to-type As}) (id-right-unit (label-to-sub L))) ⟩
  sty-to-type As [ label-to-sub L ● idSub ]ty
    ≈˘⟨ reflexive≈ty (tm-to-ty-coh-sub (tree-to-ctx S) (sty-to-type As) idSub Γ (label-to-sub L)) ⟩
  tm-to-ty Γ (stm-to-term (SCoh S As L))
    ≈⟨ tm-to-ty-prop tty ⟩
  sty-to-type _ ∎
  where
    open Reasoning (ty-setoid-≈ _)
