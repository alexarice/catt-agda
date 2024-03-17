open import Catt.Typing.Rule

module Catt.Tree.Structured.Typing.Properties (ops : Op)
                                              (rules : RuleSet)
                                              (tame : Tame ops rules) where

open Tame tame

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Wedge.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Pasting
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Globular.Properties
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Structured.ToTerm

open import Catt.Ops.Tree ops

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Tree.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Structured.Support.Properties

open import Catt.Typing ops rules
open import Catt.Typing.Properties ops rules tame
open import Catt.Globular.Typing ops rules
open import Catt.Suspension.Typing ops susp-op rules susp-cond
open import Catt.Wedge.Typing ops rules tame
open import Catt.Tree.Typing ops rules tame
open import Catt.Tree.Path.Typing ops rules tame
open import Catt.Tree.Structured.Typing ops rules

≈SExt : {a b : STm (someTree S)} → a ≈[ ⌊ S ⌋ ]stm b → SExt {T = T} a ≈[ ⌊ Join S T ⌋ ]stm SExt b
≈SExt {T = T} [ p ] = [ (apply-sub-tm-eq (wedge-susp-inc-left-Ty ⌊ T ⌋) (susp-tmEq p)) ]

≈SShift : {a b : STm (someTree T)} → a ≈[ ⌊ T ⌋ ]stm b → SShift {S = S} a ≈[ ⌊ Join S T ⌋ ]stm SShift b
≈SShift {S = S} [ q ] = [ (apply-sub-tm-eq (wedge-susp-inc-right-Ty ⌊ S ⌋) q) ]

≈SPath : P ≃p Q → SPath P ≃stm SPath Q
≈SPath p = [ path-to-term-≃ p ]

susp-sty-tree-≈ : {As Bs : STy (someTree S)} → As ≈[ ⌊ S ⌋ ]sty Bs → susp-sty As ≈[ ⌊ Susp S ⌋ ]sty susp-sty Bs
susp-sty-tree-≈ {As = S⋆} {Bs = S⋆} p = refl≈sty
susp-sty-tree-≈ {As = SArr s As t} {Bs = SArr s′ Bs t′} [ Arr≈ x p x′ ] = ≈SArr (≈SExt [ x ]) (susp-sty-tree-≈ [ p ]) (≈SExt [ x′ ])

↓-label-≈ : {L M : Label-WT X S} → ap L ≈[ Γ ]l ap M → (q : lty L ≈[ Γ ]sty lty M) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → ↓-label L ≈[ Γ ]l ↓-label M ⦃ NonZero-subst (sty-dim-≈ q) it ⦄
↓-label-≈ p q .get PHere = sty-src-≈ q
↓-label-≈ p q .get (PExt P) = p .get P
↓-label-≈ p q .get (PShift P) = sty-tgt-≈ q

label-to-sub-Ty : {L : Label-WT X S} → Typing-Label Γ L → Typing-STy Γ (lty L) → Typing-Sub ⌊ S ⌋ Γ (label-to-sub L)
label-to-sub-Ty (TySing [ x ]) [ Aty ] = TyExt (TyNull Aty) x
label-to-sub-Ty {L = L} (TyJoin x Lty Mty) Aty = sub-from-wedge-Ty (↓-Ty (label-to-sub-Ty Lty (TySArr x Aty (ap-phere-Ty Mty)))) get-sndTy (label-to-sub-Ty Mty Aty) (reflexive≈tm (label-to-sub-lem L) )

TySPath : (P : Path S) → Typing-STm ⌊ S ⌋ (SPath P) (getPathType P)
TySPath P .get = path-to-term-Ty P

TySExt : {a : STm (someTree S)} → Typing-STm ⌊ S ⌋ a As → Typing-STm ⌊ Join S T ⌋ (SExt {T = T} a) (map-sty-ext As)
TySExt {As = As} {T = T} [ aty ] .get = TyConv (apply-sub-tm-typing (susp-tmTy aty) (wedge-susp-inc-left-Ty ⌊ T ⌋)) (reflexive≈ty (begin
  < susp-ty (sty-to-type As) [ wedge-susp-inc-left _ _ ]ty >ty
    ≈˘⟨ sub-action-≃-ty (susp-sty-to-type As) refl≃s ⟩
  < sty-to-type (susp-sty As) [ wedge-susp-inc-left _ (tree-size T) ]ty >ty
    ≈˘⟨ sty-sub-to-type (susp-sty As) (wedge-susp-inc-left _ (tree-size T)) ⟩
  < sty-to-type (susp-sty As [ wedge-susp-inc-left _ (tree-size T) ]sty) >ty
    ≈⟨ map-sty-ext-prop As .get  ⟩
  < sty-to-type (map-sty-ext As) >ty ∎))
  where
    open Reasoning ty-setoid

TySShift : {a : STm (someTree T)} → Typing-STm ⌊ T ⌋ a As → Typing-STm ⌊ Join S T ⌋ (SShift {S = S} a) (map-sty-shift As)
TySShift {As = As} {S = S} [ aty ] .get = TyConv (apply-sub-tm-typing aty (wedge-susp-inc-right-Ty ⌊ S ⌋)) (reflexive≈ty (begin
  < sty-to-type As [ wedge-susp-inc-right _ _ ]ty >ty
    ≈˘⟨ sty-sub-to-type As (wedge-susp-inc-right (tree-size S) _) ⟩
  < sty-to-type (As [ wedge-susp-inc-right (tree-size S) _ ]sty) >ty
    ≈˘⟨ map-sty-shift-prop As .get ⟩
  < sty-to-type (map-sty-shift As) >ty ∎))
  where
    open Reasoning ty-setoid

TySCoh : (S : Tree n)
       → {As : STy (someTree S)} → .⦃ _ : NonZero (sty-dim As) ⦄
       → ops-s S (DCT (FVSTm (sty-src As))) (DCT (FVSTm (sty-tgt As)))
       → {L : Label-WT X S}
       → Typing-STy ⌊ S ⌋ As
       → Typing-Label Γ L
       → Typing-STy Γ (lty L)
       → Typing-STm Γ (SCoh S As L) (As >>=′ L)
TySCoh S {As} supp {L} [ Aty ] Lty Ltyty .get
  = TyConv (apply-sub-tm-typing (TyCoh ⦃ tree-to-pd S ⦄
                                       (subst₂ (ops ⌊ S ⌋)
                                               l1
                                               l2
                                               supp)
                                       Aty
                                       id-Ty)
                                (label-to-sub-Ty Lty Ltyty))
           (reflexive≈ty (begin
  < sty-to-type As [ idSub ]ty [ label-to-sub L ]ty >ty
    ≈⟨ sub-action-≃-ty (id-on-ty (sty-to-type As)) refl≃s ⟩
  < sty-to-type As [ label-to-sub L ]ty >ty
    ≈⟨ label-to-sub-sty L As ⟩
  < sty-to-type (As >>=′ L) >ty ∎))
  where
    instance .x : NonZero (ty-dim (sty-to-type As))
    x = NonZero-subst (sym (sty-to-type-dim As)) it

    l1 : toVarSet (DCT (FVSTm (sty-src As))) ≡ SuppTm ⌊ S ⌋ (ty-src (sty-to-type As))
    l1 = begin
      toVarSet (DCT (FVSTm (sty-src As)))
        ≡⟨ DCT-toVarSet (FVSTm (sty-src As)) ⟩
      toVarSet (FVSTm (sty-src As))
        ≡⟨ FVSTm-to-term (sty-src As) ⟩
      SuppTm ⌊ S ⌋ (stm-to-term (sty-src As))
        ≡⟨ cong (DC ⌊ S ⌋) (FVTm-≃ (sty-src-to-term As)) ⟩
      SuppTm ⌊ S ⌋ (ty-src (sty-to-type As)) ∎
      where
        open ≡-Reasoning

    l2 : toVarSet (DCT (FVSTm (sty-tgt As))) ≡ SuppTm ⌊ S ⌋ (ty-tgt (sty-to-type As))
    l2 = begin
      toVarSet (DCT (FVSTm (sty-tgt As)))
        ≡⟨ DCT-toVarSet (FVSTm (sty-tgt As)) ⟩
      toVarSet (FVSTm (sty-tgt As))
        ≡⟨ FVSTm-to-term (sty-tgt As) ⟩
      SuppTm ⌊ S ⌋ (stm-to-term (sty-tgt As))
        ≡⟨ cong (DC ⌊ S ⌋) (FVTm-≃ (sty-tgt-to-term As)) ⟩
      SuppTm ⌊ S ⌋ (ty-tgt (sty-to-type As)) ∎
      where
        open ≡-Reasoning

    open Reasoning ty-setoid

label-equality-to-sub : (L M : Label-WT X S) → ap L ≈[ Γ ]l ap M → lty L ≈[ Γ ]sty lty M → label-to-sub L ≈[ Γ ]s label-to-sub M
label-equality-to-sub {S = Sing} L M [ p ] [ q ] = Ext≈ (Null≈ q) (p PHere .get)
label-equality-to-sub {S = Join S T} L M [ p ] q
  = sub-from-wedge-≈
      (↓-≈ (label-equality-to-sub (label₁ L) (label₁ M) [ p ∘ PExt ] (≈SArr (p PHere) q (p (PShift PHere)))))
      (label-equality-to-sub (label₂ L) (label₂ M) [ p ∘ PShift ] q)

≈SCoh : (S : Tree n) → {As Bs : STy (someTree S)} → As ≈[ ⌊ S ⌋ ]sty Bs → {L M : Label X S} → L ≈[ Γ ]l M → {Cs Cs′ : STy X} → Cs ≈[ Γ ]sty Cs′ → SCoh S As (L ,, Cs) ≈[ Γ ]stm SCoh S Bs (M ,, Cs′)
≈SCoh S {As} {Bs} [ p ] {L} {M} q {S⋆} {S⋆} r = [ Coh≈ p (apply-sub-eq-sub idSub (label-equality-to-sub (L ,, S⋆) (M ,, S⋆) q r)) ]
≈SCoh S {As} {Bs} p {L} {M} q {SArr s Cs t} {SArr s′ Cs′ t′} r = begin
  SCoh S As (L ,, SArr s Cs t)
    ≈⟨ reflexive≈stm (SCoh-↓ S As (L ,, SArr s Cs t)) ⟩
  SCoh (Susp S) (susp-sty As) (↓-label (L ,, SArr s Cs t) ,, Cs)
    ≈⟨ ≈SCoh (Susp S) (susp-sty-tree-≈ p) (↓-label-≈ q r) {Cs} {Cs′} (sty-base-≈ r) ⟩
  SCoh (Susp S) (susp-sty Bs)
    (↓-label (M ,, SArr s′ Cs′ t′) ,, Cs′)
    ≈˘⟨ reflexive≈stm (SCoh-↓ S Bs (M ,, SArr s′ Cs′ t′)) ⟩
  SCoh S Bs (M ,, SArr s′ Cs′ t′) ∎
  where
    open Reasoning stm-setoid-≈

≈->>= : a ≈[ ⌊ S ⌋ ]stm b → {L : Label-WT X S} → (Lty : Typing-Label Γ L) → Typing-STy Γ (lty L) → (a >>= L) ≈[ Γ ]stm (b >>= L)
≈->>= {a = a} {b = b} [ p ] {L} Lty AsTy .get = begin
  stm-to-term (a >>= L)
    ≈˘⟨ reflexive≈tm (label-to-sub-stm L a) ⟩
  stm-to-term a [ label-to-sub L ]tm
    ≈⟨ apply-sub-tm-eq (label-to-sub-Ty Lty AsTy) p ⟩
  stm-to-term b [ label-to-sub L ]tm
    ≈⟨ reflexive≈tm (label-to-sub-stm L b) ⟩
  stm-to-term (b >>= L) ∎
  where
    open Reasoning (tm-setoid-≈ _)

>>=-≈ : (a : STm (someTree S)) → {L M : Label-WT X S} → ap L ≈[ Γ ]l ap M → lty L ≈[ Γ ]sty lty M → (a >>= L) ≈[ Γ ]stm (a >>= M)
>>=-≈ a {L = L} {M = M} p q .get = begin
  stm-to-term (a >>= L)
    ≈˘⟨ reflexive≈tm (label-to-sub-stm L a) ⟩
  stm-to-term a [ label-to-sub L ]tm
    ≈⟨ apply-sub-eq-tm (stm-to-term a) (label-equality-to-sub L M p q) ⟩
  stm-to-term a [ label-to-sub M ]tm
    ≈⟨ reflexive≈tm (label-to-sub-stm M a) ⟩
  stm-to-term (a >>= M) ∎
  where
    open Reasoning (tm-setoid-≈ _)

≈-label-comp : {L M : Label (someTree T) S} → L ≈[ ⌊ T ⌋ ]l M → {N : Label-WT X T} → (Lty : Typing-Label Γ N) → Typing-STy Γ (lty N) → L ●l N ≈[ Γ ]l M ●l N
≈-label-comp p LTy AsTy .get Z = ≈->>= (p .get Z) LTy AsTy

label-comp-≈ : (L : Label (someTree T) S) → {M N : Label-WT X T} → ap M ≈[ Γ ]l ap N → lty M ≈[ Γ ]sty lty N → L ●l M ≈[ Γ ]l L ●l N
label-comp-≈ L p q .get Z = >>=-≈ (L Z) p q

>>=′-≈ : (As : STy (someTree S)) → {L M : Label-WT X S} → ap L ≈[ Γ ]l ap M → lty L ≈[ Γ ]sty lty M → As >>=′ L ≈[ Γ ]sty As >>=′ M
>>=′-≈ S⋆ p q = q
>>=′-≈ (SArr s As t) p q = ≈SArr (>>=-≈ s p q) (>>=′-≈ As p q) (>>=-≈ t p q)

>>=-Ty : {L : Label-WT X S} → Typing-STm ⌊ S ⌋ a As → Typing-Label Γ L → Typing-STy Γ (lty L) → Typing-STm Γ (a >>= L) (As >>=′ L)
>>=-Ty {a = a} {As = As} {L = L} [ aty ] Lty Ltyty .get
  = transport-typing-full (apply-sub-tm-typing aty (label-to-sub-Ty Lty Ltyty))
                          refl≃c
                          (label-to-sub-stm L a)
                          (label-to-sub-sty L As)

>>=′-Ty : {L : Label-WT X S} → Typing-STy ⌊ S ⌋ As → Typing-Label Γ L → Typing-STy Γ (lty L) → Typing-STy Γ (As >>=′ L)
>>=′-Ty {As = As} {L = L} [ Asty ] Lty Ltyty .get
  = transport-typing-ty (apply-sub-ty-typing Asty (label-to-sub-Ty Lty Ltyty))
                        refl≃c
                        (label-to-sub-sty L As)

label-comp-Ty : {L : Label-WT (someTree T) S} {M : Label-WT X T} → Typing-Label ⌊ T ⌋ L → Typing-Label Γ M → Typing-STy Γ (lty M) → Typing-Label Γ (L ●lt M)
label-comp-Ty (TySing x) MTy AsTy = TySing (>>=-Ty x MTy AsTy)
label-comp-Ty (TyJoin x LTy LTy′) MTy AsTy = TyJoin (>>=-Ty x MTy AsTy) (label-comp-Ty LTy MTy AsTy) (label-comp-Ty LTy′ MTy AsTy)

last-path-Ty : (T : Tree n) → Typing-STm ⌊ T ⌋ (SPath (last-path T)) S⋆
last-path-Ty T = [ (transport-typing (tree-last-var-Ty T) (sym≃tm (last-path-to-term T))) ]

map-sty-ext-Ty : Typing-STy ⌊ S ⌋ As → Typing-STy ⌊ Join S T ⌋ (map-sty-ext {S = S} {T = T} As)
map-sty-ext-Ty {As = S⋆} AsTy = TySArr (TySPath PHere) TySStar (TySShift (TySPath PHere))
map-sty-ext-Ty {As = SArr s As t} [ TyArr sty AsTy tty ] = TySArr (TySExt [ sty ]) (map-sty-ext-Ty [ AsTy ]) (TySExt [ tty ])

map-ext-Ty : {L : Label-WT (someTree S) U} → Typing-Label ⌊ S ⌋ L → Typing-Label ⌊ Join S T ⌋ (map-ext {T = T} L)
map-ext-Ty (TySing x) = TySing (TySExt x)
map-ext-Ty (TyJoin x Lty Mty) = TyJoin (TySExt x) (map-ext-Ty Lty) (map-ext-Ty Mty)

map-sty-shift-Ty : Typing-STy ⌊ T ⌋ As → Typing-STy ⌊ Join S T ⌋ (map-sty-shift {T = T} {S = S} As)
map-sty-shift-Ty {As = S⋆} AsTy = TySStar
map-sty-shift-Ty {As = SArr s As t} [ TyArr sty AsTy tty ] = TySArr (TySShift [ sty ]) (map-sty-shift-Ty [ AsTy ]) (TySShift [ tty ])

map-shift-Ty : {L : Label-WT (someTree T) U} → Typing-Label ⌊ T ⌋ L → Typing-Label ⌊ Join S T ⌋ (map-shift {S = S} L)
map-shift-Ty (TySing x) = TySing (TySShift x)
map-shift-Ty (TyJoin x Lty Mty) = TyJoin (TySShift x) (map-shift-Ty Lty) (map-shift-Ty Mty)

id-label-Ty : (S : Tree n) → Typing-Label ⌊ S ⌋ (id-label-wt S)
id-label-Ty Sing = TySing (TySPath PHere)
id-label-Ty (Join S T) = TyJoin (TySPath PHere) (transport-label-typing (map-ext-Ty (id-label-Ty S)) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ refl≃stm))) (transport-label-typing (map-shift-Ty (id-label-Ty T)) [ (λ P → compute-≃ refl≃stm) ] refl≃sty)

stm-sub-Ty : Typing-STm Δ a As → Typing-Sub Δ Γ σ → Typing-STm Γ (a [ σ ]stm) (As [ σ ]sty)
stm-sub-Ty {As = As} [ aty ] σty = [ TyConv (apply-sub-tm-typing aty σty) (reflexive≈ty (sym≃ty (sty-sub-to-type As _))) ]

label-sub-Ty : {L : Label-WT X S} → Typing-Label Δ L → Typing-Sub Δ Γ σ → Typing-Label Γ (L [ σ ]l)
label-sub-Ty (TySing xty) σty = TySing (stm-sub-Ty xty σty)
label-sub-Ty (TyJoin xty Lty Mty) σty = TyJoin (stm-sub-Ty xty σty) (label-sub-Ty Lty σty) (label-sub-Ty Mty σty)

to-label-Ty : (S : Tree n) → (Γ : Ctx m) → Typing-Sub ⌊ S ⌋ Γ σ → Typing-Label Γ (to-label-wt S σ)
to-label-Ty S Γ σty = label-sub-Ty (id-label-Ty S) σty

Label′-Ty : {L : Label-WT X S} → Typing-Label Γ L → Typing-STy Γ (lty L) → Typing-Label′ Γ L
Label′-Ty Lty Asty = [ label-to-sub-Ty Lty Asty ]

Label-ty : {L : Label-WT X S} → Typing-Label′ Γ L → Typing-Label Γ L
Label-ty {S = S} {Γ = Γ} {L = L} [ Lty ] = transport-label-typing (to-label-Ty S Γ Lty) (label-to-sub-to-label L) (sty-to-type-to-sty (lty L))

++t-inc-left-Ty : (S : Tree n)
                         → (T : Tree m)
                         → Typing-Label ⌊ S ++t T ⌋ (++t-inc-left S T)
++t-inc-left-Ty Sing T = TySing (TySPath PHere)
++t-inc-left-Ty (Join S₁ S₂) T
  = TyJoin (TySPath PHere)
           (transport-label-typing (map-ext-Ty (id-label-Ty S₁))
                                   [ (λ P → compute-≃ refl≃stm) ]
                                   (SArr≃ refl≃stm
                                          refl≃sty
                                          (compute-≃ (SShift≃ refl≃ (SPath≃ (sym≃p (++t-inc-left-phere S₂ T)))))))
           (transport-label-typing (map-shift-Ty (++t-inc-left-Ty S₂ T))
                                   [ (λ P → compute-≃ refl≃stm) ]
                                   refl≃sty)

++t-inc-right-Ty : (S : Tree n)
                 → (T : Tree m)
                 → Typing-Label ⌊ S ++t T ⌋ (++t-inc-right S T)
++t-inc-right-Ty Sing T = id-label-Ty T
++t-inc-right-Ty (Join S₁ S₂) T = transport-label-typing (map-shift-Ty (++t-inc-right-Ty S₂ T)) [ (λ P → compute-≃ refl≃stm) ] refl≃sty

replace-label-Ty : {L : Label-WT X S}
                 → Typing-Label Γ L
                 → Typing-STm Γ a (lty L)
                 → ap L PHere ≈[ Γ ]stm a
                 → Typing-Label Γ (replace-label (ap L) a ,, lty L)
replace-label-Ty (TySing x) aTy p = TySing aTy
replace-label-Ty (TyJoin x LTy LTy′) aTy p = TyJoin aTy (label-typing-conv LTy (≈SArr p refl≈sty refl≈stm)) LTy′

replace-label-eq : (L : Label X S)
                 → (a : STm X)
                 → a ≈[ Γ ]stm L PHere
                 → replace-label L a ≈[ Γ ]l L
replace-label-eq L a p .get PHere = p
replace-label-eq L a p .get (PExt P) = refl≈stm
replace-label-eq L a p .get (PShift P) = refl≈stm

++l-Ty : Typing-Label Γ (L ,, As)
                 → Typing-Label Γ (M ,, As)
                 → L (last-path S) ≈[ Γ ]stm M PHere
                 → Typing-Label Γ (L ++l M ,, As)
++l-Ty (TySing x) MTy p = replace-label-Ty MTy x (sym≈stm p)
++l-Ty (TyJoin {L = L} x LTy LTy′) MTy p = TyJoin x (label-typing-conv LTy (≈SArr refl≈stm refl≈sty (reflexive≈stm (sym≃stm (++l-phere (ap L ∘ PShift) _))))) (++l-Ty LTy′ MTy p)

++l′-phere : (L : Label X S)
           → (M : Label X T)
           → L (last-path S) ≈[ Γ ]stm M PHere
           → L PHere ≈[ Γ ]stm (L ++l′ M) PHere
++l′-phere {S = Sing} L M p = p
++l′-phere {S = Join S₁ S₂} L M p = refl≈stm

++l′-Ty : Typing-Label Γ (L ,, As)
        → Typing-Label Γ (M ,, As)
        → L (last-path S) ≈[ Γ ]stm M PHere
        → Typing-Label Γ (L ++l′ M ,, As)
++l′-Ty (TySing x) MTy p = MTy
++l′-Ty (TyJoin {L = L} x LTy LTy′) MTy p
  = TyJoin x (label-typing-conv LTy (≈SArr refl≈stm refl≈sty (++l′-phere (ap (label₂ L)) _ p))) (++l′-Ty LTy′ MTy p)

++l-eq : (L : Label X S)
       → (M : Label X T)
       → L (last-path S) ≈[ Γ ]stm M PHere
       → L ++l M ≈[ Γ ]l L ++l′ M
++l-eq {S = Sing} L M p = replace-label-eq M (L PHere) p
++l-eq {S = Join S₁ S₂} L M p .get PHere = refl≈stm
++l-eq {S = Join S₁ S₂} L M p .get (PExt Z) = refl≈stm
++l-eq {S = Join S₁ S₂} L M p .get (PShift Z) = ++l-eq (L ∘ PShift) M p .get Z

label-between-++t-lem : (L : Label (someTree S′) S)
                                → (M : Label (someTree T′) T)
                                → L (last-path S) ≈[ ⌊ S′ ⌋ ]stm SPath (last-path S′)
                                → M PHere ≈[ ⌊ T′ ⌋ ]stm SHere
                                → ((L ●l ++t-inc-left S′ T′) (last-path S)
                                  ≈[ ⌊ S′ ++t T′ ⌋ ]stm
                                  (M ●l ++t-inc-right S′ T′) PHere)
label-between-++t-lem {S′ = S′} {S = S} {T′ = T′} L M p q = begin
  (L ●l ++t-inc-left S′ T′) (last-path S)
    ≡⟨⟩
  (L (last-path S) >>= ++t-inc-left S′ T′)
    ≈⟨ ≈->>= p (++t-inc-left-Ty S′ T′) TySStar ⟩
  (SPath (last-path S′) >>= ++t-inc-left S′ T′)
    ≈⟨ reflexive≈stm (SPath≃ (++t-inc-phere S′ T′)) ⟩
  (SHere >>= ++t-inc-right S′ T′)
    ≈˘⟨ ≈->>= q (++t-inc-right-Ty S′ T′) TySStar ⟩
  (M PHere >>= ++t-inc-right S′ T′)
    ≡⟨⟩
  (M ●l ++t-inc-right S′ T′) PHere ∎
  where
    open Reasoning stm-setoid-≈

label-between-++t-Ty : {L : Label (someTree S′) S}
                               → {M : Label (someTree T′) T}
                               → Typing-Label ⌊ S′ ⌋ (L ,, S⋆)
                               → Typing-Label ⌊ T′ ⌋ (M ,, S⋆)
                               → L (last-path S) ≈[ ⌊ S′ ⌋ ]stm SPath (last-path S′)
                               → M PHere ≈[ ⌊ T′ ⌋ ]stm SHere
                               → Typing-Label ⌊ S′ ++t T′ ⌋ (label-between-++t L M ,, S⋆)
label-between-++t-Ty {S′ = S′} {S = S} {T′ = T′} {L = L} {M = M} LTy MTy p q
  = ++l′-Ty (label-comp-Ty LTy (++t-inc-left-Ty _ _) TySStar)
                      (label-comp-Ty MTy (++t-inc-right-Ty _ _) TySStar)
                      (label-between-++t-lem L M p q)

label-between-joins-Ty : {L : Label (someTree S′) S}
                       → {M : Label (someTree T′) T}
                       → Typing-Label ⌊ S′ ⌋ (L ,, S⋆)
                       → Typing-Label ⌊ T′ ⌋ (M ,, S⋆)
                       → M PHere ≈[ ⌊ T′ ⌋ ]stm SHere
                       → Typing-Label ⌊ Join S′ T′ ⌋ (label-between-joins L M ,, S⋆)
label-between-joins-Ty LTy MTy p = TyJoin (TySPath PHere) (label-typing-conv (map-ext-Ty LTy) (≈SArr refl≈stm refl≈sty (sym≈stm (≈SShift p)))) (map-shift-Ty MTy)

label-max-equality-to-equality : {L M : Label-WT X S} → ap L ≃lm ap M → Typing-Label Γ L → Typing-Label Γ M → ap L ≈[ Γ ]l ap M
label-max-equality-to-type-equality : {L M : Label-WT X S} → ap L ≃lm ap M → Typing-Label Γ L → Typing-Label Γ M → lty L ≈[ Γ ]sty lty M

label-max-equality-to-equality {S = Sing} [ p ] Lty Mty .get PHere = reflexive≈stm (p PHere)
label-max-equality-to-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get PHere
  = sty-src-≈ (label-max-equality-to-type-equality [ (λ Q → p (PExt Q) ⦃ inst ⦄) ] Lty Mty)
label-max-equality-to-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PExt P)
  = label-max-equality-to-equality [ (λ Q → p (PExt Q) ⦃ inst ⦄) ] Lty Mty .get P
label-max-equality-to-equality {S = Join S Sing} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PShift PHere)
  = sty-tgt-≈ (label-max-equality-to-type-equality [ (λ Q → p (PExt Q) ⦃ inst ⦄) ] Lty Mty)
label-max-equality-to-equality {S = Join S T@(Join _ _)} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′) .get (PShift P)
  = label-max-equality-to-equality [ (λ Q → p (PShift Q) ⦃ build ⦃ maximal-join-not-here Q ⦄ ⦄) ] Lty′ Mty′ .get P

label-max-equality-to-type-equality {S = Sing} [ p ] (TySing x) (TySing y) = [ (Ty-unique-≃ (p PHere .get) (x .get) (y .get)) ]
label-max-equality-to-type-equality {S = Join S T} [ p ] (TyJoin x Lty Lty′) (TyJoin y Mty Mty′)
  = sty-base-≈ (label-max-equality-to-type-equality [ (λ Q → p (PExt Q) ⦃ inst ⦄) ] Lty Mty)

label-≃-Ty : (p : S ≃′ T) → {L : Label-WT X T} → Typing-Label Γ L → Typing-Label Γ (label-wt-≃ p L)
label-≃-Ty Refl≃′ LTy = LTy
label-≃-Ty (Join≃′ p q) (TyJoin {L = L} x LTy LTy′) = TyJoin x (label-typing-conv (label-≃-Ty p LTy) (reflexive≈sty (SArr≃ refl≃stm refl≃sty (ap-≃ (refl≃l {L = ap L}) (Shift≃ refl≃ (trans≃p (Here≃ (sym≃ (≃′-to-≃ q))) (ppath-≃-≃p q PHere))))))) (label-≃-Ty q LTy′)

truncate-sty′-≈ : d ≡ d′ → As ≈[ Γ ]sty Bs → truncate-sty′ d As ≈[ Γ ]sty truncate-sty′ d′ Bs
truncate-sty′-≈ {d = zero} refl q = q
truncate-sty′-≈ {d = suc d} refl q = truncate-sty′-≈ {d = d} refl (sty-base-≈ q)

truncate-sty-≈ : d ≡ d′ → As ≈[ Γ ]sty Bs → truncate-sty d As ≈[ Γ ]sty truncate-sty d′ Bs
truncate-sty-≈ {d = d} refl q = truncate-sty′-≈ (cong (_∸ d) (sty-dim-≈ q)) q

SCoh-typing-prop : {L : Label-WT X S} → Typing-STm Γ (SCoh S As L) Bs → As >>=′ L ≈[ Γ ]sty Bs
SCoh-typing-prop {S = S} {Γ = Γ} {As = As} {L = L} [ tty ] .get = begin
  sty-to-type (As >>=′ L)
    ≈˘⟨ reflexive≈ty (label-to-sub-sty L As) ⟩
  sty-to-type As [ label-to-sub L ]ty
    ≈˘⟨ reflexive≈ty (sub-action-≃-ty (refl≃ty {A = sty-to-type As}) (id-left-unit (label-to-sub L))) ⟩
  sty-to-type As [ idSub ● label-to-sub L ]ty
    ≈˘⟨ reflexive≈ty (tm-to-ty-coh-sub ⌊ S ⌋ (sty-to-type As) idSub Γ (label-to-sub L)) ⟩
  tm-to-ty Γ (stm-to-term (SCoh S As L))
    ≈⟨ tm-to-ty-prop tty ⟩
  sty-to-type _ ∎
  where
    open Reasoning (ty-setoid-≈ _)

SCoh-Label-Ty : Typing-Tm Γ (stm-to-term (SCoh S As (L ,, S⋆))) B → Typing-Label Γ (L ,, S⋆)
SCoh-Label-Ty {L = L} aty
  = Label-ty [ (transport-typing-sub (coh-sub-ty aty) refl≃c refl≃c (id-left-unit (label-to-sub (L ,, S⋆)))) ]

sty-to-coh-Ty : {As : STy (someTree S)}
              → .⦃ _ : NonZero (sty-dim As) ⦄
              → ops-s S (DCT (FVSTm (sty-src As))) (DCT (FVSTm (sty-tgt As)))
              → Typing-STy ⌊ S ⌋ As
              → Typing-STm ⌊ S ⌋ (sty-to-coh As) As
sty-to-coh-Ty {S = S} {As = As} supp AsTy = TySConv (TySCoh S supp AsTy (id-label-Ty S) TySStar) (reflexive≈sty (>>=′-id As))

++l′-inc-left : (L : Label X S)
              → (M : Label X T)
              → (A : STy X)
              → L (last-path S) ≈[ Γ ]stm M PHere
              → (ap (++t-inc-left S T) ●l (L ++l′ M ,, A)) ≈[ Γ ]l L
++l′-inc-left {S = S} {T = T} L M A p
  = trans≈l (sym≈l (label-comp-≈ (ap (++t-inc-left S T)) (++l-eq L M p) (refl≈sty {As = A})))
            (reflexive≈l (++l-inc-left L M A))

STy-unique : Typing-STm Γ a As → Typing-STm Γ a Bs → As ≈[ Γ ]sty Bs
STy-unique [ ty1 ] [ ty2 ] .get = Ty-unique ty1 ty2

STy-unique-≃ : a ≃stm b → Typing-STm Γ a As → Typing-STm Γ b Bs → As ≈[ Γ ]sty Bs
STy-unique-≃ [ p ] [ ty1 ] [ ty2 ] .get = Ty-unique-≃ p ty1 ty2
