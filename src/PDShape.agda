{-# OPTIONS --safe --without-K #-}

module PDShape where

open import Data.Nat
open import Induction.WellFounded
open import Ctx
open import Data.Product

data PDShape : (lev submax : ℕ) → Set where
  BaseS : PDShape 0 0
  AttachMaxS : ∀ {lev} → PDShape lev 0 → PDShape (suc lev) 0
  AttachNMS : ∀ {lev submax} → PDShape lev (suc submax) → PDShape (suc lev) submax
  RestrS : ∀ {lev submax} → PDShape (suc lev) submax → PDShape lev (suc submax)

private
  variable
    submax : ℕ
    lev : ℕ


pds-bd-i≤ : PDShape lev (suc submax) → PDShape lev submax
pds-bd-i> : PDShape (suc lev) 0 → PDShape lev 0

pds-bd-i≤ (AttachNMS pds) = AttachNMS (pds-bd-i≤ pds)
pds-bd-i≤ {_} {zero} (RestrS pds) = pds-bd-i> pds
pds-bd-i≤ {_} {suc submax} (RestrS pds) = RestrS (pds-bd-i≤ pds)

pds-bd-i> (AttachMaxS pds) = pds
pds-bd-i> (AttachNMS pds) = pds-bd-i≤ pds

record PDS : Set where
  constructor mkPDS
  field
    {pds-lev} : ℕ
    {pds-submax} : ℕ
    getPDS : PDShape pds-lev pds-submax

open PDS

infix 4 _<ps_

data _<ps_ : PDS → PDS → Set where
  AMStep : {lev : ℕ} →
           (pds : PDShape lev 0) →
           mkPDS pds <ps mkPDS (AttachMaxS pds)
  ANStep : {lev : ℕ} →
           {submax : ℕ} →
           (pds : PDShape lev (suc submax)) →
           mkPDS pds <ps mkPDS (AttachNMS pds)
  RStep : {lev : ℕ} →
          {submax : ℕ} →
          (pds : PDShape (suc lev) submax) →
          mkPDS pds <ps mkPDS (RestrS pds)

wf : WellFounded _<ps_
wf (mkPDS pds) = go pds
  where
    transport : ∀ {x₁ x₂ y : PDS} → x₁ <ps y → x₂ <ps y → Acc _<ps_ x₁ → Acc _<ps_ x₂
    transport (AMStep pds) (AMStep .pds) a = a
    transport (ANStep pds) (ANStep .pds) a = a
    transport (RStep pds) (RStep .pds) a = a

    lem : ∀ {x y : PDS} → x <ps y → Acc _<ps_ x → Acc _<ps_ y
    lem p₁ a = acc (λ z p₂ → transport p₁ p₂ a)

    go : (pds : PDShape lev submax) → Acc _<ps_ (mkPDS pds)
    go BaseS = acc (λ y ())
    go (AttachMaxS pds) = lem (AMStep pds) (go pds)
    go (AttachNMS pds) = lem (ANStep pds) (go pds)
    go (RestrS pds) = lem (RStep pds) (go pds)

open TransitiveClosure

infix 4 _<ps⁺_

_<ps⁺_ : PDS → PDS → Set
_<ps⁺_ = _<⁺_ (_<ps_)

wf⁺ : WellFounded _<ps⁺_
wf⁺ = wellFounded _<ps_ wf

data Parsable : PDS → Set where
  ParseHigher : NECtx →
                {lev orig-sm submax : ℕ} →
                (rest : PDShape lev submax) →
                {orig : PDShape (suc lev) orig-sm} →
                mkPDS rest <ps⁺ mkPDS orig →
                Parsable (mkPDS orig)
  ParseLower : NECtx →
               {submax : ℕ} →
               {orig : PDShape 0 submax} →
               Parsable (mkPDS orig)

ctx-parser : (pds : PDS) → Parsable pds
ctx-parser = All.wfRec wf⁺ _ Parsable go
  where
    go : ∀ x → WfRec _<ps⁺_ Parsable x → Parsable x
    go (mkPDS BaseS) rec = ParseLower singleton-ctx-ne
    go (mkPDS (AttachMaxS pds)) rec = ParseHigher singleton-ctx-ne pds [ AMStep pds ]
    go (mkPDS (AttachNMS pds)) rec = ParseHigher singleton-ctx-ne pds [ ANStep pds ]
    go (mkPDS (RestrS pds)) rec with rec (mkPDS pds) [ RStep pds ]
    ... | ParseHigher ctx c p₁ with trans p₁ [ RStep pds ]
    ...   | lem with rec (mkPDS c) lem
    ...     | ParseHigher ctx-base rest p₂ =
      ParseHigher (attach-ctx-ne ctx-base (proj₁ ctx)) rest (trans p₂ lem)
    ...     | ParseLower ctx-base = ParseLower (attach-ctx-ne ctx-base (proj₁ ctx))

pds-ctx : {dim : ℕ} → PDShape 0 dim → Ctx
pds-ctx pds with ctx-parser (mkPDS pds)
... | ParseLower ctx = proj₁ ctx
