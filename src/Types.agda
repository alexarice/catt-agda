{-# OPTIONS --safe --without-K #-}

module Types where

open import Ctx
open import Data.Empty
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit
open import NatProperties
open import Relation.Nullary
open import Function.Base
open import Induction.WellFounded
open import Induction
open import Data.Container.Core hiding (⟪_⟫)
open import Data.Container.Membership using (_∈_)
open import Data.Container.Relation.Unary.All using (□)
open import Level using (0ℓ)

private
  variable
    c : Ctx

data Ty (c : Ctx) : Set

data Term {c : Ctx} : Ty c → Set

data PDB {c : Ctx} : {ty : Ty c} → Term ty → (submax : ℕ) → Set

data Ty c where
  ⋆ : Ty c
  _⟶_ : {ty : Ty c} → (x y : Term ty) → Ty c

data PDB {c} where
  Base : (t : Term {c} ⋆) → PDB t 0
  AttachMax : {ty : Ty c} →
              {tm : Term ty} →
              (pd : PDB tm 0) →
              (tgt : Term ty) →
              (fill : Term (tm ⟶ tgt)) →
              PDB fill 0
  AttachNM : {ty : Ty c} →
             {tm : Term ty} →
             {submax : ℕ} →
             (pd : PDB tm (suc submax)) →
             (tgt : Term ty) →
             (fill : Term (tm ⟶ tgt)) →
             PDB fill submax
  Restr : {ty : Ty c} →
          {src : Term ty} →
          {tgt : Term ty} →
          {tm : Term (src ⟶ tgt)} →
          {submax : ℕ} →
          (pd : PDB tm submax) →
          PDB tgt (suc submax)

record PD (c : Ctx) (d : ℕ) : Set where
  inductive
  constructor mkPD
  field
    {pd-tm} : Term {c} ⋆
    getPD : PDB pd-tm d

pdb-src-i< : {submax : ℕ} → {ty : Ty c} → {tm : Term ty} → (pd : PDB tm (suc (suc submax))) → PDB tm (suc submax)
pdb-src-i≡ : {ty : Ty c} → {tm : Term ty} → (pd : PDB tm 1) → Σ[ t ∈ Term ty ] PDB t 0
pdb-src-i> : {base : Ty c} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → (pd : PDB tm 0) → Σ[ t ∈ Term base ] PDB t 0

pdb-src-i< (AttachNM pd tgt fill) = AttachNM (pdb-src-i< pd) tgt fill
pdb-src-i< {_} {zero} (Restr pd) = Restr (proj₂ (pdb-src-i≡ pd))
pdb-src-i< {_} {suc submax} (Restr pd) = Restr (pdb-src-i< pd)

pdb-src-i≡ (AttachNM pd tgt fill) = -, AttachNM (pdb-src-i< pd) tgt fill
pdb-src-i≡ (Restr pd) = pdb-src-i> pd

pdb-src-i> (AttachMax pd tgt fill) = -, pd
pdb-src-i> (AttachNM pd tgt fill) = pdb-src-i≡ pd

pd-src : {dim : ℕ} → PD c (suc dim) → PD c dim
pd-src {_} {zero} (mkPD pdb) = mkPD (proj₂ (pdb-src-i≡ pdb))
pd-src {_} {suc i} (mkPD pdb) = mkPD (pdb-src-i< pdb)

pdb-tgt-i≤ : {submax : ℕ} → {ty : Ty c} → {tm : Term ty} → (pd : PDB tm (suc submax)) → PDB tm submax
pdb-tgt-i> : {base : Ty c} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → (pd : PDB tm 0) → PDB tgt 0
drop-pd : {ty : Ty c} → {tm : Term ty} → (pd : PDB tm 0) → (nt : Term ty) → PDB nt 0

pdb-tgt-i≤ (AttachNM pd tgt fill) = AttachNM (pdb-tgt-i≤ pd) tgt fill
pdb-tgt-i≤ {_} {zero} (Restr pd) = pdb-tgt-i> pd
pdb-tgt-i≤ {_} {suc _} (Restr pd) = Restr (pdb-tgt-i≤ pd)

pdb-tgt-i> (AttachMax pd tgt fill) = drop-pd pd tgt
pdb-tgt-i> (AttachNM pd tgt fill) = drop-pd (pdb-tgt-i≤ pd) tgt

drop-pd (Base _) nt = Base nt
drop-pd (AttachMax pd tgt _) nt = AttachMax pd tgt nt
drop-pd (AttachNM pd tgt _) nt = AttachNM pd tgt nt

-- pdb-tgt-i≤ i (AttachMax pd tgt fill) p = ⊥-elim (si≰‴i p)
-- pdb-tgt-i≤ i (AttachNM x pd tgt fill) p = AttachNM p (pdb-tgt-i≤ i pd (≤‴-step p)) tgt fill
-- pdb-tgt-i≤ i (Restr pd) ≤‴-refl = pdb-tgt-i> i pd
-- pdb-tgt-i≤ i (Restr pd) (≤‴-step p) = Restr (pdb-tgt-i≤ i pd p)

-- pdb-tgt-i> i (AttachMax pd tgt fill) = drop-pd pd tgt
-- pdb-tgt-i> i (AttachNM ≤‴-refl pd tgt fill) = drop-pd (pdb-tgt-i≤ i pd ≤‴-refl) tgt
-- pdb-tgt-i> i (AttachNM (≤‴-step p) pd tgt fill) = ⊥-elim (si≰‴i p)
-- pdb-tgt-i> i (Restr pd) = ⊥-elim (si≰‴i (pdb-dim-lemma pd))

-- drop-pd (Base _) nt = Base nt
-- drop-pd (AttachMax pd tgt _) nt = AttachMax pd tgt nt
-- drop-pd (AttachNM x pd tgt _) nt = AttachNM x pd tgt nt
-- drop-pd (Restr pd) nt = ⊥-elim (si≰‴i (pdb-dim-lemma pd))

pd-tgt : {dim : ℕ} → PD c (suc dim) → PD c dim
pd-tgt {_} {i} (mkPD pdb) = mkPD (pdb-tgt-i≤ pdb)

record PDB′ (c : Ctx) : Set where
  inductive
  constructor mkPDB′
  field
    {pdb-ty} : Ty c
    {pdb-tm} : Term pdb-ty
    {pdb-submax} : ℕ
    getPdb : PDB pdb-tm pdb-submax

open PDB′

infix 4 _<pb_
data _<pb_ {c : Ctx} : PDB′ c → PDB′ c → Set where
  AMStep : {ty : Ty c} →
           {tm : Term ty} →
           (pd : PDB tm 0) →
           (tgt : Term ty) →
           (fill : Term (tm ⟶ tgt)) →
           mkPDB′ pd <pb mkPDB′ (AttachMax pd tgt fill)
  ANStep : {ty : Ty c} →
           {tm : Term ty} →
           {submax : ℕ} →
           (pd : PDB tm (suc submax)) →
           (tgt : Term ty) →
           (fill : Term (tm ⟶ tgt)) →
           mkPDB′ pd <pb mkPDB′ (AttachNM pd tgt fill)
  RStep : {ty : Ty c} →
          {src : Term ty} →
          {tgt : Term ty} →
          {tm : Term (src ⟶ tgt)} →
          {submax : ℕ} →
          (pd : PDB tm submax) →
          mkPDB′ pd <pb mkPDB′ (Restr pd)

wf : (c : Ctx) → WellFounded (_<pb_ {c})
wf c (mkPDB′ pdb) = go pdb
  where
    transport : ∀ {x₁ x₂ y : PDB′ c} → x₁ <pb y → x₂ <pb y → Acc _<pb_ x₁ → Acc _<pb_ x₂
    transport (AMStep pd tgt fill) (AMStep .pd .tgt .fill) a = a
    transport (ANStep pd tgt fill) (ANStep .pd .tgt .fill) a = a
    transport (RStep pd) (RStep .pd) a = a

    lem : ∀ {x y : PDB′ c} → x <pb y → Acc _<pb_ x → Acc _<pb_ y
    lem p₁ a = acc (λ x₂ p₂ → transport p₁ p₂ a)

    go : {ty : Ty c} → {tm : Term ty} → {d : ℕ} → (pdb : PDB tm d) → Acc _<pb_ (mkPDB′ pdb)
    go (Base _) = acc (λ y ())
    go (AttachMax pdb tgt fill) = lem (AMStep pdb tgt fill) (go pdb)
    go (AttachNM pdb tgt fill) = lem (ANStep pdb tgt fill) (go pdb)
    go (Restr pdb) = lem (RStep pdb) (go pdb)

open TransitiveClosure

infix 4 _<pb⁺_

_<pb⁺_ : {c : Ctx} → PDB′ c → PDB′ c → Set
_<pb⁺_ {c} = _<⁺_ (_<pb_ {c})

wf⁺ : (c : Ctx) → WellFounded (_<pb⁺_ {c})
wf⁺ c = wellFounded _<pb_ (wf c)

higher : PDB′ c → Set
higher (mkPDB′ {⋆} _) = ⊥
higher (mkPDB′ {x ⟶ y} _) = ⊤

record parsable-pd {submax} {base : Ty c}
                   {src tgt : Term base}
                   {tm : Term (src ⟶ tgt)}
                   (pd : PDB tm submax) : Set where
  inductive
  constructor parse
  field
    parsed : NECtx
    {nt} : Term base
    {dim} : ℕ
    npd : PDB nt dim
    wfproof : mkPDB′ npd <pb⁺ mkPDB′ pd

open parsable-pd

parsable-helper : (pdb : PDB′ c) → (higher pdb) → Set
parsable-helper (mkPDB′ {x ⟶ y} pdb) tt = parsable-pd pdb

parsable : PDB′ c → Set
parsable pdb = (h : higher pdb) → parsable-helper pdb h

ctx-parser : (pd : PDB′ c) → parsable pd
ctx-parser {c} = All.wfRec (wf⁺ c) 0ℓ parsable go
  where
    go : ∀ x → WfRec _<pb⁺_ parsable x → parsable x
    go (mkPDB′ pd@(AttachMax pdb tgt fill)) rec tt =
      parse singleton-ctx-ne pdb [ AMStep pdb tgt fill ]
    go (mkPDB′ pd@(AttachNM pdb tgt fill)) rec tt =
      parse singleton-ctx-ne pdb [ ANStep pdb tgt fill ]
    go (mkPDB′ {x ⟶ y} pd@(Restr pdb)) rec tt =
      parse (attach-ctx-ne (parsed continue) (proj₁ (parsed continue))) (npd continue) (trans (wfproof continue) continuation<pb)
      where
        parse-inner : parsable-pd pdb
        parse-inner = rec (mkPDB′ pdb) [ RStep pdb ] tt

        continuation : PDB (nt parse-inner) (dim parse-inner)
        continuation = npd parse-inner

        continuation<pb : mkPDB′ continuation <pb⁺ mkPDB′ (Restr pdb)
        continuation<pb = trans (wfproof parse-inner) [ RStep pdb ]

        continue : parsable-pd continuation
        continue = rec (mkPDB′ continuation) continuation<pb tt

lower : PDB′ c → Set
lower (mkPDB′ {⋆} pdb) = ⊤
lower (mkPDB′ {x ⟶ y} pdb) = ⊥

parsable-base : PDB′ c → Set
parsable-base pdb = (lower pdb) → NECtx

pd-ctx : ∀ {i} → PD c i → Ctx
pd-ctx {c} (mkPD pdb) = proj₁ (helper (mkPDB′ pdb) tt)
  where
    helper : (pdb : PDB′ c) → parsable-base pdb
    helper = All.wfRec (wf⁺ c) 0ℓ parsable-base go
      where
        go : ∀ x → WfRec (_<pb⁺_ {c}) parsable-base x → parsable-base x
        go (mkPDB′ (Base _)) rec tt = singleton-ctx-ne
        go (mkPDB′ {⋆} (Restr pdb)) rec tt = attach-ctx-ne (continue tt) (proj₁ (parsed parse-inner))
          where
            parse-inner : parsable-pd pdb
            parse-inner = ctx-parser (mkPDB′ pdb) tt

            continuation : PDB′ c
            continuation = mkPDB′ (npd parse-inner)

            continuation<pb : continuation <pb⁺ mkPDB′ (Restr pdb)
            continuation<pb = trans (wfproof parse-inner) [ RStep pdb ]

            continue : parsable-base continuation
            continue = rec continuation continuation<pb

record CtxSubstitution (c d : Ctx) (ty : Ty d) : Set where
  inductive
  field
    ⟪_⟫ : Fin (c .size) → Term ty
    arrSub : (s t : Fin (c .size)) → CtxSubstitution (arr c s t) d (⟪ s ⟫ ⟶ ⟪ t ⟫)

pd-ctx-sub : ∀ {i} → (pd : PD c i) → CtxSubstitution (pd-ctx pd) c ⋆
pd-ctx-sub = {!!}

mapType : {c d : Ctx} → CtxSubstitution c d ⋆ → Ty c → Ty d
mapType = {!!}

data TermShape : Set where
  V : TermShape
  CH : TermShape → TermShape → TermShape
  CM : TermShape → TermShape → TermShape

term-container : Container 0ℓ 0ℓ
term-container .Shape = TermShape
term-container .Position V = ⊤
term-container .Position (CH _ _) = Bool
term-container .Position (CM _ _) = Bool

FV : {ty : Ty c} → Term ty → ⟦ term-container ⟧ (CtxIndex c)

IsComplete : {ty : Ty c} → Term ty → Set
IsComplete tm = ∀ i → i ∈ FV tm

purety-to-ty : (p : PureTy c) → Ty c

data Term {c} where
  Var : (ty : PureTy c) → Fin (retrieve-size ty) → Term (purety-to-ty ty)
  -- Coh : {d : ℕ} → (pd : PD c d) → {n : ℕ} → {ty : Ty (pd-ctx pd) n} (s t : Term ty) → (sc : IsComplete s) → (tc : IsComplete t) → Term (mapType (pd-ctx-sub pd) ty)

purety-to-ty ⋆P = ⋆
purety-to-ty (_⟶P_ {t = t} x y) = Var t x ⟶ Var t y

FV t = {!!}
