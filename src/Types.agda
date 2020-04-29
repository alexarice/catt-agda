{-# OPTIONS --safe --with-K #-}

module Types where

open import Ctx
open import Data.Empty
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
open import Level using (0ℓ)

private
  variable
    c : Ctx
    n : ℕ

data Ty (c : Ctx) : ℕ → Set

data Term {c : Ctx} : {n : ℕ} → Ty c n → Set

data PDB {c : Ctx} : ∀ {n} {ty : Ty c n} → Term ty → (dim : ℕ) → Set

data Ty c where
  ⋆ : Ty c 0
  _⟶_ : ∀ {n} {ty : Ty c n} → (x y : Term ty) → Ty c (suc n)

ty-base : Ty c (suc n) → Ty c n
ty-base (_⟶_ {ty = ty} x y) = ty

ty-src : (ty : Ty c (suc n)) → Term (ty-base ty)
ty-src (x ⟶ y) = x

ty-tgt : (ty : Ty c (suc n)) → Term (ty-base ty)
ty-tgt (x ⟶ y) = y

data PDB {c} where
  Base : (t : Term {c} ⋆) → PDB t 0
  AttachMax : {n : ℕ} →
              {ty : Ty c n} →
              {tm : Term ty} →
              (pd : PDB tm n) →
              (tgt : Term ty) →
              (fill : Term (tm ⟶ tgt)) →
              PDB fill (suc n)
  AttachNM : {n : ℕ} →
             {ty : Ty c n} →
             {tm : Term ty} →
             {dim : ℕ} →
             (n <‴ dim) →
             (pd : PDB tm dim) →
             (tgt : Term ty) →
             (fill : Term (tm ⟶ tgt)) →
             PDB fill dim
  Restr : {n : ℕ} →
          {ty : Ty c n} →
          {src : Term ty} →
          {tgt : Term ty} →
          {tm : Term (src ⟶ tgt)} →
          {dim : ℕ} →
          (pd : PDB tm dim) →
          PDB tgt dim

record PD (c : Ctx) (d : ℕ) : Set where
  constructor mkPD
  field
    {pd-tm} : Term {c} ⋆
    getPD : PDB pd-tm d

pdb-dim-lemma : {ty : Ty c n} → {tm : Term ty} → {dim : ℕ} → (pd : PDB tm dim) → n ≤‴ dim
pdb-dim-lemma (Base _) = ≤‴-refl
pdb-dim-lemma (AttachMax pd tgt _) = ≤‴-refl
pdb-dim-lemma (AttachNM x pd tgt _) = x
pdb-dim-lemma (Restr pd) = ≤‴-step (pdb-dim-lemma pd)

pdb-src-i< : (i : ℕ) → {n : ℕ} → {ty : Ty c n} → {tm : Term ty} → (pd : PDB tm (suc i)) → n <‴ i → PDB tm i
pdb-src-i≡ : (i : ℕ) → {ty : Ty c i} → {tm : Term ty} → (pd : PDB tm (suc i)) → Σ[ t ∈ Term ty ] PDB t i
pdb-src-i> : (i : ℕ) → {base : Ty c i} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → (pd : PDB tm (suc i)) → Σ[ t ∈ Term base ] PDB t i

pdb-src-i< i (AttachMax pd tgt fill) p = ⊥-elim (si≰‴i (≤‴-step p))
pdb-src-i< i (AttachNM x pd tgt fill) p =
  AttachNM (≤‴-step p) (pdb-src-i< i pd (≤‴-step p)) tgt fill
pdb-src-i< i (Restr pd) ≤‴-refl = Restr (proj₂ (pdb-src-i≡ i pd))
pdb-src-i< i (Restr pd) (≤‴-step p) = Restr (pdb-src-i< i pd p)

pdb-src-i≡ i (AttachNM x pd tgt fill) =
  fill , AttachNM ≤‴-refl (pdb-src-i< i pd ≤‴-refl) tgt fill
pdb-src-i≡ i (Restr pd) = pdb-src-i> i pd

pdb-src-i> i (AttachMax pd tgt fill) = -, pd
pdb-src-i> i (AttachNM ≤‴-refl pd tgt fill) = pdb-src-i≡ i pd
pdb-src-i> i (AttachNM (≤‴-step p) pd tgt fill) = ⊥-elim (si≰‴i p)
pdb-src-i> i (Restr pd) = ⊥-elim (si≰‴i (pdb-dim-lemma pd))

pd-src : {i : ℕ} → PD c (suc i) → PD c i
pd-src {_} {zero} (mkPD pdb) = mkPD (proj₂ (pdb-src-i≡ 0 pdb))
pd-src {_} {suc i} (mkPD pdb) = mkPD (pdb-src-i< (suc i) pdb (≤⇒≤‴ (s≤s z≤n)))

pdb-tgt-i≤ : (i : ℕ) → {n : ℕ} → {ty : Ty c n} → {tm : Term ty} → (pd : PDB tm (suc i)) → n ≤‴ i → PDB tm i
pdb-tgt-i> : (i : ℕ) → {base : Ty c i} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → (pd : PDB tm (suc i)) → PDB tgt i
drop : {i : ℕ} → {ty : Ty c i} → {tm : Term ty} → (pd : PDB tm i) → (nt : Term ty) → PDB nt i

pdb-tgt-i≤ i (AttachMax pd tgt fill) p = ⊥-elim (si≰‴i p)
pdb-tgt-i≤ i (AttachNM x pd tgt fill) p = AttachNM p (pdb-tgt-i≤ i pd (≤‴-step p)) tgt fill
pdb-tgt-i≤ i (Restr pd) ≤‴-refl = pdb-tgt-i> i pd
pdb-tgt-i≤ i (Restr pd) (≤‴-step p) = Restr (pdb-tgt-i≤ i pd p)

pdb-tgt-i> i (AttachMax pd tgt fill) = drop pd tgt
pdb-tgt-i> i (AttachNM ≤‴-refl pd tgt fill) = drop (pdb-tgt-i≤ i pd ≤‴-refl) tgt
pdb-tgt-i> i (AttachNM (≤‴-step p) pd tgt fill) = ⊥-elim (si≰‴i p)
pdb-tgt-i> i (Restr pd) = ⊥-elim (si≰‴i (pdb-dim-lemma pd))

drop (Base _) nt = Base nt
drop (AttachMax pd tgt _) nt = AttachMax pd tgt nt
drop (AttachNM x pd tgt _) nt = AttachNM x pd tgt nt
drop (Restr pd) nt = ⊥-elim (si≰‴i (pdb-dim-lemma pd))

pd-tgt : {i : ℕ} → PD c (suc i) → PD c i
pd-tgt {_} {i} (mkPD pdb) = mkPD (pdb-tgt-i≤ i pdb (≤⇒≤‴ z≤n))

record PDB′ (c : Ctx) : Set where
  constructor mkPDB′
  field
    {pdb-n} : ℕ
    {pdb-ty} : Ty c pdb-n
    {pdb-tm} : Term pdb-ty
    {pdb-d} : ℕ
    getPdb : PDB pdb-tm pdb-d

open PDB′

infix 4 _<pb_
data _<pb_ {c : Ctx} : PDB′ c → PDB′ c → Set where
  AMStep : {n : ℕ} →
           {ty : Ty c n} →
           {tm : Term ty} →
           (pd : PDB tm n) →
           (tgt : Term ty) →
           (fill : Term (tm ⟶ tgt)) →
           mkPDB′ pd <pb mkPDB′ (AttachMax pd tgt fill)
  ANStep : {n : ℕ} →
           {ty : Ty c n} →
           {tm : Term ty} →
           {dim : ℕ} →
           (p : n <‴ dim) →
           (pd : PDB tm dim) →
           (tgt : Term ty) →
           (fill : Term (tm ⟶ tgt)) →
           mkPDB′ pd <pb mkPDB′ (AttachNM p pd tgt fill)
  RStep : {n : ℕ} →
          {ty : Ty c n} →
          {src : Term ty} →
          {tgt : Term ty} →
          {tm : Term (src ⟶ tgt)} →
          {dim : ℕ} →
          (pd : PDB tm dim) →
          mkPDB′ pd <pb mkPDB′ (Restr pd)

wf : (c : Ctx) → WellFounded (_<pb_ {c})
wf c (mkPDB′ pdb) = go pdb
  where
    transport : ∀ {x₁ x₂ y : PDB′ c} → x₁ <pb y → x₂ <pb y → Acc _<pb_ x₁ → Acc _<pb_ x₂
    transport (AMStep pd tgt fill) (AMStep .pd .tgt .fill) a = a
    transport (ANStep p pd tgt fill) (ANStep .p .pd .tgt .fill) a = a
    transport (RStep pd) (RStep .pd) a = a

    lem : ∀ {x y : PDB′ c} → x <pb y → Acc _<pb_ x → Acc _<pb_ y
    lem p₁ a = acc (λ x₂ p₂ → transport p₁ p₂ a)

    go : {ty : Ty c n} → {tm : Term ty} → {d : ℕ} → (pdb : PDB tm d) → Acc _<pb_ (mkPDB′ pdb)
    go (Base _) = acc (λ y ())
    go (AttachMax pdb tgt fill) = lem (AMStep pdb tgt fill) (go pdb)
    go (AttachNM x pdb tgt fill) = lem (ANStep x pdb tgt fill) (go pdb)
    go (Restr pdb) = lem (RStep pdb) (go pdb)

open TransitiveClosure

infix 4 _<pb⁺_

_<pb⁺_ : {c : Ctx} → PDB′ c → PDB′ c → Set
_<pb⁺_ {c} = _<⁺_ (_<pb_ {c})

wf⁺ : (c : Ctx) → WellFounded (_<pb⁺_ {c})
wf⁺ c = wellFounded _<pb_ (wf c)

higher : PDB′ c → Set
higher (mkPDB′ {zero} _) = ⊥
higher (mkPDB′ {suc n} _) = ⊤

record parsable-pd {n} {d} {base : Ty c n}
                   {src tgt : Term base}
                   {tm : Term (src ⟶ tgt)}
                   (pd : PDB tm d) : Set where
  constructor parse
  field
    parsed : NECtx
    {nt} : Term base
    {dim} : ℕ
    npd : PDB nt dim
    wfproof : mkPDB′ npd <pb⁺ mkPDB′ pd

open parsable-pd

parsable-helper : (pdb : PDB′ c) → (higher pdb) → Set
parsable-helper (mkPDB′ {suc n} {x ⟶ y} pdb) tt = parsable-pd pdb

parsable : PDB′ c → Set
parsable pdb = (h : higher pdb) → parsable-helper pdb h

ctx-parser : (pd : PDB′ c) → parsable pd
ctx-parser {c} = All.wfRec (wf⁺ c) 0ℓ parsable go
  where
    go : ∀ x → WfRec _<pb⁺_ parsable x → parsable x
    go (mkPDB′ pd@(AttachMax pdb tgt fill)) rec tt =
      parse singleton-ctx-ne pdb [ AMStep pdb tgt fill ]
    go (mkPDB′ pd@(AttachNM x pdb tgt fill)) rec tt =
      parse singleton-ctx-ne pdb [ ANStep x pdb tgt fill ]
    go (mkPDB′ {suc n} {x ⟶ y} pd@(Restr pdb)) rec tt =
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
lower (mkPDB′ {zero} pdb) = ⊤
lower (mkPDB′ {suc n} pdb) = ⊥

parsable-base : PDB′ c → Set
parsable-base pdb = (lower pdb) → NECtx

pd-ctx : ∀ {i} → PD c i → NECtx
pd-ctx {c} (mkPD pdb) = helper (mkPDB′ pdb) tt
  where
    helper : (pdb : PDB′ c) → parsable-base pdb
    helper = All.wfRec (wf⁺ c) 0ℓ parsable-base go
      where
        go : ∀ x → WfRec (_<pb⁺_ {c}) parsable-base x → parsable-base x
        go (mkPDB′ (Base _)) rec tt = singleton-ctx-ne
        go (mkPDB′ {zero} (Restr pdb)) rec tt = attach-ctx-ne (continue tt) (proj₁ (parsed parse-inner))
          where
            parse-inner : parsable-pd pdb
            parse-inner = ctx-parser (mkPDB′ pdb) tt

            continuation : PDB′ c
            continuation = mkPDB′ (npd parse-inner)

            continuation<pb : continuation <pb⁺ mkPDB′ (Restr pdb)
            continuation<pb = trans (wfproof parse-inner) [ RStep pdb ]

            continue : parsable-base continuation
            continue = rec continuation continuation<pb



purety-to-ty : PureTy c n → Ty c n

data Term {c} where
  Var : ∀ {n} → (ty : PureTy c n) → Fin (retrieve-size ty) → Term (purety-to-ty ty)

purety-to-ty ⋆P = ⋆
purety-to-ty (_⟶P_ {t = t} x y) = Var t x ⟶ Var t y
