{-# OPTIONS --safe --with-K #-}

module Types where

open import Ctx
open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import NatProperties
open import Relation.Nullary

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
          {dim : ℕ}
          (pd : PDB tm dim) →
          PDB tgt dim

PD : Ctx → ℕ → Set
PD c dim = Σ[ t ∈ Term {c} ⋆ ] PDB t dim

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
pd-src {_} {zero} (_ , pdb) = pdb-src-i≡ 0 pdb
pd-src {_} {suc i} (_ , pdb) = -, pdb-src-i< (suc i) pdb (≤⇒≤‴ (s≤s z≤n))

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
pd-tgt {_} {i} = map₂ (λ pdb → pdb-tgt-i≤ i pdb (≤⇒≤‴ z≤n))

purety-to-ty : PureTy c n → Ty c n

data Term {c} where
  Var : ∀ {n} → (ty : PureTy c n) → Fin (retrieve-size ty) → Term (purety-to-ty ty)

purety-to-ty ⋆P = ⋆
purety-to-ty (_⟶P_ {t = t} x y) = Var t x ⟶ Var t y
