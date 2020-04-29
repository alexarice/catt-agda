{-# OPTIONS --safe --without-K #-}

module Types where

open import Ctx
open import Data.Nat
open import Data.Nat.Properties
open import NatProperties
open import Data.Fin using (Fin)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty

private
  variable
    c : Ctx
    n : ℕ

data Ty (c : Ctx) : ℕ → Set

data Term {c : Ctx} : {n : ℕ} → Ty c n → Set

data PDB {c : Ctx} : ∀ {n} {ty : Ty c n} → Term ty → Set

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
  Base : (t : Term {c} ⋆) → PDB t
  Attach : {n : ℕ} →
           {ty : Ty c n} →
           {tm : Term ty} →
           (pd : PDB tm) →
           (tgt : Term ty) →
           (fill : Term (tm ⟶ tgt)) →
           PDB fill
  Restr : {n : ℕ} →
          {ty : Ty c n} →
          {src : Term ty} →
          {tgt : Term ty} →
          {tm : Term (src ⟶ tgt)} →
          (pd : PDB tm) →
          PDB tgt

PD : Ctx → Set
PD c = Σ[ t ∈ Term {c} ⋆ ] PDB t

ty-dim : Ty c n → ℕ
ty-dim ⋆ = 0
ty-dim (_⟶_ {ty = ty} x y) = suc (ty-dim ty)

tm-dim : {ty : Ty c n} → Term ty → ℕ
tm-dim {ty = ty} _ = ty-dim ty

pdb-dim : {ty : Ty c n} → {tm : Term ty} → PDB tm -> ℕ
pdb-dim (Base _) = 0
pdb-dim {c} {n} (Attach pd tgt fill) = pdb-dim pd ⊔ n
pdb-dim (Restr pd) = pdb-dim pd

pd-dim : PD c → ℕ
pd-dim (_ , p) = pdb-dim p

pdb-dim-lemma : {ty : Ty c n} → {tm : Term ty} → (pd : PDB tm) → n ≤ pdb-dim pd
pdb-dim-lemma (Base _) = ≤-refl
pdb-dim-lemma (Attach pd tgt _) = n≤m⊔n (pdb-dim pd) (suc _)
pdb-dim-lemma (Restr pd) = ≤-trans (n≤1+n _) (pdb-dim-lemma pd)

pdb-src-i< : (i : ℕ) → {ty : Ty c n} → {tm : Term ty} → (pd : PDB tm) → pdb-dim pd ≤ suc i → n <‴ i → PDB tm

pdb-src-i≡ : (i : ℕ) → {ty : Ty c n} → {tm : Term ty} → (pd : PDB tm) → pdb-dim pd ≤ suc i → n ≡ i → Σ[ t ∈ Term ty ] PDB t

pdb-src-i> : (i : ℕ) → {base : Ty c n} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → (pd : PDB tm) → pdb-dim pd ≤ suc i → suc n >‴ i → Σ[ t ∈ Term base ] PDB t

pdb-src-i< i (Base x) d p = Base x
pdb-src-i< i (Attach pd tgt fill) d p =
  Attach (pdb-src-i< i pd (m⊔n≤o⇒m≤o (pdb-dim pd) _ d) (≤‴-step p)) tgt fill
pdb-src-i< i (Restr {n} {ty} {src} {tgt} {tm} pd) d p = γ
  where
    go : Dec (suc n <‴ i) → PDB tgt
    go (yes q) = Restr (pdb-src-i< i pd d q)
    go (no q) = Restr (proj₂ (pdb-src-i≡ i pd d (¬<‴∧≤‴⇒≡ q p)))

    γ : PDB tgt
    γ = go (suc n <‴? i)

pdb-src-i≡ i (Base x) d p = x , (Base x)
pdb-src-i≡ i (Attach pd tgt fill) d refl =
  fill , (Attach (pdb-src-i< i pd (m⊔n≤o⇒m≤o (pdb-dim pd) _ d) ≤‴-refl) tgt fill)
pdb-src-i≡ i (Restr {n} {ty} {src} {tgt} {tm} pd) d refl = pdb-src-i> i pd d ≤‴-refl

pdb-src-i> {c} {n} i (Attach pd tgt fill) d p = pdb-src-i≡ i pd (m⊔n≤o⇒m≤o (pdb-dim pd) _ d) (≤-antisym (≤-pred (m⊔n≤o⇒n≤o (pdb-dim pd) (suc n) d)) (≤-pred (≤‴⇒≤ p)))
pdb-src-i> i (Restr pd) d p = ⊥-elim (≤⇒≯ (≤-trans (pdb-dim-lemma pd) d) (s≤s (≤‴⇒≤ p)))

pd-src : PD c → Maybe (PD c)
pd-src (_ , pdb) = {!!}

purety-to-ty : PureTy c n → Ty c n

data Term {c} where
  Var : ∀ {n} → (ty : PureTy c n) → Fin (retrieve-size ty) → Term (purety-to-ty ty)

purety-to-ty ⋆P = ⋆
purety-to-ty (_⟶P_ {t = t} x y) = Var t x ⟶ Var t y
