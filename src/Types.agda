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

open import PDShape

private
  variable
    c : Ctx

data Ty (c : Ctx) : Set

data Term {c : Ctx} : Ty c → Set

data Ty c where
  ⋆ : Ty c
  _⟶_ : {ty : Ty c} → (x y : Term ty) → Ty c

ty-dim : Ty c → ℕ
ty-dim ⋆ = 0
ty-dim (_⟶_ {ty = ty} x y) = suc (ty-dim ty)

data PDB {c : Ctx} : {ty : Ty c} → Term ty → {submax : ℕ} → PDShape (ty-dim ty) submax → Set

data PDB {c} where
  Base : (t : Term {c} ⋆) → PDB t BaseS
  AttachMax : {ty : Ty c} →
              {tm : Term ty} →
              {pds : PDShape (ty-dim ty) 0} →
              (pd : PDB tm pds) →
              (tgt : Term ty) →
              (fill : Term (tm ⟶ tgt)) →
              PDB fill (AttachMaxS pds)
  AttachNM : {ty : Ty c} →
             {tm : Term ty} →
             {submax : ℕ} →
             {pds : PDShape (ty-dim ty) (suc submax)} →
             (pd : PDB tm pds) →
             (tgt : Term ty) →
             (fill : Term (tm ⟶ tgt)) →
             PDB fill (AttachNMS pds)
  Restr : {ty : Ty c} →
          {src : Term ty} →
          {tgt : Term ty} →
          {tm : Term (src ⟶ tgt)} →
          {submax : ℕ} →
          {pds : PDShape (suc (ty-dim ty)) submax} →
          (pd : PDB tm pds) →
          PDB tgt (RestrS pds)

record PD (c : Ctx) {d : ℕ} (pds : PDShape 0 d) : Set where
  inductive
  constructor mkPD
  field
    {pd-tm} : Term {c} ⋆
    getPD : PDB pd-tm pds

pdb-src-i< : {submax : ℕ} → {ty : Ty c} → {tm : Term ty} → {pds : PDShape (ty-dim ty) (suc (suc submax))} → (pd : PDB tm pds) → PDB tm (pds-bd-i≤ pds)
pdb-src-i≡ : {ty : Ty c} → {tm : Term ty} → {pds : PDShape (ty-dim ty) 1} (pd : PDB tm pds) → Σ[ t ∈ Term ty ] PDB t (pds-bd-i≤ pds)
pdb-src-i> : {base : Ty c} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → {pds : PDShape (suc (ty-dim base)) 0} → (pd : PDB tm pds) → Σ[ t ∈ Term base ] PDB t (pds-bd-i> pds)

pdb-src-i< (AttachNM pd tgt fill) = AttachNM (pdb-src-i< pd) tgt fill
pdb-src-i< {_} {zero} (Restr pd) = Restr (proj₂ (pdb-src-i≡ pd))
pdb-src-i< {_} {suc submax} (Restr pd) = Restr (pdb-src-i< pd)

pdb-src-i≡ (AttachNM pd tgt fill) = -, AttachNM (pdb-src-i< pd) tgt fill
pdb-src-i≡ (Restr pd) = pdb-src-i> pd

pdb-src-i> (AttachMax pd tgt fill) = -, pd
pdb-src-i> (AttachNM pd tgt fill) = pdb-src-i≡ pd

pd-src : {dim : ℕ} → {pds : PDShape 0 (suc dim)} → PD c pds → PD c (pds-bd-i≤ pds)
pd-src {_} {zero} (mkPD pdb) = mkPD (proj₂ (pdb-src-i≡ pdb))
pd-src {_} {suc i} (mkPD pdb) = mkPD (pdb-src-i< pdb)

pdb-tgt-i≤ : {submax : ℕ} → {ty : Ty c} → {tm : Term ty} → {pds : PDShape (ty-dim ty) (suc submax)} → (pd : PDB tm pds) → PDB tm (pds-bd-i≤ pds)
pdb-tgt-i> : {base : Ty c} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → {pds : PDShape (suc (ty-dim base)) 0} → (pd : PDB tm pds) → PDB tgt (pds-bd-i> pds)
drop-pd : {ty : Ty c} → {tm : Term ty} → {pds : PDShape (ty-dim ty) 0} (pd : PDB tm pds) → (nt : Term ty) → PDB nt pds

pdb-tgt-i≤ (AttachNM pd tgt fill) = AttachNM (pdb-tgt-i≤ pd) tgt fill
pdb-tgt-i≤ {_} {zero} (Restr pd) = pdb-tgt-i> pd
pdb-tgt-i≤ {_} {suc _} (Restr pd) = Restr (pdb-tgt-i≤ pd)

pdb-tgt-i> (AttachMax pd tgt fill) = drop-pd pd tgt
pdb-tgt-i> (AttachNM pd tgt fill) = drop-pd (pdb-tgt-i≤ pd) tgt

drop-pd (Base _) nt = Base nt
drop-pd (AttachMax pd tgt _) nt = AttachMax pd tgt nt
drop-pd (AttachNM pd tgt _) nt = AttachNM pd tgt nt

pd-tgt : {dim : ℕ} → {pds : PDShape 0 (suc dim)} → PD c pds → PD c (pds-bd-i≤ pds)
pd-tgt {_} {i} (mkPD pdb) = mkPD (pdb-tgt-i≤ pdb)

record CtxSubstitution (c d : Ctx) : Set where
  inductive
  field
    apply : Fin (c .size) → Term ⋆
    arrSub : (s t : Fin (c .size)) → CtxSubstitution (arr c s t) (arr d (apply s) (apply t))

open CtxSubstitution

_⇛_ : (c d : Ctx) → Set
c ⇛ d = CtxSubstitution c d ⋆

infixr 3 _∙_

mapType : ∀ {c d : Ctx} {ty : Ty d} → CtxSubstitution c d ty → Ty c → Ty d
mapTerm : ∀ {c d : Ctx} {ty : Ty d} → (sub : CtxSubstitution c d ty) → {ty₁ : Ty c} → Term ty₁ → Term (mapType sub ty₁)

mapType {ty = ty} sub ⋆ = ty
mapType sub (_⟶_ {ty = ty} x y) = mapTerm sub x ⟶ mapTerm sub y

compose : ∀ {c d e : Ctx} {ty₁ : Ty d} {ty₂ : Ty e} → (sub : CtxSubstitution d e ty₂) → CtxSubstitution c d ty₁ → CtxSubstitution c e (mapType sub ty₁)
compose σ τ .apply = mapTerm σ ∘ apply τ
compose σ τ .arrSub s t = {!!}

pd-ctx-sub : ∀ {d} {pds : PDShape 0 d} → (pd : PD c pds) → CtxSubstitution (pds-ctx pds) c ⋆
pd-ctx-sub pd = {!!}





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
  Coh : ∀ {d} {pds : PDShape 0 d} → (pd : PD c pds) → {ty : Ty (pds-ctx pds)} (s t : Term ty) → (sc : IsComplete s) → (tc : IsComplete t) → Term (mapType (pd-ctx-sub pd) ty)
  Comp : ∀ {d} {pds : PDShape 0 (suc d)} → (pd : PD c pds) → {ty : Ty (pds-ctx (pds-bd-i≤ pds))} → (s t : Term ty) → (sc : IsComplete s) → (tc : IsComplete t) → Term (mapTerm (pd-ctx-sub (pd-src pd)) s ⟶ mapTerm (pd-ctx-sub (pd-tgt pd)) t)

purety-to-ty ⋆P = ⋆
purety-to-ty (_⟶P_ {t = t} x y) = Var t x ⟶ Var t y

mapTerm sub x = {!!}

FV t = {!!}
