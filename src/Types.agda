{-# OPTIONS --safe --without-K #-}

module Types where

open import Data.Nat

data Ctx : Set

data Ty (c : Ctx) : Set

data Term : (Γ : Ctx) → Ty Γ → Set

data Substitution (Γ : Ctx) : (Δ : Ctx) → Set

infixl 4 _,_
data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → (A : Ty Γ) → Ctx

data Ty Γ where
  ⋆ : Ty Γ
  _⟶_ : {A : Ty Γ} → (t u : Term Γ A) → Ty Γ

_[_]ty : {Γ Δ : Ctx} → Ty Δ → Substitution Γ Δ → Ty Γ
_[_]tm : {Γ Δ : Ctx} → {A : Ty Δ} → Term Δ A → (σ : Substitution Γ Δ) → Term Γ (A [ σ ]ty)

data Substitution Γ where
  ⟨⟩ : Substitution Γ ∅
  ⟨_,_⟩ : {Δ : Ctx} → (σ : Substitution Γ Δ) → {A : Ty Δ} → Term Γ (A [ σ ]ty) → Substitution Γ (Δ , A)

⋆ [ σ ]ty = ⋆
(t ⟶ u) [ σ ]ty = (t [ σ ]tm) ⟶ (u [ σ ]tm)

liftType : {Γ : Ctx} → (A : Ty Γ) → (B : Ty Γ) → Ty (Γ , B)

data Term where
  Var : {Γ : Ctx} → (A : Ty Γ) → Term (Γ , A) (liftType A A)
  Gen : {Γ : Ctx} → {B : Ty Γ} → (t : Term Γ B) → (A : Ty Γ) → Term (Γ , A) (liftType B A)

liftType ⋆ A = ⋆
liftType (t ⟶ u) A = (Gen t A) ⟶ Gen u A

_∘_ : {Γ Δ Υ : Ctx} → Substitution Δ Γ → Substitution Υ Δ → Substitution Υ Γ
comp-lemma : {Γ Δ Υ : Ctx} → (σ : Substitution Δ Γ) → (τ : Substitution Υ Δ) → {A : Ty Γ} → Term Υ (A [ σ ]ty [ τ ]ty) → Term Υ (A [ σ ∘ τ ]ty)
sub-ext : {Γ Δ : Ctx} → (A : Ty Γ) → Substitution Γ Δ → Substitution (Γ , A) Δ
sub-ext-lemma : {Γ Δ : Ctx} → (A : Ty Γ) → {B : Ty Δ} → (σ : Substitution Γ Δ) → Term Γ (B [ σ ]ty) → Term (Γ , A) (B [ sub-ext A σ ]ty)
sub-ext A ⟨⟩ = ⟨⟩
sub-ext A ⟨ σ , x ⟩ = ⟨ sub-ext A σ , sub-ext-lemma A σ x ⟩

⟨⟩ ∘ τ = ⟨⟩
⟨ σ , x ⟩ ∘ τ = ⟨ σ ∘ τ , comp-lemma σ τ (x [ τ ]tm) ⟩

id : (Γ : Ctx) → Substitution Γ Γ

id-lemma : {Γ : Ctx} → (A : Ty Γ) → Term (Γ , A) (liftType A A) → Term Γ (A [ id Γ ]ty)
id ∅ = ⟨⟩
id (Γ , A) = ⟨ sub-ext A (id Γ) , sub-ext-lemma A (id Γ) (id-lemma A (Var A)) ⟩

data PDB : (submax : ℕ) → (Γ : Ctx) → {A : Ty Γ} → Term Γ A → Set where
  Base : PDB 0 (∅ , ⋆) (Var ⋆)
  ExtendMax : {Γ : Ctx} → {A : Ty Γ} → {x : Term Γ A} → PDB 0 Γ x → PDB 0 (Γ , A , Gen x A ⟶ Var A) (Var (Gen x A ⟶ Var A))
  ExtendNM : {n : ℕ} → {Γ : Ctx} → {A : Ty Γ} → {x : Term Γ A} → PDB (suc n) Γ x → PDB n (Γ , A , Gen x A ⟶ Var A) (Var (Gen x A ⟶ Var A))
  Restr : {n : ℕ} → {Γ : Ctx} → {E : Ty Γ} → {A : Ty (Γ , E)} → {x y : Term (Γ , E) A} → PDB n (Γ , E , (x ⟶ y)) (Var (x ⟶ y)) → PDB (suc n) (Γ , E) y

data PD : Ctx → Set where
  Finish : {n : ℕ} → {Γ : Ctx} → {x : Term Γ ⋆} → PDB n Γ x → PD Γ

-- pdb-src-i< : {n : ℕ} → {Γ : Ctx} → {A : Ty Γ} → {x : Term Γ A} → PDB (suc (suc n)) Γ x → PDB (suc n) Γ x
-- pdb-src-i≡ : {Γ : Ctx} → {A : Ty Γ} → {x : Term Γ A} → PDB 1 Γ x → PDB 0 Γ x

pd-src : {Γ : Ctx} → PD Γ → Ctx
pd-src (Finish x) = {!!}
  where
    go : {n : ℕ} → (Γ : Ctx) → {A : Ty Γ} → {x : Term Γ A} → PDB n Γ x → Ctx
    go Γ Base = Γ
    go (Γ , _ , (Gen _ _ ⟶ Var _)) (ExtendMax pdb) = Γ
    go {zero} (Γ , _ , (Gen _ _ ⟶ Var _)) (ExtendNM pdb) = go Γ pdb
    go {suc n} (Γ , x , y) (ExtendNM pdb) = {!go Γ pdb!} , {!!} , {!!}
    go .(_ , _) (Restr pdb) = {!!}

x [ σ ]tm = {!!}

comp-lemma = {!!}
sub-ext-lemma = {!!}
id-lemma = {!!}


-- data PDB {c : Ctx} : {ty : Ty c} → Term ty → {submax : ℕ} → PDShape (ty-dim ty) submax → Set

-- data PDB {c} where
--   Base : (t : Term {c} ⋆) → PDB t BaseS
--   AttachMax : {ty : Ty c} →
--               {tm : Term ty} →
--               {pds : PDShape (ty-dim ty) 0} →
--               (pd : PDB tm pds) →
--               (tgt : Term ty) →
--               (fill : Term (tm ⟶ tgt)) →
--               PDB fill (AttachMaxS pds)
--   AttachNM : {ty : Ty c} →
--              {tm : Term ty} →
--              {submax : ℕ} →
--              {pds : PDShape (ty-dim ty) (suc submax)} →
--              (pd : PDB tm pds) →
--              (tgt : Term ty) →
--              (fill : Term (tm ⟶ tgt)) →
--              PDB fill (AttachNMS pds)
--   Restr : {ty : Ty c} →
--           {src : Term ty} →
--           {tgt : Term ty} →
--           {tm : Term (src ⟶ tgt)} →
--           {submax : ℕ} →
--           {pds : PDShape (suc (ty-dim ty)) submax} →
--           (pd : PDB tm pds) →
--           PDB tgt (RestrS pds)

-- record PD (c : Ctx) {d : ℕ} (pds : PDShape 0 d) : Set where
--   inductive
--   constructor mkPD
--   field
--     {pd-tm} : Term {c} ⋆
--     getPD : PDB pd-tm pds

-- pdb-src-i< : {submax : ℕ} → {ty : Ty c} → {tm : Term ty} → {pds : PDShape (ty-dim ty) (suc (suc submax))} → (pd : PDB tm pds) → PDB tm (pds-bd-i≤ pds)
-- pdb-src-i≡ : {ty : Ty c} → {tm : Term ty} → {pds : PDShape (ty-dim ty) 1} (pd : PDB tm pds) → Σ[ t ∈ Term ty ] PDB t (pds-bd-i≤ pds)
-- pdb-src-i> : {base : Ty c} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → {pds : PDShape (suc (ty-dim base)) 0} → (pd : PDB tm pds) → Σ[ t ∈ Term base ] PDB t (pds-bd-i> pds)

-- pdb-src-i< (AttachNM pd tgt fill) = AttachNM (pdb-src-i< pd) tgt fill
-- pdb-src-i< {_} {zero} (Restr pd) = Restr (proj₂ (pdb-src-i≡ pd))
-- pdb-src-i< {_} {suc submax} (Restr pd) = Restr (pdb-src-i< pd)

-- pdb-src-i≡ (AttachNM pd tgt fill) = -, AttachNM (pdb-src-i< pd) tgt fill
-- pdb-src-i≡ (Restr pd) = pdb-src-i> pd

-- pdb-src-i> (AttachMax pd tgt fill) = -, pd
-- pdb-src-i> (AttachNM pd tgt fill) = pdb-src-i≡ pd

-- pd-src : {dim : ℕ} → {pds : PDShape 0 (suc dim)} → PD c pds → PD c (pds-bd-i≤ pds)
-- pd-src {_} {zero} (mkPD pdb) = mkPD (proj₂ (pdb-src-i≡ pdb))
-- pd-src {_} {suc i} (mkPD pdb) = mkPD (pdb-src-i< pdb)

-- pdb-tgt-i≤ : {submax : ℕ} → {ty : Ty c} → {tm : Term ty} → {pds : PDShape (ty-dim ty) (suc submax)} → (pd : PDB tm pds) → PDB tm (pds-bd-i≤ pds)
-- pdb-tgt-i> : {base : Ty c} → {src tgt : Term base} → {tm : Term (src ⟶ tgt)} → {pds : PDShape (suc (ty-dim base)) 0} → (pd : PDB tm pds) → PDB tgt (pds-bd-i> pds)
-- drop-pd : {ty : Ty c} → {tm : Term ty} → {pds : PDShape (ty-dim ty) 0} (pd : PDB tm pds) → (nt : Term ty) → PDB nt pds

-- pdb-tgt-i≤ (AttachNM pd tgt fill) = AttachNM (pdb-tgt-i≤ pd) tgt fill
-- pdb-tgt-i≤ {_} {zero} (Restr pd) = pdb-tgt-i> pd
-- pdb-tgt-i≤ {_} {suc _} (Restr pd) = Restr (pdb-tgt-i≤ pd)

-- pdb-tgt-i> (AttachMax pd tgt fill) = drop-pd pd tgt
-- pdb-tgt-i> (AttachNM pd tgt fill) = drop-pd (pdb-tgt-i≤ pd) tgt

-- drop-pd (Base _) nt = Base nt
-- drop-pd (AttachMax pd tgt _) nt = AttachMax pd tgt nt
-- drop-pd (AttachNM pd tgt _) nt = AttachNM pd tgt nt

-- pd-tgt : {dim : ℕ} → {pds : PDShape 0 (suc dim)} → PD c pds → PD c (pds-bd-i≤ pds)
-- pd-tgt {_} {i} (mkPD pdb) = mkPD (pdb-tgt-i≤ pdb)

-- data TermShape : Set where
--   V : TermShape
--   CH : TermShape → TermShape → TermShape
--   CM : TermShape → TermShape → TermShape

-- term-container : Container 0ℓ 0ℓ
-- term-container .Shape = TermShape
-- term-container .Position V = ⊤
-- term-container .Position (CH _ _) = Bool
-- term-container .Position (CM _ _) = Bool

-- FV : {ty : Ty c} → Term ty → ⟦ term-container ⟧ (CtxIndex c)

-- IsComplete : {ty : Ty c} → Term ty → Set
-- IsComplete tm = ∀ i → i ∈ FV tm

-- purety-to-ty : (p : PureTy c) → Ty c

-- data Term {c} where
--   Var : (ty : PureTy c) → Fin (retrieve-size ty) → Term (purety-to-ty ty)
--   Coh : ∀ {d} {pds : PDShape 0 d} → (pd : PD c pds) → {ty : Ty (pds-ctx pds)} (s t : Term ty) → (sc : IsComplete s) → (tc : IsComplete t) → Term (mapType (pd-ctx-sub pd) ty)
--   Comp : ∀ {d} {pds : PDShape 0 (suc d)} → (pd : PD c pds) → {ty : Ty (pds-ctx (pds-bd-i≤ pds))} → (s t : Term ty) → (sc : IsComplete s) → (tc : IsComplete t) → Term (mapTerm (pd-ctx-sub (pd-src pd)) s ⟶ mapTerm (pd-ctx-sub (pd-tgt pd)) t)

-- purety-to-ty ⋆P = ⋆
-- purety-to-ty (_⟶P_ {t = t} x y) = Var t x ⟶ Var t y

-- mapTerm sub x = {!!}

-- FV t = {!!}
