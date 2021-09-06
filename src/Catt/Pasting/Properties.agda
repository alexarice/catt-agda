{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Binary
open import Axiom.UniquenessOfIdentityProofs
open import Catt.Variables
open import Data.Unit using (tt)
open import Catt.Globular
open import Data.Product renaming (_,_ to _,,_)

subst-pdb : (pdb : Γ ⊢pd[ submax ][ d ]) → Δ ≃c Γ → Δ ⊢pd[ submax ][ d ]
subst-pdb pdb c with ≃c-preserve-length c
... | refl with ≃c-to-≡ c
... | refl = pdb

subst-pdb-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ]) → (p : Δ ≃c Γ) → getFocusTerm pdb ≃tm getFocusTerm (subst-pdb pdb p)
subst-pdb-foc-tm pdb c with ≃c-preserve-length c
... | refl with ≃c-to-≡ c
... | refl = refl≃tm

subst-pdb-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ]) → (p : Δ ≃c Γ) → getFocusType pdb ≃ty getFocusType (subst-pdb pdb p)
subst-pdb-foc-ty pdb c with ≃c-preserve-length c
... | refl with ≃c-to-≡ c
... | refl = refl≃ty

extend-pd-eq : (pdb : Γ ⊢pd[ submax ][ d ])
             → A ≃ty getFocusType pdb
             → B ≃ty liftTerm {A = getFocusType pdb} (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V
             → Γ , A , B ⊢pd[ pred submax ][ suc d ]
extend-pd-eq pdb p q = subst-pdb (Extend pdb) (Add≃ (Add≃ refl≃c p) q)

extend-pd-eq-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ])
                    → (p : A ≃ty getFocusType pdb)
                    → (q : B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                    → 0V {Γ = Γ , A , B} ≃tm getFocusTerm (extend-pd-eq pdb p q)
extend-pd-eq-foc-tm pdb p q = trans≃tm (Var≃ (Add≃ (Add≃ refl≃c p) q) refl) (subst-pdb-foc-tm (Extend pdb) (Add≃ (Add≃ refl≃c p) q))


extend-pd-eq-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ])
                    → (p : A ≃ty getFocusType pdb)
                    → (q : B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                    → liftType {A = B} B ≃ty getFocusType (extend-pd-eq pdb p q)
extend-pd-eq-foc-ty pdb p q = trans≃ty (lift-ty-≃ q q) (subst-pdb-foc-ty (Extend pdb) (Add≃ (Add≃ refl≃c p) q))

pdb-is-non-empty : (pdb : Γ ⊢pd[ submax ][ d ]) → NonZero′ (ctxLength Γ)
pdb-is-non-empty Base = it
pdb-is-non-empty (Extend pdb) = it
pdb-is-non-empty (Restr pdb) = pdb-is-non-empty pdb

pd-is-non-empty : (pd : Γ ⊢pd₀ d) → NonZero′ (ctxLength Γ)
pd-is-non-empty (Finish pdb) = pdb-is-non-empty pdb

pdb-0-focus-ty-is-⋆ : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (⋆ {Γ = Γ}) ≃ty getFocusType pdb
pdb-0-focus-ty-is-⋆ pdb with getFocusType pdb
... | ⋆ = Star≃ refl≃c

-- pdb-dim-is-ctx-dim : Γ ⊢pd[ submax ][ d ] → ctx-dim Γ ≡ suc (d + submax)
-- pdb-dim-is-ctx-dim Base = refl
-- pdb-dim-is-ctx-dim (Extend {Γ = Γ} {submax = submax} {d = d} pdb) = begin
--   ctx-dim Γ ⊔ suc d ⊔ suc (suc d) ≡⟨ ⊔-assoc (ctx-dim Γ) (suc d) (suc (suc d)) ⟩
--   ctx-dim Γ ⊔ (suc d ⊔ suc (suc d)) ≡⟨ cong (ctx-dim Γ ⊔_) (m≤n⇒m⊔n≡n (s≤s (n≤1+n d))) ⟩
--   ctx-dim Γ ⊔ suc (suc d) ≡⟨ cong (_⊔ suc (suc d)) (pdb-dim-is-ctx-dim pdb) ⟩
--   suc (d + submax) ⊔ suc (suc d) ≡⟨ cong suc (lem d submax) ⟩
--   suc (suc (d + (submax ∸ 1))) ∎
--   where
--     open ≡-Reasoning
--     lem : ∀ d submax → d + submax ⊔ suc d ≡ suc (d + (pred submax))
--     lem d zero = begin
--       d + zero ⊔ suc d ≡⟨ m≤n⇒m⊔n≡n (≤-trans (≤-reflexive (+-identityʳ d)) (n≤1+n d)) ⟩
--       suc d ≡˘⟨ cong suc (+-identityʳ d) ⟩
--       suc (d + zero) ∎
--     lem d (suc submax) = begin
--       d + suc submax ⊔ suc d ≡⟨ cong (_⊔ suc d) (+-suc d submax) ⟩
--       suc (d + submax) ⊔ suc d ≡⟨ m≥n⇒m⊔n≡m (s≤s (m≤m+n d submax)) ⟩
--       suc (d + submax) ∎
-- pdb-dim-is-ctx-dim (Restr pdb) = trans (pdb-dim-is-ctx-dim pdb) (sym (cong suc (+-suc _ _)))

-- pd-dim-is-ctx-dim : Γ ⊢pd₀ d → ctx-dim Γ ≡ suc d
-- pd-dim-is-ctx-dim (Finish pdb) = pdb-dim-is-ctx-dim pdb

record PDB : Set where
  constructor <_>
  field
    {pdb-len} : ℕ
    {pdb-ctx} : Ctx (suc (pdb-len))
    {pdb-sm} : ℕ
    {pdb-dm} : ℕ
    pdb-pdb : pdb-ctx ⊢pd[ pdb-sm ][ pdb-dm ]

open PDB

pdb-dim-lem : {A : Ty Γ d} (pdb : Γ , A ⊢pd[ submax ][ d′ ]) → d′ ≤ d
pdb-dim-lem Base = ≤-refl
pdb-dim-lem (Extend pdb) = ≤-refl
pdb-dim-lem (Restr pdb) = ≤-trans (≤-step ≤-refl) (pdb-dim-lem pdb)

PDB-irrel : (pdb pdb2 : PDB) → pdb-ctx pdb ≃c pdb-ctx pdb2 → pdb-dm pdb ≡ pdb-dm pdb2 → pdb ≡ pdb2
PDB-irrel < Base > < Base > p q = refl
PDB-irrel < Base > < Restr pdb2 > (Add≃ Emp≃ (Star≃ x)) refl = ⊥-elim (1+n≰n (pdb-dim-lem pdb2))
PDB-irrel < Extend pdb1 > < Extend pdb2 > (Add≃ (Add≃ p x₁) x) q with PDB-irrel < pdb1 > < pdb2 > p (cong pred q)
... | refl = refl
PDB-irrel < Extend pdb1 > < Restr pdb2 > (Add≃ p x) refl with pdb-dim-lem pdb2 | ≃ty-preserve-height x
... | r | refl = ⊥-elim (1+n≰n r)
PDB-irrel < Restr pdb1 > < Base > (Add≃ Emp≃ (Star≃ x)) refl = ⊥-elim (1+n≰n (pdb-dim-lem pdb1))
PDB-irrel < Restr pdb1 > < Extend pdb2 > (Add≃ p x) refl with pdb-dim-lem pdb1 | ≃ty-preserve-height x
... | r | refl = ⊥-elim (1+n≰n r)
PDB-irrel < Restr pdb1 > < Restr pdb2 > p q with PDB-irrel < pdb1 > < pdb2 > p (cong suc q)
... | refl = refl

subst-pdb-≡ : (p : n ≡ m) → {Γ : Ctx (suc n)} → {Γ′ : Ctx (suc m)} → subst Ctx (cong suc p) Γ ≡ Γ′ → submax ≡ submax′ → d ≡ d′ → Γ ⊢pd[ submax ][ d ] → Γ′ ⊢pd[ submax′ ][ d′ ]
subst-pdb-≡ refl refl refl refl pdb = pdb

PDB-lem-len : {pdb pdb2 : PDB} → pdb ≡ pdb2 → pdb-len pdb ≡ pdb-len pdb2
PDB-lem-len refl = refl

PDB-lem-ctx : {pdb pdb2 : PDB} → (p : pdb ≡ pdb2) → subst Ctx (cong suc (PDB-lem-len p)) (pdb-ctx pdb) ≡ pdb-ctx pdb2
PDB-lem-ctx refl = refl

PDB-lem-ctx≡ : {pdb pdb2 : PDB} → (p : pdb ≡ pdb2) → (q : pdb-len pdb ≡ pdb-len pdb2) → subst Ctx (cong suc q) (pdb-ctx pdb) ≡ pdb-ctx pdb2
PDB-lem-ctx≡ {pdb} refl q = cong (λ - → subst Ctx (cong suc -) (pdb-ctx pdb)) (≡-irrelevant q refl)

PDB-lem-sm : {pdb pdb2 : PDB} → pdb ≡ pdb2 → pdb-sm pdb ≡ pdb-sm pdb2
PDB-lem-sm refl = refl

PDB-lem-dm : {pdb pdb2 : PDB} → pdb ≡ pdb2 → pdb-dm pdb ≡ pdb-dm pdb2
PDB-lem-dm refl = refl

PDB-lem-pdb : {pdb pdb2 : PDB} → (p : pdb ≡ pdb2) → subst-pdb-≡ (PDB-lem-len p) (PDB-lem-ctx p) (PDB-lem-sm p) (PDB-lem-dm p) (pdb-pdb pdb) ≡ (pdb-pdb pdb2)
PDB-lem-pdb refl = refl

ctxn-irrelevant : Irrelevant {A = Ctx n} (_≡_)
ctxn-irrelevant = Decidable⇒UIP.≡-irrelevant ctx-dec

PDB-lem≡ : {pdb pdb2 : PDB} → (p : pdb ≡ pdb2)
                           → (q : pdb-len pdb ≡ pdb-len pdb2)
                           → (r : (x : pdb-len pdb ≡ pdb-len pdb2) → subst Ctx (cong suc x) (pdb-ctx pdb) ≡ pdb-ctx pdb2)
                           → (s : pdb-sm pdb ≡ pdb-sm pdb2)
                           → (t : pdb-dm pdb ≡ pdb-dm pdb2)
                           → subst-pdb-≡ q (r q) s t (pdb-pdb pdb) ≡ (pdb-pdb pdb2)
PDB-lem≡ {pdb} refl q r s t = trans step1 (trans step2 (trans step3 step4))
  where
  step1 : subst-pdb-≡ q (r q) s t (pdb-pdb pdb) ≡
          subst-pdb-≡ refl (r refl) s t (pdb-pdb pdb)
  step1 = cong (λ - → subst-pdb-≡ - (r -) s t (pdb-pdb pdb)) (≡-irrelevant q refl)

  step2 : subst-pdb-≡ refl (r refl) s t (pdb-pdb pdb) ≡
          subst-pdb-≡ refl (r refl) refl t (pdb-pdb pdb)
  step2 = cong (λ - → subst-pdb-≡ refl (r refl) - t (pdb-pdb pdb)) (≡-irrelevant s refl)

  step3 : subst-pdb-≡ refl (r refl) refl t (pdb-pdb pdb) ≡
          subst-pdb-≡ refl (r refl) refl refl (pdb-pdb pdb)
  step3 = cong (λ - → subst-pdb-≡ refl (r refl) refl - (pdb-pdb pdb)) (≡-irrelevant t refl)

  step4 : subst-pdb-≡ refl (r refl) refl refl (pdb-pdb pdb) ≡ pdb-pdb pdb
  step4 = cong (λ - → subst-pdb-≡ refl - refl refl (pdb-pdb pdb)) (ctxn-irrelevant (r refl) refl)

pdb-irrelevant : (pdb : Γ ⊢pd[ submax ][ d ]) (pdb2 : Γ ⊢pd[ submax ][ d ]) → pdb ≡ pdb2
pdb-irrelevant {n} {Γ} pdb pdb2 = trans (cong (λ - → subst-pdb-≡ refl - refl refl pdb) (ctxn-irrelevant refl (PDB-lem-ctx≡ PDB≡ refl)))
                                        (PDB-lem≡ PDB≡ refl (PDB-lem-ctx≡ PDB≡) refl refl)
  where
    PDB≡ : < pdb > ≡ < pdb2 >
    PDB≡ = PDB-irrel < pdb > < pdb2 > refl≃c refl

pdb-is-globular : (pdb : Γ ⊢pd[ submax ][ d ]) → ctx-is-globular Γ
focus-term-is-var : (pdb : Γ ⊢pd[ submax ][ d ]) → isVar (getFocusTerm pdb)
focus-ty-is-globular : (pdb : Γ ⊢pd[ submax ][ d ]) → ty-is-globular (getFocusType pdb)

pdb-is-globular Base = tt ,, tt
pdb-is-globular (Extend pdb) = ((pdb-is-globular pdb) ,, focus-ty-is-globular pdb) ,, liftTerm-preserve-isVar (getFocusTerm pdb) (focus-term-is-var pdb) ,, (liftType-preserve-is-globular (getFocusType pdb) (focus-ty-is-globular pdb) ,, tt)
pdb-is-globular (Restr pdb) = pdb-is-globular pdb

focus-term-is-var Base = tt
focus-term-is-var (Extend pdb) = tt
focus-term-is-var (Restr pdb) = ty-globular-tgt (getFocusType pdb) (focus-ty-is-globular pdb)

focus-ty-is-globular Base = tt
focus-ty-is-globular (Extend pdb) = liftTerm-preserve-isVar (liftTerm (getFocusTerm pdb)) (liftTerm-preserve-isVar (getFocusTerm pdb) (focus-term-is-var pdb)) ,, liftType-preserve-is-globular (liftType (getFocusType pdb)) (liftType-preserve-is-globular (getFocusType pdb) (focus-ty-is-globular pdb)) ,, tt
focus-ty-is-globular (Restr pdb) = ty-globular-base (getFocusType pdb) (focus-ty-is-globular pdb)
