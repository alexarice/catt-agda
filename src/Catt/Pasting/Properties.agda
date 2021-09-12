{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Relation.Binary
open import Axiom.UniquenessOfIdentityProofs
open import Catt.Variables
open import Data.Unit using (tt)
open import Catt.Globular
open import Data.Product renaming (_,_ to _,,_)
import Relation.Binary.Reasoning.Setoid as Reasoning

subst-pdb : {Γ Δ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ d ]) → Δ ≃c Γ → Δ ⊢pd[ submax ][ d ]
subst-pdb pdb c with ≃c-to-≡ c
... | refl = pdb

subst-pdb-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ]) → (p : Δ ≃c Γ) → getFocusTerm pdb ≃tm getFocusTerm (subst-pdb pdb p)
subst-pdb-foc-tm pdb c with ≃c-to-≡ c
... | refl = refl≃tm

subst-pdb-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ]) → (p : Δ ≃c Γ) → getFocusType pdb ≃ty getFocusType (subst-pdb pdb p)
subst-pdb-foc-ty pdb c with ≃c-to-≡ c
... | refl = refl≃ty

subst-pdb-supp-src : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ _ : NonZero′ (submax + d) ⦄ → (p : Δ ≃c Γ) → supp-pdb-src pdb ≡ supp-pdb-src (subst-pdb pdb p)
subst-pdb-supp-src pdb p with ≃c-to-≡ p
... | refl = refl

subst-pdb-supp-tgt : (pdb : Γ ⊢pd[ submax ][ d ]) → .⦃ _ : NonZero′ (submax + d) ⦄ → (p : Δ ≃c Γ) → supp-pdb-tgt pdb ≡ supp-pdb-tgt (subst-pdb pdb p)
subst-pdb-supp-tgt pdb p with ≃c-to-≡ p
... | refl = refl

extend-pd-eq : (pdb : Γ ⊢pd[ submax ][ d ])
             → A ≃ty getFocusType pdb
             → B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V
             → Γ , A , B ⊢pd[ pred submax ][ suc d ]
extend-pd-eq pdb p q = subst-pdb (Extend pdb) (Add≃ (Add≃ refl≃c p) q)

extend-pd-eq-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ])
                    → (p : A ≃ty getFocusType pdb)
                    → (q : B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                    → 0V {suc (suc (ctxLength Γ))} ≃tm getFocusTerm (extend-pd-eq pdb p q)
extend-pd-eq-foc-tm pdb p q = subst-pdb-foc-tm (Extend pdb) (Add≃ (Add≃ refl≃c p) q)


extend-pd-eq-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ])
                    → (p : A ≃ty getFocusType pdb)
                    → (q : B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                    → liftType B ≃ty getFocusType (extend-pd-eq pdb p q)
extend-pd-eq-foc-ty pdb p q = trans≃ty (lift-ty-≃ q) (subst-pdb-foc-ty (Extend pdb) (Add≃ (Add≃ refl≃c p) q))

pdb-is-non-empty : (pdb : Γ ⊢pd[ submax ][ d ]) → NonZero′ (ctxLength Γ)
pdb-is-non-empty Base = it
pdb-is-non-empty (Extend pdb) = it
pdb-is-non-empty (Restr pdb) = pdb-is-non-empty pdb

pd-is-non-empty : (pd : Γ ⊢pd₀ d) → NonZero′ (ctxLength Γ)
pd-is-non-empty (Finish pdb) = pdb-is-non-empty pdb

pdb-0-focus-ty-is-⋆ : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (⋆ {ctxLength Γ}) ≃ty getFocusType pdb
pdb-0-focus-ty-is-⋆ pdb with getFocusType pdb
... | ⋆ = Star≃ refl

supp-pdb-src-≃ : (pdb : Γ ⊢pd[ submax ][ d ])
               → (p : A ≃ty getFocusType pdb)
               → (q : B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
               → supp-pdb-src (Extend pdb) ≡ supp-pdb-src (extend-pd-eq pdb p q)
supp-pdb-src-≃ pdb p q = subst-pdb-supp-src (Extend pdb) (Add≃ (Add≃ refl≃c p) q)

supp-pdb-tgt-≃ : (pdb : Γ ⊢pd[ submax ][ d ])
               → (p : A ≃ty getFocusType pdb)
               → (q : B ≃ty liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
               → supp-pdb-tgt (Extend pdb) ≡ supp-pdb-tgt (extend-pd-eq pdb p q)
supp-pdb-tgt-≃ pdb p q = subst-pdb-supp-tgt (Extend pdb) (Add≃ (Add≃ refl≃c p) q)

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

pdb-dim-lem : {A : Ty (ctxLength Γ) d} (pdb : Γ , A ⊢pd[ submax ][ d′ ]) → d′ ≤ d
pdb-dim-lem Base = ≤-refl
pdb-dim-lem (Extend pdb) = ≤-refl
pdb-dim-lem (Restr pdb) = ≤-trans (≤-step ≤-refl) (pdb-dim-lem pdb)

isEven : ℕ → Set
isOdd : ℕ → Set

isEven zero = ⊤
isEven (suc n) = isOdd n

isOdd zero = ⊥
isOdd (suc n) = isEven n

pdb-len-lem : Γ ⊢pd[ submax ][ d ] → isOdd (ctxLength Γ)
pdb-len-lem Base = tt
pdb-len-lem (Extend pdb) = pdb-len-lem pdb
pdb-len-lem (Restr pdb) = pdb-len-lem pdb

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

replacePdSub-lem : (σ : Sub (suc n) l)
                 → (τ : Sub m n)
                 → (t : Tm l)
                 → σ ∘ liftSub τ ≃s replacePdSub σ t ∘ liftSub τ
replacePdSub-lem ⟨ σ , t ⟩ τ _ = trans≃s (lift-sub-comp-lem-sub σ τ) (sym≃s (lift-sub-comp-lem-sub σ τ))


pdb-globular-lem-1 : (pdb : Γ ⊢pd[ submax ][ d ])
                   → .⦃ _ : is-zero submax ⦄
                   → .⦃ _ : NonZero′ (submax + d) ⦄
                   → (σ : Sub (ctxLength Γ) l)
                   → (τ : Sub (ctxLength Γ) l)
                   → (t : Tm (suc (suc l)))
                   → σ ∘ pdb-src pdb ≃s τ ∘ pdb-src pdb
                   → liftSub (liftSub σ) ∘ pdb-src pdb ≃s (replacePdSub (liftSub (liftSub τ)) t) ∘ pdb-src pdb
pdb-globular-lem-1 (Extend {submax = zero} pdb) ⟨ σ , x ⟩ ⟨ τ , y ⟩ t (Ext≃ p q) = Ext≃ l1 l2
  where
    l1 : (liftSub (liftSub ⟨ σ , x ⟩) ∘
            liftSub (liftSub (liftSub (idSub _))))
           ≃s
           (replacePdSub (liftSub (liftSub ⟨ τ , y ⟩)) t ∘
            liftSub (liftSub (liftSub (idSub _))))
    l1 = begin
      < liftSub (liftSub ⟨ σ , x ⟩) ∘ liftSub (liftSub (liftSub (idSub _))) >s
        ≈⟨ apply-lifted-sub-sub-≃ (liftSub (liftSub (liftSub (idSub _)))) ⟨ liftSub σ , liftTerm x ⟩ ⟩
      < liftSub (⟨ liftSub σ , liftTerm x ⟩ ∘ liftSub (liftSub (liftSub (idSub _)))) >s
        ≈⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (liftSub (liftSub (liftSub (idSub _)))) ⟨ σ , x ⟩) ⟩
      < liftSub (liftSub (⟨ σ , x ⟩ ∘ liftSub (liftSub (liftSub (idSub _))))) >s
        ≈⟨ lift-sub-≃ (lift-sub-≃ p) ⟩
      < liftSub (liftSub (⟨ τ , y ⟩ ∘ liftSub (liftSub (liftSub (idSub _))))) >s
        ≈˘⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (liftSub (liftSub (liftSub (idSub _)))) ⟨ τ , y ⟩) ⟩
      < liftSub (⟨ liftSub τ , liftTerm y ⟩ ∘ liftSub (liftSub (liftSub (idSub _)))) >s
        ≈˘⟨ apply-lifted-sub-sub-≃ (liftSub (liftSub (liftSub (idSub _)))) ⟨ liftSub τ , liftTerm y ⟩ ⟩
      < liftSub (liftSub ⟨ τ , y ⟩) ∘ liftSub (liftSub (liftSub (idSub _))) >s
        ≈⟨ replacePdSub-lem (liftSub (liftSub ⟨ τ , y ⟩)) (liftSub (liftSub (idSub _))) t ⟩
      < replacePdSub (liftSub (liftSub ⟨ τ , y ⟩)) t ∘ liftSub (liftSub (liftSub (idSub _))) >s ∎
      where
        open Reasoning sub-setoid

    l2 : 2V [ liftSub (liftSub ⟨ σ , x ⟩) ]tm
           ≃tm
         2V [ replacePdSub (liftSub (liftSub ⟨ τ , y ⟩)) t ]tm
    l2 = begin
      < 1V [ liftSub (liftSub σ) ]tm >tm ≈⟨ apply-lifted-sub-tm-≃ 1V (liftSub σ) ⟩
      < liftTerm (1V [ liftSub σ ]tm) >tm ≈⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ 1V σ) ⟩
      < liftTerm (liftTerm (1V [ σ ]tm)) >tm ≈⟨ lift-tm-≃ (lift-tm-≃ q) ⟩
      < liftTerm (liftTerm (1V [ τ ]tm)) >tm ≈˘⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ 1V τ) ⟩
      < (liftTerm (1V [ liftSub τ ]tm)) >tm ≈˘⟨ apply-lifted-sub-tm-≃ 1V (liftSub τ) ⟩
      < 1V [ liftSub (liftSub τ) ]tm
        >tm ≈⟨ sub-action-≃-tm (refl≃tm {s = 1V}) (replacePdSub-lem (liftSub (liftSub ⟨ τ , y ⟩)) (idSub _) t) ⟩
      < 1V [ replacePdSub (liftSub (liftSub ⟨ τ , y ⟩)) t ∘ liftSub (idSub _) ]tm >tm ≡⟨⟩
      < 2V [ replacePdSub (liftSub (liftSub ⟨ τ , y ⟩)) t ]tm >tm ∎
      where
        open Reasoning tm-setoid
pdb-globular-lem-1 (Extend {submax = suc zero} pdb) ⟨ σ , x ⟩ ⟨ τ , y ⟩ t p = begin
  < ⟨ liftSub (liftSub σ) , liftTerm (liftTerm x) ⟩ ∘ liftSub (liftSub (pdb-src pdb)) >s
    ≈⟨ apply-lifted-sub-sub-≃ (liftSub (liftSub (pdb-src pdb))) ⟨ liftSub σ , liftTerm x ⟩ ⟩
  < liftSub (⟨ liftSub σ , liftTerm x ⟩ ∘ liftSub (liftSub (pdb-src pdb))) >s
    ≈⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (liftSub (liftSub (pdb-src pdb))) ⟨ σ , x ⟩) ⟩
  < liftSub (liftSub (⟨ σ , x ⟩ ∘ liftSub (liftSub (pdb-src pdb)))) >s
    ≈⟨ lift-sub-≃ (lift-sub-≃ p) ⟩
  < liftSub (liftSub (⟨ τ , y ⟩ ∘ liftSub (liftSub (pdb-src pdb)))) >s
    ≈˘⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (liftSub (liftSub (pdb-src pdb))) ⟨ τ , y ⟩) ⟩
  < liftSub (liftSub ⟨ τ , y ⟩ ∘ liftSub (liftSub (pdb-src pdb))) >s
    ≈˘⟨ apply-lifted-sub-sub-≃ (liftSub (liftSub (pdb-src pdb))) (liftSub ⟨ τ , y ⟩) ⟩
  < liftSub (liftSub ⟨ τ , y ⟩) ∘ liftSub (liftSub (pdb-src pdb)) >s ≈⟨ lift-sub-comp-lem-sub (liftSub (liftSub τ)) (liftSub (pdb-src pdb)) ⟩
  < liftSub (liftSub τ) ∘ liftSub (pdb-src pdb) >s ≈˘⟨ lift-sub-comp-lem-sub (liftSub (liftSub τ)) (liftSub (pdb-src pdb)) ⟩
  < ⟨ liftSub (liftSub τ) , t ⟩ ∘ liftSub (liftSub (pdb-src pdb)) >s ∎
  where
    open Reasoning sub-setoid

open import Data.Fin using (Fin; suc; zero)
pdb-globular-1 : (pdb : Γ ⊢pd[ submax ][ d ])
               → .⦃ nz : NonZero′ (submax + d) ⦄
               → .⦃ nz2 : NonZero′ ((pred submax) + (newDim submax d)) ⦄
               → pdb-src pdb ∘ pdb-src (pdb-bd-pd pdb) ≃s pdb-tgt pdb ∘ pdb-src (pdb-bd-pd pdb)
pdb-globular-1 (Extend {submax = zero} pdb) = pdb-globular-lem-1 pdb (idSub _) (idSub _) 1V refl≃s
pdb-globular-1 (Extend {submax = suc zero} pdb) = pdb-globular-lem-1 (pdb-bd-pd pdb) (pdb-src pdb) (pdb-tgt pdb) 1V (pdb-globular-1 pdb)
pdb-globular-1 (Extend {submax = suc (suc zero)} pdb) = begin
  < ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ , 0V ⟩
       ∘ liftSub (liftSub (pdb-src (pdb-bd-pd pdb))) >s ≈⟨ lift-sub-comp-lem-sub ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ (liftSub (pdb-src (pdb-bd-pd pdb))) ⟩
  < ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ ∘
    liftSub (pdb-src (pdb-bd-pd pdb)) >s
    ≈⟨ lift-sub-comp-lem-sub (liftSub (liftSub (pdb-src pdb))) (pdb-src (pdb-bd-pd pdb)) ⟩
  < liftSub (liftSub (pdb-src pdb)) ∘ pdb-src (pdb-bd-pd pdb) >s ≈⟨ apply-lifted-sub-sub-≃ (pdb-src (pdb-bd-pd pdb)) (liftSub (pdb-src pdb)) ⟩
  < liftSub (liftSub (pdb-src pdb) ∘ pdb-src (pdb-bd-pd pdb)) >s ≈⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (pdb-src (pdb-bd-pd pdb)) (pdb-src pdb)) ⟩
  < liftSub (liftSub (pdb-src pdb ∘ pdb-src (pdb-bd-pd pdb))) >s ≈⟨ lift-sub-≃ (lift-sub-≃ (pdb-globular-1 pdb)) ⟩
  < liftSub (liftSub (pdb-tgt pdb ∘ pdb-src (pdb-bd-pd pdb))) >s
    ≈˘⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (pdb-src (pdb-bd-pd pdb)) (pdb-tgt pdb)) ⟩
  < liftSub (liftSub (pdb-tgt pdb) ∘ pdb-src (pdb-bd-pd pdb)) >s
    ≈˘⟨ apply-lifted-sub-sub-≃ (pdb-src (pdb-bd-pd pdb)) (liftSub (pdb-tgt pdb)) ⟩
  < liftSub (liftSub (pdb-tgt pdb)) ∘ pdb-src (pdb-bd-pd pdb) >s
    ≈˘⟨ lift-sub-comp-lem-sub (liftSub (liftSub (pdb-tgt pdb))) (pdb-src (pdb-bd-pd pdb)) ⟩
  < ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ ∘
      liftSub (pdb-src (pdb-bd-pd pdb)) >s
    ≈˘⟨ lift-sub-comp-lem-sub ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ (liftSub (pdb-src (pdb-bd-pd pdb))) ⟩
  < ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ , 0V ⟩
       ∘ liftSub (liftSub (pdb-src (pdb-bd-pd pdb))) >s ∎
  where
    open Reasoning sub-setoid
pdb-globular-1 (Extend {submax = suc (suc (suc submax))} pdb) = Ext≃ (Ext≃ lem refl≃tm) refl≃tm
  where
    open Reasoning sub-setoid
    lem : ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ , 0V ⟩
            ∘ liftSub (liftSub (pdb-src (pdb-bd-pd pdb)))
            ≃s
          ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ , 0V ⟩
            ∘ liftSub (liftSub (pdb-src (pdb-bd-pd pdb)))
    lem = begin
      < ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ , 0V ⟩
          ∘ liftSub (liftSub (pdb-src (pdb-bd-pd pdb))) >s
        ≈⟨ lift-sub-comp-lem-sub ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ (liftSub (pdb-src (pdb-bd-pd pdb))) ⟩
      < ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ ∘
          liftSub (pdb-src (pdb-bd-pd pdb)) >s
        ≈⟨ lift-sub-comp-lem-sub (liftSub (liftSub (pdb-src pdb))) (pdb-src (pdb-bd-pd pdb)) ⟩
      < liftSub (liftSub (pdb-src pdb)) ∘ pdb-src (pdb-bd-pd pdb) >s
        ≈⟨ apply-lifted-sub-sub-≃ (pdb-src (pdb-bd-pd pdb)) (liftSub (pdb-src pdb)) ⟩
      < liftSub (liftSub (pdb-src pdb) ∘ pdb-src (pdb-bd-pd pdb)) >s ≈⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (pdb-src (pdb-bd-pd pdb)) (pdb-src pdb)) ⟩
      < liftSub (liftSub (pdb-src pdb ∘ pdb-src (pdb-bd-pd pdb))) >s ≈⟨ lift-sub-≃ (lift-sub-≃ (pdb-globular-1 pdb)) ⟩
      < liftSub (liftSub (pdb-tgt pdb ∘ pdb-src (pdb-bd-pd pdb))) >s
        ≈˘⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (pdb-src (pdb-bd-pd pdb)) (pdb-tgt pdb)) ⟩
      < liftSub (liftSub (pdb-tgt pdb) ∘ pdb-src (pdb-bd-pd pdb)) >s
        ≈˘⟨ apply-lifted-sub-sub-≃ (pdb-src (pdb-bd-pd pdb)) (liftSub (pdb-tgt pdb)) ⟩
      < liftSub (liftSub (pdb-tgt pdb)) ∘ pdb-src (pdb-bd-pd pdb) >s
        ≈˘⟨ lift-sub-comp-lem-sub (liftSub (liftSub (pdb-tgt pdb))) (pdb-src (pdb-bd-pd pdb)) ⟩
      < ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ ∘
          liftSub (pdb-src (pdb-bd-pd pdb)) >s
        ≈˘⟨ lift-sub-comp-lem-sub ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ (liftSub (pdb-src (pdb-bd-pd pdb))) ⟩
      < ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ , 0V ⟩
          ∘ liftSub (liftSub (pdb-src (pdb-bd-pd pdb))) >s ∎
pdb-globular-1 (Restr {submax = zero} pdb) = pdb-globular-1 pdb
pdb-globular-1 (Restr {submax = suc submax} pdb) = pdb-globular-1 pdb

pd-globular-1 : (pd : Γ ⊢pd₀ suc (suc d))
              → pd-src pd ∘ pd-src (pd-bd-pd pd) ≃s pd-tgt pd ∘ pd-src (pd-bd-pd pd)
pd-globular-1 (Finish pdb) = pdb-globular-1 pdb

pdb-globular-lem-2 : (pdb : Γ ⊢pd[ submax ][ d ])
                   → .⦃ _ : is-zero submax ⦄
                   → .⦃ _ : NonZero′ (submax + d) ⦄
                   → (σ : Sub (ctxLength Γ) l)
                   → (τ : Sub (ctxLength Γ) l)
                   → (t : Tm (suc (suc l)))
                   → σ ∘ pdb-tgt pdb ≃s τ ∘ pdb-tgt pdb
                   → liftSub (liftSub σ) ∘ pdb-tgt pdb ≃s replacePdSub (liftSub (liftSub τ)) t ∘ pdb-tgt pdb
pdb-globular-lem-2 (Extend {submax = zero} pdb) ⟨ σ , x ⟩ ⟨ τ , y ⟩ t (Ext≃ p q) = Ext≃ l1 l2
  where
    l1 : ⟨ liftSub (liftSub σ) , liftTerm (liftTerm x) ⟩
           ∘ liftSub (liftSub (liftSub (idSub _)))
           ≃s
         ⟨ liftSub (liftSub τ) , t ⟩
           ∘ liftSub (liftSub (liftSub (idSub _)))
    l1 = begin
      < ⟨ liftSub (liftSub σ) , liftTerm (liftTerm x) ⟩ ∘ liftSub (liftSub (liftSub (idSub _))) >s
        ≈⟨ apply-lifted-sub-sub-≃ (liftSub (liftSub (liftSub (idSub _)))) ⟨ liftSub σ , liftTerm x ⟩ ⟩
      < liftSub (⟨ liftSub σ , liftTerm x ⟩ ∘ liftSub (liftSub (liftSub (idSub _)))) >s
        ≈⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (liftSub (liftSub (liftSub (idSub _)))) ⟨ σ , x ⟩) ⟩
      < liftSub (liftSub (⟨ σ , x ⟩ ∘ liftSub (liftSub (liftSub (idSub _))))) >s
        ≈⟨ lift-sub-≃ (lift-sub-≃ p) ⟩
      < liftSub (liftSub (⟨ τ , y ⟩ ∘ liftSub (liftSub (liftSub (idSub _))))) >s
        ≈˘⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (liftSub (liftSub (liftSub (idSub _)))) ⟨ τ , y ⟩) ⟩
      < liftSub (liftSub ⟨ τ , y ⟩ ∘ liftSub (liftSub (liftSub (idSub _)))) >s
        ≈˘⟨ apply-lifted-sub-sub-≃ (liftSub (liftSub (liftSub (idSub _)))) (liftSub ⟨ τ , y ⟩) ⟩
      < liftSub (liftSub ⟨ τ , y ⟩) ∘ liftSub (liftSub (liftSub (idSub _))) >s
        ≈⟨ lift-sub-comp-lem-sub (liftSub (liftSub τ)) (liftSub (liftSub (idSub _))) ⟩
      < liftSub (liftSub τ) ∘ liftSub (liftSub (idSub _)) >s
        ≈˘⟨ lift-sub-comp-lem-sub (liftSub (liftSub τ)) (liftSub (liftSub (idSub _))) ⟩
      < ⟨ liftSub (liftSub τ) , t ⟩ ∘ liftSub (liftSub (liftSub (idSub _))) >s ∎
      where
         open Reasoning sub-setoid

    l2 : 0V [ liftSub (liftSub σ) ]tm ≃tm 0V [ liftSub (liftSub τ) ]tm
    l2 = begin
      < 0V [ liftSub (liftSub σ) ]tm >tm ≈⟨ apply-lifted-sub-tm-≃ 0V (liftSub σ) ⟩
      < liftTerm (0V [ liftSub σ ]tm) >tm ≈⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ 0V σ) ⟩
      < liftTerm (liftTerm (0V [ σ ]tm)) >tm ≈⟨ lift-tm-≃ (lift-tm-≃ q) ⟩
      < liftTerm (liftTerm (0V [ τ ]tm)) >tm ≈˘⟨ lift-tm-≃ (apply-lifted-sub-tm-≃ 0V τ) ⟩
      < liftTerm (0V [ liftSub τ ]tm) >tm ≈˘⟨ apply-lifted-sub-tm-≃ 0V (liftSub τ) ⟩
      < 0V [ liftSub (liftSub τ) ]tm >tm ∎
      where
        open Reasoning tm-setoid
pdb-globular-lem-2 (Extend {submax = suc zero} pdb) ⟨ σ , x ⟩ ⟨ τ , y ⟩ t p with pdb-tgt pdb
... | ⟨ μ , z ⟩ = begin
  < (⟨ liftSub (liftSub σ) , liftTerm (liftTerm x) ⟩ ∘ ⟨ liftSub (liftSub μ) , 1V ⟩) >s
    ≈⟨ apply-lifted-sub-sub-≃ ⟨ liftSub (liftSub μ) , 1V ⟩ ⟨ liftSub σ , liftTerm x ⟩ ⟩
  < liftSub (⟨ liftSub σ , liftTerm x ⟩ ∘ ⟨ liftSub (liftSub μ) , 1V ⟩) >s
    ≈⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (⟨ liftSub (liftSub μ) , 1V ⟩) ⟨ σ , x ⟩) ⟩
  < liftSub (liftSub (⟨ σ , x ⟩ ∘ ⟨ liftSub (liftSub μ) , 1V ⟩)) >s
    ≈⟨ lift-sub-≃ (lift-sub-≃ p) ⟩
  < (liftSub (liftSub (⟨ τ , y ⟩ ∘ ⟨ liftSub (liftSub μ) , 1V ⟩))) >s
    ≈˘⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (⟨ liftSub (liftSub μ) , 1V ⟩) ⟨ τ , y ⟩) ⟩
  < liftSub (liftSub ⟨ τ , y ⟩ ∘ ⟨ liftSub (liftSub μ) , 1V ⟩) >s
    ≈˘⟨ apply-lifted-sub-sub-≃ (⟨ liftSub (liftSub μ) , 1V ⟩) (liftSub ⟨ τ , y ⟩) ⟩
  < liftSub (liftSub ⟨ τ , y ⟩) ∘ ⟨ liftSub (liftSub μ) , 1V ⟩ >s
    ≈⟨ lift-sub-comp-lem-sub (liftSub (liftSub τ)) ⟨ liftSub μ , 0V ⟩ ⟩
  < liftSub (liftSub τ) ∘ ⟨ liftSub μ , 0V ⟩ >s
    ≈˘⟨ lift-sub-comp-lem-sub (liftSub (liftSub τ)) ⟨ liftSub μ , 0V ⟩ ⟩
  < ⟨ liftSub (liftSub τ) , t ⟩ ∘ ⟨ liftSub (liftSub μ) , 1V ⟩ >s ∎
  where
    open Reasoning sub-setoid


pdb-globular-2 : (pdb : Γ ⊢pd[ submax ][ d ])
               → .⦃ nz : NonZero′ (submax + d) ⦄
               → .⦃ nz2 : NonZero′ ((pred submax) + (newDim submax d)) ⦄
               → pdb-src pdb ∘ pdb-tgt (pdb-bd-pd pdb) ≃s pdb-tgt pdb ∘ pdb-tgt (pdb-bd-pd pdb)
pdb-globular-2 (Extend {submax = zero} pdb) = pdb-globular-lem-2 pdb (idSub _) (idSub _) 1V refl≃s
pdb-globular-2 (Extend {submax = suc zero} pdb) = pdb-globular-lem-2 (pdb-bd-pd pdb) (pdb-src pdb) (pdb-tgt pdb) 1V (pdb-globular-2 pdb)
pdb-globular-2 (Extend {submax = suc (suc zero)} pdb) with pdb-tgt (pdb-bd-pd pdb) | pdb-globular-2 pdb
... | ⟨ μ , z ⟩ | Ext≃ p q = Ext≃ lem refl≃tm
  where
    open Reasoning sub-setoid
    lem : ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , Var (suc zero) ⟩ , Var zero ⟩ ∘ liftSub (liftSub μ)
            ≃s
          ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , Var (suc zero) ⟩ , Var zero ⟩ ∘ liftSub (liftSub μ)
    lem = begin
      < ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , Var (suc zero) ⟩ , Var zero ⟩ ∘ liftSub (liftSub μ) >s
        ≈⟨ lift-sub-comp-lem-sub ⟨ liftSub (liftSub (pdb-src pdb)) , Var (suc zero) ⟩ (liftSub μ) ⟩
      < ⟨ liftSub (liftSub (pdb-src pdb)) , Var (suc zero) ⟩ ∘ liftSub μ >s
        ≈⟨ lift-sub-comp-lem-sub (liftSub (liftSub (pdb-src pdb))) μ ⟩
      < liftSub (liftSub (pdb-src pdb)) ∘ μ >s
        ≈⟨ apply-lifted-sub-sub-≃ μ (liftSub (pdb-src pdb)) ⟩
      < liftSub (liftSub (pdb-src pdb) ∘ μ) >s
        ≈⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ μ (pdb-src pdb)) ⟩
      < liftSub (liftSub (pdb-src pdb ∘ μ)) >s
        ≈⟨ lift-sub-≃ (lift-sub-≃ p) ⟩
      < liftSub (liftSub (pdb-tgt pdb ∘ μ)) >s
        ≈˘⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ μ (pdb-tgt pdb)) ⟩
      < liftSub (liftSub (pdb-tgt pdb) ∘ μ) >s
        ≈˘⟨ apply-lifted-sub-sub-≃ μ (liftSub (pdb-tgt pdb)) ⟩
      < liftSub (liftSub (pdb-tgt pdb)) ∘ μ >s
        ≈˘⟨ lift-sub-comp-lem-sub (liftSub (liftSub (pdb-tgt pdb))) μ ⟩
      < ⟨ liftSub (liftSub (pdb-tgt pdb)) , Var (suc zero) ⟩ ∘ liftSub μ
        >s
        ≈˘⟨ lift-sub-comp-lem-sub ⟨ liftSub (liftSub (pdb-tgt pdb)) , Var (suc zero) ⟩ (liftSub μ) ⟩
      < ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , Var (suc zero) ⟩ , Var zero ⟩ ∘ liftSub (liftSub μ) >s ∎
pdb-globular-2 (Extend {submax = suc (suc (suc submax))} pdb) = Ext≃ (Ext≃ lem refl≃tm) refl≃tm
  where
    open Reasoning sub-setoid
    lem : ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , 1V ⟩ , 0V ⟩
            ∘ liftSub (liftSub (pdb-tgt (pdb-bd-pd pdb)))
            ≃s
          ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , 1V ⟩ , 0V ⟩
            ∘ liftSub (liftSub (pdb-tgt (pdb-bd-pd pdb)))
    lem = begin
      < ⟨ ⟨ liftSub (liftSub (pdb-src pdb)) , Var (suc zero) ⟩ , Var zero ⟩
          ∘ liftSub (liftSub (pdb-tgt (pdb-bd-pd pdb))) >s
        ≈⟨ lift-sub-comp-lem-sub ⟨ liftSub (liftSub (pdb-src pdb)) , Var (suc zero) ⟩ (liftSub (pdb-tgt (pdb-bd-pd pdb))) ⟩
      < ⟨ liftSub (liftSub (pdb-src pdb)) , Var (suc zero) ⟩
          ∘ liftSub (pdb-tgt (pdb-bd-pd pdb)) >s
        ≈⟨ lift-sub-comp-lem-sub (liftSub (liftSub (pdb-src pdb))) (pdb-tgt (pdb-bd-pd pdb)) ⟩
      < liftSub (liftSub (pdb-src pdb)) ∘ pdb-tgt (pdb-bd-pd pdb) >s
        ≈⟨ apply-lifted-sub-sub-≃ (pdb-tgt (pdb-bd-pd pdb)) (liftSub (pdb-src pdb)) ⟩
      < liftSub (liftSub (pdb-src pdb) ∘ pdb-tgt (pdb-bd-pd pdb)) >s
        ≈⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (pdb-tgt (pdb-bd-pd pdb)) (pdb-src pdb)) ⟩
      < liftSub (liftSub (pdb-src pdb ∘ pdb-tgt (pdb-bd-pd pdb))) >s
        ≈⟨ lift-sub-≃ (lift-sub-≃ (pdb-globular-2 pdb)) ⟩
      < liftSub (liftSub (pdb-tgt pdb ∘ pdb-tgt (pdb-bd-pd pdb))) >s
        ≈˘⟨ lift-sub-≃ (apply-lifted-sub-sub-≃ (pdb-tgt (pdb-bd-pd pdb)) (pdb-tgt pdb)) ⟩
      < liftSub (liftSub (pdb-tgt pdb) ∘ pdb-tgt (pdb-bd-pd pdb)) >s
        ≈˘⟨ apply-lifted-sub-sub-≃ (pdb-tgt (pdb-bd-pd pdb)) (liftSub (pdb-tgt pdb)) ⟩
      < liftSub (liftSub (pdb-tgt pdb)) ∘ pdb-tgt (pdb-bd-pd pdb) >s
        ≈˘⟨ lift-sub-comp-lem-sub (liftSub (liftSub (pdb-tgt pdb))) (pdb-tgt (pdb-bd-pd pdb)) ⟩
      < ⟨ liftSub (liftSub (pdb-tgt pdb)) , Var (suc zero) ⟩
          ∘ liftSub (pdb-tgt (pdb-bd-pd pdb)) >s
        ≈˘⟨ lift-sub-comp-lem-sub ⟨ liftSub (liftSub (pdb-tgt pdb)) , Var (suc zero) ⟩ (liftSub (pdb-tgt (pdb-bd-pd pdb))) ⟩
      < ⟨ ⟨ liftSub (liftSub (pdb-tgt pdb)) , Var (suc zero) ⟩ , Var zero ⟩
          ∘ liftSub (liftSub (pdb-tgt (pdb-bd-pd pdb))) >s ∎
pdb-globular-2 (Restr {submax = zero} pdb) = pdb-globular-2 pdb
pdb-globular-2 (Restr {submax = suc submax} pdb) = pdb-globular-2 pdb

pd-globular-2 : (pd : Γ ⊢pd₀ suc (suc d))
              → pd-src pd ∘ pd-tgt (pd-bd-pd pd) ≃s pd-tgt pd ∘ pd-tgt (pd-bd-pd pd)
pd-globular-2 (Finish pdb) = pdb-globular-2 pdb
