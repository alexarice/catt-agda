module Catt.Pasting.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Pasting

pdb-odd-length : {Γ : Ctx m} → Γ ⊢pdb → Odd m
pdb-odd-length Base = tt
pdb-odd-length (Extend pdb p q) = pdb-odd-length pdb
pdb-odd-length (Restr pdb) = pdb-odd-length pdb

pdb-≃ : Γ ≃c Δ → Γ ⊢pdb → Δ ⊢pdb
pdb-≃ p pdb with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = pdb

pdb-≃-focus-ty : (p : Γ ≃c Δ) → (pdb : Γ ⊢pdb) → focus-ty (pdb-≃ p pdb) ≃ty focus-ty pdb
pdb-≃-focus-ty p pdb with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = refl≃ty

pdb-≃-focus-tm : (p : Γ ≃c Δ) → (pdb : Γ ⊢pdb) → focus-tm (pdb-≃ p pdb) ≃tm focus-tm pdb
pdb-≃-focus-tm p pdb with ≃c-preserve-length p
... | refl with ≃c-to-≡ p
... | refl = refl≃tm

pdb-proj₁ : (pdb : (Γ , B , A) ⊢pdb) → B ≃ty focus-ty (pdb-prefix pdb)
pdb-proj₁ (Extend pdb p q) = p
pdb-proj₁ (Restr pdb) = pdb-proj₁ pdb

pdb-proj₂ : (pdb : Γ , B , A ⊢pdb) → A ≃ty wk-tm (focus-tm (pdb-prefix pdb)) ─⟨ wk-ty (focus-ty (pdb-prefix pdb)) ⟩⟶ 0V
pdb-proj₂ (Extend pdb p q) = q
pdb-proj₂ (Restr pdb) = pdb-proj₂ pdb

focus-ty-dim-to-non-empty : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pdb) → (1 ≤ ty-dim (focus-ty pdb)) → NonZero n
focus-ty-dim-to-non-empty (Extend pdb p q) x = it
focus-ty-dim-to-non-empty (Restr pdb) x = focus-ty-dim-to-non-empty pdb (≤-trans x (≤-trans (≤-reflexive (ty-dim-ty-base (focus-ty pdb))) pred[n]≤n))

pdb-singleton-lem : ∅ , A ⊢pdb → A ≃ty ⋆ {n = 0}
pdb-singleton-lem Base = refl≃ty
pdb-singleton-lem (Restr pdb) = pdb-singleton-lem pdb

pdb-dim-lem : (pdb : Γ , A ⊢pdb) → ty-dim (focus-ty pdb) ≤ ty-dim A
pdb-dim-lem Base = z≤n
pdb-dim-lem (Extend pdb p q) = ≤-reflexive (wk-ty-dim _)
pdb-dim-lem (Restr pdb) = ≤-trans (≤-trans (≤-reflexive (ty-dim-ty-base (focus-ty pdb))) pred[n]≤n) (pdb-dim-lem pdb)

pdb-irrel : (pdb pdb2 : Γ ⊢pdb) → ty-dim (focus-ty pdb) ≡ ty-dim (focus-ty pdb2) → pdb ≡ pdb2
pdb-irrel Base Base x = refl
pdb-irrel Base (Restr pdb2) x = ⊥-elim (NonZero-⊥ (pdb-dim-lem pdb2))
pdb-irrel (Extend {B = B} pdb p q) (Extend pdb2 p′ q′) x with pdb-irrel pdb pdb2 lem
  where
    open ≡-Reasoning
    lem : ty-dim (focus-ty pdb) ≡ ty-dim (focus-ty pdb2)
    lem = cong pred (begin
      suc (ty-dim (focus-ty pdb))
        ≡˘⟨ cong suc (wk-ty-dim (focus-ty pdb)) ⟩
      suc (ty-dim (wk-ty (focus-ty pdb)))
        ≡˘⟨ ty-dim-≃ q ⟩
      ty-dim B
        ≡⟨ ty-dim-≃ q′ ⟩
      suc (ty-dim (wk-ty (focus-ty pdb2)))
        ≡⟨ cong suc (wk-ty-dim (focus-ty pdb2)) ⟩
      suc (ty-dim (focus-ty pdb2)) ∎)
... | refl = cong₂ (Extend pdb) (≃ty-irrel p p′) (≃ty-irrel q q′)
pdb-irrel (Extend {A = A} {B = B} pdb p q) (Restr pdb2) x = ⊥-elim (1+n≰n lem)
  where
    open ≤-Reasoning

    lem : suc (ty-dim (focus-ty pdb2)) ≤ ty-dim (focus-ty pdb2)
    lem = begin
      suc (ty-dim (focus-ty pdb2))
        ≤⟨ s≤s (pdb-dim-lem pdb2) ⟩
      suc (ty-dim B)
        ≡˘⟨ cong suc (wk-ty-dim B) ⟩
      suc (ty-dim (wk-ty B))
        ≡⟨ cong suc x ⟩
      suc (ty-dim (ty-base (focus-ty pdb2)))
        ≡⟨ cong suc (ty-dim-ty-base (focus-ty pdb2)) ⟩
      suc (pred (ty-dim (focus-ty pdb2)))
        ≡⟨ suc-pred (ty-dim (focus-ty pdb2)) ⟩
      ty-dim (focus-ty pdb2) ∎
pdb-irrel (Restr pdb) Base x = sym (pdb-irrel Base (Restr pdb) (sym x))
pdb-irrel (Restr pdb) (Extend pdb2 p q) x = sym (pdb-irrel (Extend pdb2 p q) (Restr pdb) (sym x))
pdb-irrel (Restr pdb) (Restr pdb2) x with pdb-irrel pdb pdb2 lem
  where
    open ≡-Reasoning
    lem : ty-dim (focus-ty pdb) ≡ ty-dim (focus-ty pdb2)
    lem = begin
      ty-dim (focus-ty pdb)
        ≡˘⟨ suc-pred (ty-dim (focus-ty pdb)) ⟩
      suc (pred (ty-dim (focus-ty pdb)))
        ≡˘⟨ cong suc (ty-dim-ty-base (focus-ty pdb)) ⟩
      suc (ty-dim (ty-base (focus-ty pdb)))
        ≡⟨ cong suc x ⟩
      suc (ty-dim (ty-base (focus-ty pdb2)))
        ≡⟨ cong suc (ty-dim-ty-base (focus-ty pdb2)) ⟩
      suc (pred (ty-dim (focus-ty pdb2)))
        ≡⟨ suc-pred (ty-dim (focus-ty pdb2)) ⟩
      ty-dim (focus-ty pdb2) ∎
... | refl = refl

pdb-max-dim : {Γ : Ctx n} → Γ ⊢pdb → ℕ
pdb-max-dim Base = 0
pdb-max-dim (Extend {B = B} pdb p q) = ty-dim B
pdb-max-dim (Restr pdb) = pdb-max-dim pdb

pdb-max-dim-is-A : {Γ : Ctx n} → (pdb : Γ , B , A ⊢pdb) → pdb-max-dim pdb ≡ ty-dim A
pdb-max-dim-is-A (Extend pdb p q) = refl
pdb-max-dim-is-A (Restr pdb) = pdb-max-dim-is-A pdb

pdb-max-dim-irrel : (pdb1 : Γ ⊢pdb) → (pdb2 : Γ ⊢pdb) → pdb-max-dim pdb1 ≡ pdb-max-dim pdb2
pdb-max-dim-irrel {Γ = ∅} pdb1 pdb2 = ⊥-elim (pdb-odd-length pdb1)
pdb-max-dim-irrel {Γ = ∅ , .⋆} Base Base = refl
pdb-max-dim-irrel {Γ = ∅ , .⋆} Base (Restr pdb2) = pdb-max-dim-irrel Base pdb2
pdb-max-dim-irrel {Γ = ∅ , A} (Restr pdb1) pdb2 = pdb-max-dim-irrel pdb1 pdb2
pdb-max-dim-irrel {Γ = Γ , B , A} pdb1 pdb2 = trans (pdb-max-dim-is-A pdb1) (sym (pdb-max-dim-is-A pdb2))

pdb-max-dim-is-max : (pdb : Γ ⊢pdb) → ty-dim (focus-ty pdb) ≤ pdb-max-dim pdb
pdb-max-dim-is-max Base = z≤n
pdb-max-dim-is-max (Extend pdb p q) = ≤-reflexive (wk-ty-dim _)
pdb-max-dim-is-max (Restr pdb) = ≤-trans (≤-trans (≤-reflexive (ty-dim-ty-base (focus-ty pdb))) pred[n]≤n) (pdb-max-dim-is-max pdb)

pdb-reduce-dim : (pdb : Γ ⊢pdb) → (d : ℕ) → (k : ℕ) → (d + k ≡ ty-dim (focus-ty pdb)) → Γ ⊢pdb
pdb-reduce-dim pdb d zero p = pdb
pdb-reduce-dim pdb d (suc k) p = pdb-reduce-dim (Restr pdb ⦃ NonZero-subst (trans (sym (+-suc d k)) p) it ⦄) d k lem
  where
    open ≡-Reasoning
    lem : d + k ≡ ty-dim (ty-base (focus-ty pdb))
    lem = begin
      d + k
        ≡˘⟨ cong pred (+-suc d k)  ⟩
      pred (d + suc k)
        ≡⟨ cong pred p ⟩
      pred (ty-dim (focus-ty pdb))
        ≡˘⟨ ty-dim-ty-base (focus-ty pdb) ⟩
      ty-dim (ty-base (focus-ty pdb)) ∎

pdb-reduce-dim-dim : (pdb : Γ ⊢pdb) → (d : ℕ) → (k : ℕ) → (p : d + k ≡ ty-dim (focus-ty pdb)) → d ≡ ty-dim (focus-ty (pdb-reduce-dim pdb d k p))
pdb-reduce-dim-dim pdb d zero p = trans (sym (+-identityʳ d)) p
pdb-reduce-dim-dim pdb d (suc k) p = pdb-reduce-dim-dim (Restr pdb ⦃ NonZero-subst (trans (sym (+-suc d k)) p) it ⦄) d k lem
  where
    open ≡-Reasoning
    lem : d + k ≡ ty-dim (ty-base (focus-ty pdb))
    lem = begin
      d + k
        ≡˘⟨ cong pred (+-suc d k)  ⟩
      pred (d + suc k)
        ≡⟨ cong pred p ⟩
      pred (ty-dim (focus-ty pdb))
        ≡˘⟨ ty-dim-ty-base (focus-ty pdb) ⟩
      ty-dim (ty-base (focus-ty pdb)) ∎

pdb-to-dim : {Γ : Ctx n} → (pdb : Γ ⊢pdb) → (d : ℕ) → (d ≤ pdb-max-dim pdb) → Γ ⊢pdb
pdb-to-dim pdb d p with d ≤″? ty-dim (focus-ty pdb)
... | yes (less-than-or-equal {k = k} q) = pdb-reduce-dim pdb d k q
pdb-to-dim Base .zero z≤n | no q = ⊥-elim (q (less-than-or-equal refl))
pdb-to-dim (Extend pdb p₁ q₁) d p | no q = ⊥-elim (q (≤⇒≤″ (≤-trans p (≤-reflexive (sym (wk-ty-dim _))))))
pdb-to-dim (Restr pdb) d p | no q = pdb-to-dim pdb d p

pdb-to-dim-dim : {Γ : Ctx n} → (pdb : Γ ⊢pdb) → (d : ℕ) → (p : d ≤ pdb-max-dim pdb) → d ≡ ty-dim (focus-ty (pdb-to-dim pdb d p))
pdb-to-dim-dim pdb d p with d ≤″? ty-dim (focus-ty pdb)
... | yes (less-than-or-equal {k = k} q) = pdb-reduce-dim-dim pdb d k q
pdb-to-dim-dim Base .zero z≤n | no q = ⊥-elim (q (less-than-or-equal refl))
pdb-to-dim-dim (Extend pdb p₁ q₁) d p | no q = ⊥-elim (q (≤⇒≤″ (≤-trans p (≤-reflexive (sym (wk-ty-dim _))))))
pdb-to-dim-dim (Restr pdb) d p | no q = pdb-to-dim-dim pdb d p

pdb-dec : (Γ : Ctx n) → Dec (Γ ⊢pdb)
pdb-dec ∅ = no (λ x → pdb-odd-length x)
pdb-dec (∅ , ⋆) = yes Base
pdb-dec (∅ , s ─⟨ A ⟩⟶ t) = no (λ x → no-term-in-empty-context s)
pdb-dec (Γ , B , A) with (pdb-dec Γ)
... | no d = no (λ x → d (pdb-prefix x))
... | yes d with (ty-dim B ≤? pdb-max-dim d)
... | no q = no (λ x → q (≤-trans (≤-reflexive (ty-dim-≃ (pdb-proj₁ x))) (≤-trans (pdb-max-dim-is-max (pdb-prefix x)) (≤-reflexive (pdb-max-dim-irrel (pdb-prefix x) d)))))
... | yes q with ≃ty-dec B (focus-ty new-pdb) | ≃ty-dec A (wk-tm (focus-tm new-pdb) ─⟨ wk-ty (focus-ty new-pdb) ⟩⟶ 0V)
  where new-pdb = pdb-to-dim d (ty-dim B) q
... | yes p | yes r = yes (Extend (pdb-to-dim d (ty-dim B) q) p r)
... | yes p | no r = no (λ x → r (trans≃ty (pdb-proj₂ x) (reflexive≃ty (cong (λ y → wk-tm (focus-tm y) ─⟨ wk-ty (focus-ty y) ⟩⟶ 0V) (pdb-irrel (pdb-prefix x) (pdb-to-dim d (ty-dim B) q) (trans (sym (ty-dim-≃ (pdb-proj₁ x))) (pdb-to-dim-dim d (ty-dim B) q)))))))
... | no p | r = no (λ x → p (trans≃ty (pdb-proj₁ x) (reflexive≃ty (cong focus-ty (pdb-irrel (pdb-prefix x) (pdb-to-dim d (ty-dim B) q) (trans (sym (ty-dim-≃ (pdb-proj₁ x))) (pdb-to-dim-dim d (ty-dim B) q)))))))

pdb-to-pd : (Γ : Ctx n) → Γ ⊢pdb → Γ ⊢pd
pdb-to-pd Γ pdb = Finish (pdb-to-dim pdb 0 z≤n) ⦃ IsZero-subst (pdb-to-dim-dim pdb 0 z≤n) it ⦄

pd-dec : (Γ : Ctx n) → Dec (Γ ⊢pd)
pd-dec Γ with pdb-dec Γ
... | yes p = yes (pdb-to-pd Γ p)
... | no p = no (λ where (Finish x) → p x)

right-base-≃ : A ≃ty B → s ≃tm t → right-base A s ≃tm right-base B t
right-base-≃ (Star≃ x) q = q
right-base-≃ (Arr≃ x p q) _ = right-base-≃ p q

right-base-< : 0 < ty-dim A → right-base A s ≃tm right-base A t
right-base-< {A = s ─⟨ A ⟩⟶ t} p = refl≃tm

right-base-base : (A : Ty n) → .⦃ _ : NonZero (ty-dim A) ⦄ → right-base A s ≃tm right-base (ty-base A) (ty-tgt A)
right-base-base (s ─⟨ A ⟩⟶ t) = refl≃tm

right-base-wk : (A : Ty n) → (t : Tm n) → right-base (wk-ty A) (wk-tm t) ≃tm wk-tm (right-base A t)
right-base-wk ⋆ t = refl≃tm
right-base-wk (s ─⟨ A ⟩⟶ t) _ = right-base-wk A t

pdb-right-base-prefix : (pdb : Γ , B , A ⊢pdb) → 0 < ty-dim B → pdb-right-base pdb ≃tm wk-tm (wk-tm (pdb-right-base (pdb-prefix pdb)))
pdb-right-base-prefix (Extend pdb p q) x = begin
  < pdb-right-base (Extend pdb p q) >tm
    ≈⟨ right-base-≃ (wk-ty-≃ q) refl≃tm ⟩
  < right-base (wk-ty (wk-ty (focus-ty pdb))) (wk-tm (Var zero)) >tm
    ≈⟨ right-base-< (<-≤-trans x (≤-reflexive (trans (ty-dim-≃ p) (sym (trans (wk-ty-dim (wk-ty (focus-ty pdb))) (wk-ty-dim (focus-ty pdb))))))) ⟩
  < right-base (wk-ty (wk-ty (focus-ty pdb))) (wk-tm (wk-tm (focus-tm pdb))) >tm
    ≈⟨ right-base-wk (wk-ty (focus-ty pdb)) (wk-tm (focus-tm pdb)) ⟩
  < wk-tm (right-base (wk-ty (focus-ty pdb)) (wk-tm (focus-tm pdb))) >tm
    ≈⟨ wk-tm-≃ (right-base-wk (focus-ty pdb) (focus-tm pdb)) ⟩
  < wk-tm (wk-tm (right-base (focus-ty pdb) (focus-tm pdb))) >tm ∎
  where
    open Reasoning tm-setoid
pdb-right-base-prefix (Restr pdb) x = begin
  < pdb-right-base (Restr pdb) >tm
    ≈˘⟨ right-base-base (focus-ty pdb) ⟩
  < pdb-right-base pdb >tm
    ≈⟨ pdb-right-base-prefix pdb x ⟩
  < wk-tm (wk-tm (pdb-right-base (pdb-prefix (Restr pdb)))) >tm ∎
  where
    open Reasoning tm-setoid

pd-right-base : (pd : Γ ⊢pd) → pdb-right-base (pd-to-pdb pd) ≃tm pd-focus-tm pd
pd-right-base (Finish pdb) with focus-ty pdb
... | ⋆ = refl≃tm

pdb-dim-proj : (pdb : Γ , B , A ⊢pdb) → ty-dim A ≡ suc (ty-dim B)
pdb-dim-proj (Extend pdb p q) = trans (ty-dim-≃ q) (cong suc (trans (wk-ty-dim (focus-ty pdb)) (ty-dim-≃ (sym≃ty p))))
pdb-dim-proj (Restr pdb) = pdb-dim-proj pdb

pdb-right-base-0-dim : (pdb : Γ , B , A ⊢pdb) → ty-dim B ≡ 0 → pdb-right-base pdb ≃tm 1V {n = 2 + ctxLength Γ}
pdb-right-base-0-dim (Extend pdb p q) x = trans≃tm (right-base-≃ (wk-ty-≃ q) refl≃tm) (right-base-≃ (wk-ty-≃ (wk-ty-≃ (⋆-is-only-0-d-ty {A = focus-ty pdb} ⦃ IsZero-subst (trans (sym x) (ty-dim-≃ p)) it ⦄))) refl≃tm)
pdb-right-base-0-dim (Restr (Extend pdb p q)) x = trans≃tm (sym≃tm (right-base-base (wk-ty _))) (pdb-right-base-0-dim (Extend pdb p q) x)
pdb-right-base-0-dim {B = B} {A = A} (Restr (Restr pdb)) x = ⊥-elim (NonZero-⊥ lem)
  where
    lem : ty-dim (ty-base (focus-ty pdb)) ≤ 0
    lem = begin
      ty-dim (ty-base (focus-ty pdb))
        ≡⟨ ty-dim-ty-base (focus-ty pdb) ⟩
      pred (ty-dim (focus-ty pdb))
        ≤⟨ pred-mono-≤ (pdb-dim-lem pdb) ⟩
      pred (ty-dim A)
        ≡⟨ cong pred (pdb-dim-proj pdb) ⟩
      ty-dim B
        ≡⟨ x ⟩
      0 ∎
      where
        open ≤-Reasoning

focus-ty-is-globular : (pdb : Γ ⊢pdb) → ty-is-globular (focus-ty pdb)
focus-tm-is-globular : (pdb : Γ ⊢pdb) → isVar (focus-tm pdb)

focus-ty-is-globular Base = tt
focus-ty-is-globular (Extend pdb p q) = wk-ty-preserve-is-globular _ (≃ty-preserve-globular (sym≃ty q) ((wk-tm-preserve-isVar (focus-tm pdb) (focus-tm-is-globular pdb)) ,, ((wk-ty-preserve-is-globular (focus-ty pdb) (focus-ty-is-globular pdb)) ,, tt)))
focus-ty-is-globular (Restr pdb) = ty-base-globular (focus-ty pdb) (focus-ty-is-globular pdb)

focus-tm-is-globular Base = tt
focus-tm-is-globular (Extend pdb p q) = tt
focus-tm-is-globular (Restr pdb) = ty-tgt-globular (focus-ty pdb) (focus-ty-is-globular pdb)

right-base-isVar : (A : Ty n) → ty-is-globular A → (t : Tm n) → isVar t → isVar (right-base A t)
right-base-isVar ⋆ g t iv = iv
right-base-isVar (s ─⟨ A ⟩⟶ t) (g1 ,, g2 ,, g3) _ _ = right-base-isVar A g2 t g3

pdb-right-base-isVar : (pdb : Γ ⊢pdb) → isVar (pdb-right-base pdb)
pdb-right-base-isVar pdb = right-base-isVar (focus-ty pdb) (focus-ty-is-globular pdb) (focus-tm pdb) (focus-tm-is-globular pdb)

pdb-length-prop : (pdb : Γ ⊢pdb) → 1 + pdb-length pdb * 2 ≡ ctxLength Γ
pdb-length-prop Base = refl
pdb-length-prop (Extend pdb p q) = cong 2+ (pdb-length-prop pdb)
pdb-length-prop (Restr pdb) = pdb-length-prop pdb

pdb-focus-dim-prop : (pdb : Γ ⊢pdb) → pdb-focus-dim pdb ≡ ty-dim (focus-ty pdb)
pdb-focus-dim-prop Base = refl
pdb-focus-dim-prop (Extend {B = B} pdb p q) = begin
  suc (pdb-focus-dim pdb)
    ≡⟨ cong suc (pdb-focus-dim-prop pdb) ⟩
  suc (ty-dim (focus-ty pdb))
    ≡˘⟨ cong suc (wk-ty-dim (focus-ty pdb)) ⟩
  suc (ty-dim (wk-ty (focus-ty pdb)))
    ≡˘⟨ ty-dim-≃ q ⟩
  ty-dim B
    ≡˘⟨ wk-ty-dim B ⟩
  ty-dim (wk-ty B) ∎
  where
    open ≡-Reasoning
pdb-focus-dim-prop (Restr pdb) = begin
  pred (pdb-focus-dim pdb)
    ≡⟨ cong pred (pdb-focus-dim-prop pdb) ⟩
  pred (ty-dim (focus-ty pdb))
    ≡˘⟨ ty-dim-ty-base (focus-ty pdb) ⟩
  ty-dim (ty-base (focus-ty pdb)) ∎
  where
    open ≡-Reasoning

pdb-non-empty : {Γ : Ctx n} → (Γ ⊢pdb) → NonZero n
pdb-non-empty pdb = Odd-is-NonZero _ (pdb-odd-length pdb)

pd-non-empty : {Γ : Ctx n} → (Γ ⊢pd) → NonZero n
pd-non-empty (Finish pdb) = pdb-non-empty pdb
