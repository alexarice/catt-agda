module Catt.Tree.Structured.Globular.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.ToTerm

sty-dim-≃ : As ≃sty Bs → sty-dim As ≡ sty-dim Bs
sty-dim-≃ {As = S⋆} {Bs = S⋆} p = refl
sty-dim-≃ {As = SArr _ As _} {Bs = SArr _ Bs _} [ Arr≃ _ p _ ] = cong suc (sty-dim-≃ [ p ])

sty-src-≃ : (p : As ≃sty Bs) → .⦃ _ : NonZero (sty-dim As) ⦄ → sty-src As ≃stm sty-src Bs ⦃ NonZero-subst (sty-dim-≃ p) it ⦄
sty-src-≃ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≃ p _ _ ] = [ p ]

sty-tgt-≃ : (p : As ≃sty Bs) → .⦃ _ : NonZero (sty-dim As) ⦄ → sty-tgt As ≃stm sty-tgt Bs ⦃ NonZero-subst (sty-dim-≃ p) it ⦄
sty-tgt-≃ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≃ _ _ p ] = [ p ]

sty-base-≃ : (p : As ≃sty Bs) → sty-base As ≃sty sty-base Bs
sty-base-≃ {As = S⋆} {Bs = S⋆} [ Star≃ x ] = [ Star≃ x ]
sty-base-≃ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≃ _ p _ ] = [ p ]

sty-prop : (As : STy X) → .⦃ _ : NonZero (sty-dim As) ⦄ → SArr (sty-src As) (sty-base As) (sty-tgt As) ≃sty As
sty-prop (SArr s As t) = refl≃sty

sty-dim-label : (As : STy (someTree S)) → (L : Label-WT X S) → sty-dim (As >>=′ L) ≡ sty-dim As + sty-dim (lty L)
sty-dim-label S⋆ L = refl
sty-dim-label (SArr s As t) L = cong suc (sty-dim-label As L)

sty-to-type-dim : (As : STy X) → ty-dim (sty-to-type As) ≡ sty-dim As
sty-to-type-dim S⋆ = refl
sty-to-type-dim (SArr s As t) = cong suc (sty-to-type-dim As)

truncate-sty′-≃ : d ≡ d′ → As ≃sty Bs → truncate-sty′ d As ≃sty truncate-sty′ d′ Bs
truncate-sty′-≃ {d = zero} refl q = q
truncate-sty′-≃ {d = suc d} refl q = truncate-sty′-≃ {d = d} refl (sty-base-≃ q)

truncate-sty-≃ : d ≡ d′ → As ≃sty Bs → truncate-sty d As ≃sty truncate-sty d′ Bs
truncate-sty-≃ {d = d} refl q = truncate-sty′-≃ (cong (_∸ d) (sty-dim-≃ q)) q

truncate-sty-1-map-ext : (As : STy (someTree S)) → truncate-sty 1 (map-sty-ext {T = T} As) ≃sty SArr SHere S⋆ (SPath (PShift {T = T} {S = S} PHere))
truncate-sty-1-map-ext S⋆ = SArr≃ refl≃stm refl≃sty (compute-2 refl≃stm)
truncate-sty-1-map-ext (SArr s S⋆ t) = SArr≃ refl≃stm refl≃sty (compute-2 refl≃stm)
truncate-sty-1-map-ext (SArr _ (SArr s As t) _) = truncate-sty-1-map-ext (SArr s As t)

truncate-sty-1-1-Full : (As : STy (someTree S)) → ⦃ 1-Full As ⦄ → truncate-sty 1 As ≃sty SArr SHere S⋆ (SPath (last-path S))
truncate-sty-1-1-Full (SArr s S⋆ t) = SArr≃ it refl≃sty it
truncate-sty-1-1-Full (SArr _ As@(SArr _ _ _) _) = truncate-sty-1-1-Full As

truncate-sty′-label : (d : ℕ) → (As : STy (someTree S)) → (L : Label-WT X S) → d ≤ sty-dim As → truncate-sty′ d (As >>=′ L) ≃sty truncate-sty′ d As >>=′ L
truncate-sty′-label zero As L p = refl≃sty
truncate-sty′-label (suc d) (SArr s As t) L p = truncate-sty′-label d As L (≤-pred p)

truncate-sty-label : (d : ℕ) → (As : STy (someTree S)) → (L : Label-WT X S) → truncate-sty (d + sty-dim (lty L)) (As >>=′ L) ≃sty truncate-sty d As >>=′ L
truncate-sty-label d As L = begin
  < truncate-sty (d + sty-dim (lty L)) (As >>=′ L) >sty
    ≡⟨⟩
  < truncate-sty′ (sty-dim (As >>=′ L) ∸ (d + sty-dim (lty L))) (As >>=′ L) >sty
    ≈⟨ truncate-sty′-≃ lem refl≃sty ⟩
  < truncate-sty′ (sty-dim As ∸ d) (As >>=′ L) >sty
    ≈⟨ truncate-sty′-label (sty-dim As ∸ d) As L (m∸n≤m (sty-dim As) d) ⟩
  < truncate-sty′ (sty-dim As ∸ d) As >>=′ L >sty
    ≡⟨⟩
  < truncate-sty d As >>=′ L >sty ∎
  where
    lem : sty-dim (As >>=′ L) ∸ (d + sty-dim (lty L)) ≡ sty-dim As ∸ d
    lem = begin
      sty-dim (As >>=′ L) ∸ (d + sty-dim (lty L))
        ≡⟨ cong (_∸ (d + sty-dim (lty L))) (sty-dim-label As L) ⟩
      (sty-dim As + sty-dim (lty L)) ∸ (d + sty-dim (lty L))
        ≡⟨ cong (sty-dim As + sty-dim (lty L) ∸_) (+-comm d (sty-dim (lty L))) ⟩
      sty-dim As + sty-dim (lty L) ∸ (sty-dim (lty L) + d)
        ≡˘⟨ ∸-+-assoc (sty-dim As + sty-dim (lty L)) (sty-dim (lty L)) d ⟩
      sty-dim As + sty-dim (lty L) ∸ sty-dim (lty L) ∸ d
        ≡⟨ cong (_∸ d) (m+n∸n≡m (sty-dim As) (sty-dim (lty L))) ⟩
      sty-dim As ∸ d ∎
      where
        open ≡-Reasoning
    open Reasoning sty-setoid

truncate-sty-≤ : (d : ℕ) → (As : STy X) → (d < sty-dim As) → truncate-sty d As ≃sty truncate-sty d (sty-base As)
truncate-sty-≤ d (SArr s As t) p
  rewrite +-∸-assoc 1 p = refl≃sty

sty-base-dim : (As : STy X) → sty-dim (sty-base As) ≡ pred (sty-dim As)
sty-base-dim S⋆ = refl
sty-base-dim (SArr s As t) = refl
