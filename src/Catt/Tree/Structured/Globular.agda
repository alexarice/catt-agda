module Catt.Tree.Structured.Globular where

open import Catt.Prelude
open import Catt.Tree.Structured

sty-dim : STy X → ℕ
sty-dim S⋆ = 0
sty-dim (SArr s A t) = suc (sty-dim A)

sty-base : STy X → STy X
sty-base S⋆ = S⋆
sty-base (SArr s As t) = As

sty-src : (As : STy X) → .⦃ NonZero (sty-dim As) ⦄ → STm X
sty-src (SArr s As t) = s

sty-tgt : (As : STy X) → .⦃ NonZero (sty-dim As) ⦄ → STm X
sty-tgt (SArr s As t) = t

truncate-sty′ : ℕ → STy X → STy X
truncate-sty′ zero As = As
truncate-sty′ (suc d) As = truncate-sty′ d (sty-base As)

truncate-sty : ℕ → STy X → STy X
truncate-sty d As = truncate-sty′ (sty-dim As ∸ d) As
