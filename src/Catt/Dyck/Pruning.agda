module Catt.Dyck.Pruning where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Globular
open import Catt.Discs
open import Catt.Dyck
open import Catt.Dyck.Properties

infixl 5 _//_
_//_ : (dy : Dyck (suc n) d) → Peak dy → Dyck n d
dy // ⇕pk d = d
⇑ dy // ⇑pk p = ⇑ (dy // p)
⇓ dy // ⇓pk p = ⇓ (dy // p)

π : {dy : Dyck (suc n) d} → Peak dy → Sub (3 + n * 2) (1 + n * 2) ⋆
π (⇕pk {d = d} dy) = ⟨ ⟨ idSub , dyck-term dy ⟩ , identity-term (dyck-type dy) (dyck-term dy) ⟩
π (⇑pk p) = ⟨ ⟨ (wk-sub (wk-sub (π p))) , 1V ⟩ , 0V ⟩
π (⇓pk p) = π p

private
  prune-sub : {dy : Dyck (suc n) d} → Peak dy → Sub (3 + n * 2) m ⋆ → Sub (1 + n * 2) m ⋆
  prune-sub (⇕pk dy) σ = sub-proj₁ (sub-proj₁ σ)
  prune-sub (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ = ⟨ ⟨ (prune-sub p σ) , s ⟩ , t ⟩
  prune-sub (⇓pk p) σ = prune-sub p σ

infixl 5 _//s_
_//s_ : {dy : Dyck (suc n) d} → Sub (3 + n * 2) m ⋆ → Peak dy → Sub (1 + n * 2) m ⋆
σ //s p = prune-sub p σ
