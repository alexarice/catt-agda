module Catt.Tree.Path.Support where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Tree
open import Catt.Tree.Path

open import Catt.Support
open import Catt.Support.Properties
open import Catt.Suspension.Support
open import Catt.Wedge.Support

open ≡-Reasoning

SuppPath : (P : Path S) → VarSet (suc (tree-size S))
SuppPath PHere = trueAt (fromℕ _)
SuppPath (PExt P) = wedge-susp-vs (susp-vs (SuppPath P)) empty
SuppPath (PShift P) = wedge-susp-vs empty (SuppPath P)

SuppPath-to-term : (P : Path S) → SuppPath P ≡ DC ⌊ S ⌋ (FVTm (path-to-term P))
SuppPath-to-term PHere = sym (DC-fromℕ _)
SuppPath-to-term (PExt {S = S} {T = T} P) = begin
  wedge-susp-vs (susp-vs (SuppPath P)) empty
    ≡⟨ cong (λ - → wedge-susp-vs (susp-vs -) empty) (SuppPath-to-term P) ⟩
  wedge-susp-vs (susp-vs (SuppTm ⌊ S ⌋ (path-to-term P))) empty
    ≡⟨ wedge-susp-vs-ext ⌊ S ⌋ (path-to-term P) ⌊ T ⌋ ⟩
  SuppTm (wedge-susp ⌊ S ⌋ ⌊ T ⌋) (susp-tm (path-to-term P) [ wedge-susp-inc-left _ _ ]tm) ∎
SuppPath-to-term (PShift {T = T} {S = S} P) = begin
  wedge-susp-vs empty (SuppPath P)
    ≡⟨ cong (wedge-susp-vs empty) (SuppPath-to-term P) ⟩
  wedge-susp-vs empty (SuppTm ⌊ T ⌋ (path-to-term P))
    ≡⟨ wedge-susp-vs-shift ⌊ S ⌋ ⌊ T ⌋ (path-to-term P) ⟩
  SuppTm ⌊ Join S T ⌋ (path-to-term P [ wedge-susp-inc-right _ _ ]tm) ∎
