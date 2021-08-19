{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Discs.Properties where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Data.Nat
open import Catt.Globular.Properties

sub-from-disc-tm-≃ : {s : Tm Γ (suc (suc d))} → {t : Tm Δ (suc (suc d′))} → Γ ≃c Δ → s ≃tm t → sub-from-disc s ≃s sub-from-disc t
sub-from-sphere-ty-≃ : {A : Ty Γ (suc d)} {B : Ty Δ (suc d′)} → Γ ≃c Δ → A ≃ty B → sub-from-sphere A ≃s sub-from-sphere B

sub-from-disc-tm-≃ p q = Ext≃ (sub-from-sphere-ty-≃ p (tm-to-ty-≃ p q)) q

sub-from-sphere-ty-≃ p Star≃ = Null≃
sub-from-sphere-ty-≃ {d = suc d} {d′ = suc d′} p (Arr≃ q r s) = Ext≃ (sub-from-disc-tm-≃ p q) s

-- disc-to-subbed-tm : sub-from-disc (t [ σ ]tm) ≃s σ ∘ sub-from-disc t
-- disc-to-subbed-tm = Ext≃ {!!} refl≃tm
