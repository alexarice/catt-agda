module Catt.Wedge where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension

wedge : (Γ : Ctx (suc n)) → (x : Tm (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
wedge-inc-right : (x : Tm (suc n)) → (m : ℕ) → Sub (suc m) (suc (m + n)) ⋆

wedge {m = zero} Γ x (Δ , A) = Γ
wedge {m = suc m} Γ x (Δ , A) = (wedge Γ x Δ) , A [ wedge-inc-right x m ]ty

wedge-inc-right x zero = ⟨ ⟨⟩ , x ⟩
wedge-inc-right x (suc m) = ⟨ lift-sub (wedge-inc-right x m) , 0V ⟩

wedge-inc-left : (x : Tm (suc n)) → (m : ℕ) → Sub (suc n) (suc (m + n)) ⋆
wedge-inc-left x zero = idSub
wedge-inc-left x (suc m) = lift-sub (wedge-inc-left x m)

wedge-susp : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + (2 + n)))
wedge-susp Γ Δ = wedge (susp-ctx Γ) get-snd Δ

wedge-susp-inc-right : (n m : ℕ) → Sub (suc m) (suc (m + (2 + n))) ⋆
wedge-susp-inc-right n m = wedge-inc-right get-snd m

wedge-susp-inc-left : (n m : ℕ) → Sub (3 + n) (suc (m + (2 + n))) ⋆
wedge-susp-inc-left n m = wedge-inc-left get-snd m

sub-from-wedge : Sub (suc n) l A → Sub (suc m) l A → Sub (suc (m + n)) l A
sub-from-wedge σ ⟨ ⟨⟩ , t ⟩ = σ
sub-from-wedge σ ⟨ ⟨ τ , u ⟩ , t ⟩ = ⟨ sub-from-wedge σ ⟨ τ , u ⟩ , t ⟩

sub-between-wedges : Sub (suc n) (suc l) ⋆ → Sub (suc m) (suc l′) ⋆ → (s : Tm (suc l)) → Sub (suc (m + n)) (suc (l′ + l)) ⋆
sub-between-wedges {l′ = l′} σ τ s = sub-from-wedge (σ ● wedge-inc-left s l′) (τ ● wedge-inc-right s l′)

sub-between-wedge-susps : Sub (suc n) (suc l) ⋆ → Sub (suc m) (suc l′) ⋆ → Sub (suc (m + (2 + n))) (suc (l′ + (2 + l))) ⋆
sub-between-wedge-susps σ τ = sub-between-wedges (susp-sub σ) τ get-snd
