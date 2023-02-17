module Catt.Connection where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension

connect : (Γ : Ctx (suc n)) → (x : Tm (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-inc-right : (x : Tm (suc n)) → (m : ℕ) → Sub (suc m) (suc (m + n)) ⋆

connect {m = zero} Γ x (Δ , A) = Γ
connect {m = suc m} Γ x (Δ , A) = (connect Γ x Δ) , A [ connect-inc-right x m ]ty

connect-inc-right x zero = ⟨ ⟨⟩ , x ⟩
connect-inc-right x (suc m) = ⟨ lift-sub (connect-inc-right x m) , 0V ⟩

connect-inc-left : (x : Tm (suc n)) → (m : ℕ) → Sub (suc n) (suc (m + n)) ⋆
connect-inc-left x zero = idSub
connect-inc-left x (suc m) = lift-sub (connect-inc-left x m)

connect-susp : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + (2 + n)))
connect-susp Γ Δ = connect (susp-ctx Γ) get-snd Δ

connect-susp-inc-right : (n m : ℕ) → Sub (suc m) (suc (m + (2 + n))) ⋆
connect-susp-inc-right n m = connect-inc-right get-snd m

connect-susp-inc-left : (n m : ℕ) → Sub (3 + n) (suc (m + (2 + n))) ⋆
connect-susp-inc-left n m = connect-inc-left get-snd m

sub-from-connect : Sub (suc n) l A → Sub (suc m) l A → Sub (suc (m + n)) l A
sub-from-connect σ ⟨ ⟨⟩ , t ⟩ = σ
sub-from-connect σ ⟨ ⟨ τ , u ⟩ , t ⟩ = ⟨ sub-from-connect σ ⟨ τ , u ⟩ , t ⟩

sub-between-connects : Sub (suc n) (suc l) ⋆ → Sub (suc m) (suc l′) ⋆ → (s : Tm (suc l)) → Sub (suc (m + n)) (suc (l′ + l)) ⋆
sub-between-connects {l′ = l′} σ τ s = sub-from-connect (connect-inc-left s l′ ● σ) (connect-inc-right s l′ ● τ)

sub-between-connect-susps : Sub (suc n) (suc l) ⋆ → Sub (suc m) (suc l′) ⋆ → Sub (suc (m + (2 + n))) (suc (l′ + (2 + l))) ⋆
sub-between-connect-susps σ τ = sub-between-connects (susp-sub σ) τ get-snd
