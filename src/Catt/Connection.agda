module Catt.Connection where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension

connect : (Γ : Ctx (suc n)) → (x : Tm (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-inc-right : (x : Tm (suc n)) → (m : ℕ) → Sub (suc m) (suc (m + n)) ⋆

connect Γ x (∅ , A) = Γ
connect Γ x (Δ , A , B) = (connect Γ x (Δ , A)) , B [ connect-inc-right x (ctxLength Δ) ]ty

connect-inc-right x zero = ⟨ ⟨⟩ , x ⟩
connect-inc-right x (suc m) = ⟨ liftSub (connect-inc-right x m) , 0V ⟩

connect-inc-left : (x : Tm (suc n)) → (m : ℕ) → Sub (suc n) (suc (m + n)) ⋆
connect-inc-left x zero = idSub
connect-inc-left x (suc m) = liftSub (connect-inc-left x m)

connect-susp : (Γ : Ctx (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + (2 + n)))
connect-susp Γ Δ = connect (suspCtx Γ) getSnd Δ

connect-susp-inc-right : (n m : ℕ) → Sub (suc m) (suc (m + (2 + n))) ⋆
connect-susp-inc-right n m = connect-inc-right getSnd m

connect-susp-inc-left : (n m : ℕ) → Sub (3 + n) (suc (m + (2 + n))) ⋆
connect-susp-inc-left n m = connect-inc-left getSnd m

sub-from-connect : Sub (suc n) l A → Sub (suc m) l A → Sub (suc (m + n)) l A
sub-from-connect σ ⟨ ⟨⟩ , t ⟩ = σ
sub-from-connect σ ⟨ ⟨ τ , u ⟩ , t ⟩ = ⟨ sub-from-connect σ ⟨ τ , u ⟩ , t ⟩

sub-between-connects : Sub (suc n) (suc l) ⋆ → Sub (suc m) (suc l′) ⋆ → (s : Tm (suc l)) → Sub (suc (m + n)) (suc (l′ + l)) ⋆
sub-between-connects {l′ = l′} σ τ s = sub-from-connect (connect-inc-left s l′ ∘ σ) (connect-inc-right s l′ ∘ τ)

sub-between-connect-susps : Sub (suc n) (suc l) ⋆ → Sub (suc m) (suc l′) ⋆ → Sub (suc (m + (2 + n))) (suc (l′ + (2 + l))) ⋆
sub-between-connect-susps σ τ = sub-between-connects (suspSub σ) τ getSnd
