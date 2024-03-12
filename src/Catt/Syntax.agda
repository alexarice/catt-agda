module Catt.Syntax where

open import Catt.Prelude
open import Catt.Syntax.Base public
open import Catt.Suspension

wk-tm : Tm n → Tm (suc n)
wk-ty : Ty n → Ty (suc n)
wk-sub : Sub n m A → Sub n (suc m) (wk-ty A)

wk-ty ⋆ = ⋆
wk-ty (s ─⟨ A ⟩⟶ t) = wk-tm s ─⟨ wk-ty A ⟩⟶ wk-tm t

wk-tm (Var i) = Var (suc i)
wk-tm (Coh S A σ) = Coh S A (wk-sub σ)

wk-sub ⟨ A ⟩′ = ⟨ wk-ty A ⟩′
wk-sub ⟨ σ , t ⟩ = ⟨ wk-sub σ , wk-tm t ⟩

ctx-proj₁ : Ctx (suc n) → Ctx n
ctx-proj₁ (Γ , A) = Γ

ctx-proj₂ : Ctx (suc n) → Ty n
ctx-proj₂ (Γ , A) = A

sub-type : Sub n m A → Ty m
sub-type {A = A} σ = A

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty n → Sub n m A → Ty m
_[_]tm : Tm n → Sub n m A → Tm m

infixr 31 _●_
_●_ : Sub m n A → (σ : Sub n l B) → Sub m l (A [ σ ]ty)

⋆ [ σ ]ty = sub-type σ
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var i [ σ ]tm = i [ σ ]v
_[_]tm {A = ⋆} (Coh T B τ) σ = Coh T B (τ ● σ)
_[_]tm {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) σ = Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ ↓ σ ]tm
⟨ A ⟩′ ● σ = ⟨ A [ σ ]ty ⟩′
⟨ τ , t ⟩ ● σ = ⟨ (τ ● σ) , t [ σ ]tm ⟩

idSub : {n : ℕ} → Sub n n ⋆
idSub {zero} = ⟨ ⋆ ⟩′
idSub {suc n} = ⟨ wk-sub idSub , Var zero ⟩

project : {n : ℕ} → Sub n (suc n) ⋆
project = wk-sub idSub

infix 45 _‼_
_‼_ : (Γ : Ctx n) → (i : Fin n) → Ty n
(Γ , A) ‼ zero = wk-ty A
(Γ , A) ‼ suc i = wk-ty (Γ ‼ i)

replaceSub : Sub (1 + n) m A → Tm m → Sub (1 + n) m A
replaceSub σ t = ⟨ sub-proj₁ σ , t ⟩
