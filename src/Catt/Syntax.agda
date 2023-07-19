module Catt.Syntax where

open import Catt.Prelude
open import Catt.Syntax.Base public
open import Catt.Suspension

lift-tm : Tm n → Tm (suc n)
lift-ty : Ty n → Ty (suc n)
lift-sub : Sub n m A → Sub n (suc m) (lift-ty A)

lift-ty ⋆ = ⋆
lift-ty (s ─⟨ A ⟩⟶ t) = lift-tm s ─⟨ lift-ty A ⟩⟶ lift-tm t

lift-tm (Var i) = Var (suc i)
lift-tm (Coh S A σ) = Coh S A (lift-sub σ)

lift-sub ⟨⟩ = ⟨⟩
lift-sub ⟨ σ , t ⟩ = ⟨ lift-sub σ , lift-tm t ⟩

ctx-proj₁ : Ctx (suc n) → Ctx n
ctx-proj₁ (Γ , A) = Γ

ctx-proj₂ : Ctx (suc n) → Ty n
ctx-proj₂ (Γ , A) = A

sub-type : Sub n m A → Ty m
sub-type {A = A} σ = A

sub-proj₁ : Sub (suc n) m A → Sub n m A
sub-proj₁ ⟨ σ , t ⟩ = σ

sub-proj₂ : Sub (suc n) m A → Tm m
sub-proj₂ ⟨ σ , t ⟩ = t

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty n → Sub n m A → Ty m
_[_]tm : Tm n → Sub n m A → Tm m

infixl 31 _●_
_●_ : (σ : Sub n l A) → Sub m n B → Sub m l (B [ σ ]ty)

⋆ [ σ ]ty = sub-type σ
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ σ ]tm = sub-proj₂ σ
Var (suc x) [ σ ]tm = Var x [ sub-proj₁ σ ]tm
_[_]tm {A = ⋆} (Coh T B τ) σ = Coh T B (σ ● τ)
_[_]tm {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) σ = Coh (susp-ctx Δ) (susp-ty B) (susp-sub τ) [ (unrestrict σ) ]tm
σ ● ⟨⟩ = ⟨⟩
σ ● ⟨ τ , t ⟩ = ⟨ (σ ● τ) , t [ σ ]tm ⟩

idSub : {n : ℕ} → Sub n n ⋆
idSub {zero} = ⟨⟩
idSub {suc n} = ⟨ lift-sub idSub , Var zero ⟩

infix 45 _‼_
_‼_ : (Γ : Ctx n) → (i : Fin n) → Ty n
(Γ , A) ‼ zero = lift-ty A
(Γ , A) ‼ suc i = lift-ty (Γ ‼ i)

replaceSub : Sub (1 + n) m A → Tm m → Sub (1 + n) m A
replaceSub σ t = ⟨ sub-proj₁ σ , t ⟩
