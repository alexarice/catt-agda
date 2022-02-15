module Catt.Syntax where

open import Catt.Prelude
open import Catt.Syntax.Base public
open import Catt.Suspension
open import Relation.Nullary
open import Data.Empty
open import Relation.Binary.Definitions

liftTerm : Tm n → Tm (suc n)
liftType : Ty n → Ty (suc n)
liftSub : Sub n m A → Sub n (suc m) (liftType A)

liftType ⋆ = ⋆
liftType (s ─⟨ A ⟩⟶ t) = liftTerm s ─⟨ liftType A ⟩⟶ liftTerm t

liftTerm (Var i) = Var (suc i)
liftTerm (Coh S A σ) = Coh S A (liftSub σ)

liftSub ⟨⟩ = ⟨⟩
liftSub ⟨ σ , t ⟩ = ⟨ liftSub σ , liftTerm t ⟩

sub-type : Sub n m A → Ty m
sub-type {A = A} σ = A

infixr 30 _[_]ty _[_]tm
_[_]ty : Ty n → Sub n m A → Ty m
_[_]tm : Tm n → Sub n m A → Tm m

infixl 31 _∘_
_∘_ : (σ : Sub n l A) → Sub m n B → Sub m l (B [ σ ]ty)

⋆ [ σ ]ty = sub-type σ
(s ─⟨ A ⟩⟶ t) [ σ ]ty = (s [ σ ]tm) ─⟨ (A [ σ ]ty) ⟩⟶ (t [ σ ]tm)

Var zero [ ⟨ σ , t ⟩ ]tm = t
Var (suc x) [ ⟨ σ , t ⟩ ]tm = Var x [ σ ]tm
_[_]tm {A = ⋆} (Coh T B τ) σ = Coh T B (σ ∘ τ)
_[_]tm {A = s ─⟨ A ⟩⟶ t} (Coh Δ B τ) σ = _[_]tm {A = A} (Coh (suspCtx Δ) (suspTy B) (suspSub τ)) (unrestrict σ)
σ ∘ ⟨⟩ = ⟨⟩
σ ∘ ⟨ τ , t ⟩ = ⟨ (σ ∘ τ) , t [ σ ]tm ⟩

idSub : {n : ℕ} → Sub n n ⋆
idSub {zero} = ⟨⟩
idSub {suc n} = ⟨ liftSub idSub , Var zero ⟩

infix 45 _‼_
_‼_ : (Γ : Ctx n) → (i : Fin n) → Ty n
(Γ , A) ‼ zero = liftType A
(Γ , A) ‼ suc i = liftType (Γ ‼ i)

ctx-proj₁ : Ctx (suc n) → Ctx n
ctx-proj₁ (Γ , A) = Γ

ctx-proj₂ : Ctx (suc n) → Ty n
ctx-proj₂ (Γ , A) = A

replaceSub : Sub (1 + n) m A → Tm m → Sub (1 + n) m A
replaceSub ⟨ σ , _ ⟩ t = ⟨ σ , t ⟩
