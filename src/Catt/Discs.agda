{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Discs where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Pasting.Tree
open import Catt.Globular
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Connection.Properties
open import Data.Empty
open import Data.Unit

disc-size : ℕ → ℕ
sphere-size : ℕ → ℕ

disc-size n = suc (sphere-size n)

sphere-size zero = 0
sphere-size (suc n) = suc (disc-size n)

Disc : (n : ℕ) → Ctx (disc-size n)
Sphere : (n : ℕ) → Ctx (sphere-size n)
sphere-type : (n : ℕ) → Ty (sphere-size n) n

Disc n = Sphere n , sphere-type n

Sphere zero = ∅
Sphere (suc n) = Disc n , liftType (sphere-type n)

sphere-type zero = ⋆
sphere-type (suc n) = 1V ─⟨ liftType (liftType (sphere-type n)) ⟩⟶ 0V

sub-from-disc : (Γ : Ctx n) → (t : Tm n) → Sub (disc-size (get-tm-height Γ t)) n
sub-from-sphere : Ty n d → Sub (sphere-size d) n

sub-from-disc Γ t = ⟨ (sub-from-sphere (tm-to-ty Γ t)) , t ⟩

sub-from-sphere ⋆ = ⟨⟩
sub-from-sphere (s ─⟨ A ⟩⟶ t) = ⟨ ⟨ sub-from-sphere A , s ⟩ , t ⟩

disc-≡ : d ≡ d′ → Disc d ≃c Disc d′
disc-≡ refl = refl≃c

disc-susp : (n : ℕ) → suspCtx (Disc n) ≃c Disc (suc n)
sphere-susp : (n : ℕ) → suspCtx (Sphere n) ≃c Sphere (suc n)
sphere-type-susp : (n : ℕ) → suspTy (sphere-type n) ≃ty sphere-type (suc n)

disc-susp zero = refl≃c
disc-susp (suc n) = Add≃ (sphere-susp (suc n)) (sphere-type-susp (suc n))

sphere-susp zero = refl≃c
sphere-susp (suc n) = Add≃ (disc-susp n) (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n)))

sphere-type-susp zero = refl≃ty
sphere-type-susp (suc n) = Arr≃ (refl≃tm) (trans≃ty (susp-ty-lift (liftType (sphere-type n))) (lift-ty-≃ (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n))))) (refl≃tm)

is-linear : Tree n → Set
is-linear Sing = ⊤
is-linear (Join S Sing) = is-linear S
is-linear (Join S (Join _ _)) = ⊥

-- Use tree-dim
height-of-linear : (T : Tree n) → .⦃ is-linear T ⦄ → ℕ
height-of-linear Sing = 0
height-of-linear (Join S Sing) = suc (height-of-linear S)

linear-tree-compat : (T : Tree n) → .⦃ _ : is-linear T ⦄ → tree-to-ctx T ≃c Disc (height-of-linear T)
linear-tree-compat Sing = Add≃ Emp≃ (Star≃ refl)
linear-tree-compat (Join S Sing) = trans≃c (susp-ctx-≃ (linear-tree-compat S)) (disc-susp (height-of-linear S))

height-of-linear-is-tree-dim : (T : Tree n) → .⦃ _ : is-linear T ⦄ → height-of-linear T ≡ tree-dim T
height-of-linear-is-tree-dim Sing = refl
height-of-linear-is-tree-dim (Join T Sing) = cong suc (height-of-linear-is-tree-dim T)
