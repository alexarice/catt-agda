{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Discs where

open import Catt.Syntax
open import Catt.Syntax.Patterns
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
sphere-type : (n : ℕ) → Ty (Sphere n) (suc n)

Disc n = Sphere n , sphere-type n

Sphere zero = ∅
Sphere (suc n) = Disc n , liftType (sphere-type n)

sphere-type zero = ⋆
sphere-type (suc n) = 1V ─⟨ liftType (liftType (sphere-type n)) ⟩⟶ 0V

sub-from-disc : Tm Γ (suc (suc d)) → Sub (Disc d) Γ
sub-from-sphere : Ty Γ (suc d) → Sub (Sphere d) Γ

sub-from-disc t = ⟨ (sub-from-sphere (tm-to-ty t)) , t ⟩

sub-from-sphere ⋆ = ⟨⟩
sub-from-sphere {d = suc d} (s ─⟨ A ⟩⟶ t) = ⟨ sub-from-disc s , t ⟩

disc-susp : (n : ℕ) → suspCtx (Disc n) ≃c Disc (suc n)
sphere-susp : (n : ℕ) → suspCtx (Sphere n) ≃c Sphere (suc n)
sphere-type-susp : (n : ℕ) → suspTy (sphere-type n) ≃ty sphere-type (suc n)

disc-susp zero = refl≃c
disc-susp (suc n) = Add≃ (sphere-susp (suc n)) (sphere-type-susp (suc n))

sphere-susp zero = refl≃c
sphere-susp (suc n) = Add≃ (disc-susp n) (trans≃ty (reflexive≃ty (suspLiftTy (sphere-type n))) (lift-ty-≃ (sphere-type-susp n)))

sphere-type-susp zero = refl≃ty
sphere-type-susp (suc n) = Arr≃ (Var≃ refl) (trans≃ty (reflexive≃ty (trans (suspLiftTy (liftType (sphere-type n))) (cong liftType (suspLiftTy (sphere-type n))))) (lift-ty-≃ (lift-ty-≃ (sphere-type-susp n)))) (Var≃ refl)

is-linear : Tree n → Set
is-linear Sing = ⊤
is-linear (Join S Sing) = is-linear S
is-linear (Join S (Join _ _)) = ⊥

-- Use tree-dim
height-of-linear : (T : Tree n) → .(is-linear T) → ℕ
height-of-linear Sing il = 0
height-of-linear (Join S Sing) il = suc (height-of-linear S il)

linear-tree-compat : (T : Tree n) → .(l : is-linear T) → tree-to-ctx T ≃c Disc (height-of-linear T l)
linear-tree-compat Sing l = Add≃ Emp≃ Star≃
linear-tree-compat (Join S Sing) l = trans≃c (susp-ctx-≃ (linear-tree-compat S l)) (disc-susp (height-of-linear S _))

height-of-linear-is-tree-dim : (T : Tree n) → .(lh : is-linear T) → height-of-linear T lh ≡ tree-dim T
height-of-linear-is-tree-dim Sing lh = refl
height-of-linear-is-tree-dim (Join T Sing) lh = cong suc (height-of-linear-is-tree-dim T lh)
