{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Discs where

open import Catt.Syntax
open import Catt.Dimension
-- open import Catt.Syntax.Patterns
-- open import Catt.Syntax.Properties
-- open import Catt.Syntax.SyntacticEquality
-- open import Catt.Pasting
-- open import Catt.Pasting.Properties
-- open import Catt.Pasting.Tree
open import Catt.Globular
open import Data.Nat
-- open import Relation.Binary.PropositionalEquality
open import Catt.Suspension
-- open import Catt.Connection.Properties
open import Data.Empty
open import Data.Unit

disc-size : ℕ → ℕ
sphere-size : ℕ → ℕ

disc-size n = suc (sphere-size n)

sphere-size zero = 0
sphere-size (suc n) = suc (disc-size n)

Disc : (n : ℕ) → Ctx (disc-size n)
Sphere : (n : ℕ) → Ctx (sphere-size n)
sphere-type : (n : ℕ) → Ty (sphere-size n)

Disc n = Sphere n , sphere-type n

Sphere zero = ∅
Sphere (suc n) = Disc n , liftType (sphere-type n)

sphere-type zero = ⋆
sphere-type (suc n) = 1V ─⟨ liftType (liftType (sphere-type n)) ⟩⟶ 0V

sub-from-disc : (t : Tm n) → .(tm-dim Γ t (suc (suc d))) → Sub (disc-size d) n
sub-from-sphere : (A : Ty n) → .(ty-dim Γ A (suc d)) → Sub (sphere-size d) n

sub-from-disc {Γ = Γ} t x = ⟨ (sub-from-sphere (tm-to-ty Γ t)) {!!} , t ⟩

sub-from-sphere {d = zero} ⋆ x = ⟨⟩
sub-from-sphere {d = suc d} (s ─⟨ A ⟩⟶ t) x = ⟨ (sub-from-disc s (get x)) , {!t!} ⟩
  where
    get : ty-dim Γ (s ─⟨ A ⟩⟶ t) d′ → tm-dim Γ s d′
    get (ArrD x _ _) = x


-- disc-susp : (n : ℕ) → suspCtx (Disc n) ≃c Disc (suc n)
-- sphere-susp : (n : ℕ) → suspCtx (Sphere n) ≃c Sphere (suc n)
-- sphere-type-susp : (n : ℕ) → suspTy (sphere-type n) ≃ty sphere-type (suc n)

-- disc-susp zero = refl≃c
-- disc-susp (suc n) = Add≃ (sphere-susp (suc n)) (sphere-type-susp (suc n))

-- sphere-susp zero = refl≃c
-- sphere-susp (suc n) = Add≃ (disc-susp n) (trans≃ty (reflexive≃ty (suspLiftTy (sphere-type n))) (lift-ty-≃ (sphere-type-susp n)))

-- sphere-type-susp zero = refl≃ty
-- sphere-type-susp (suc n) = Arr≃ (Var≃ refl) (trans≃ty (reflexive≃ty (trans (suspLiftTy (liftType (sphere-type n))) (cong liftType (suspLiftTy (sphere-type n))))) (lift-ty-≃ (lift-ty-≃ (sphere-type-susp n)))) (Var≃ refl)

is-linear : Tree n → Set
is-linear Sing = ⊤
is-linear (Join S Sing) = is-linear S
is-linear (Join S (Join _ _)) = ⊥

height-of-linear : (T : Tree n) → .(is-linear T) → ℕ
height-of-linear Sing il = 0
height-of-linear (Join S Sing) il = suc (height-of-linear S il)

-- linear-tree-compat : (T : Tree n) → .(l : is-linear T) → tree-to-ctx T ≃c Disc (height-of-linear T l)
-- linear-tree-compat Sing l = Add≃ Emp≃ Star≃
-- linear-tree-compat (Join S Sing) l = trans≃c (susp-ctx-≃ (linear-tree-compat S l)) (disc-susp (height-of-linear S _))
