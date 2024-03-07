open import Catt.Typing.Rule

module Catt.Typing.Rule.Properties (ops : Op) where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Typing ops

module _ {rs} {rs′} (subset : rs ⊆r rs′) where
  ≈tm-⊆ : _≈[_]tm_ rs s Γ t → _≈[_]tm_ rs′ s Γ t
  ≈ty-⊆ : _≈[_]ty_ rs A Γ B → _≈[_]ty_ rs′ A Γ B
  ≈s-⊆ : _≈[_]s_ rs σ Γ τ → _≈[_]s_ rs′ σ Γ τ
  Typing-Ctx-⊆ : Typing-Ctx rs Γ → Typing-Ctx rs′ Γ
  Typing-Tm-⊆ : Typing-Tm rs Γ s A → Typing-Tm rs′ Γ s A
  Typing-Ty-⊆ : Typing-Ty rs Γ A → Typing-Ty rs′ Γ A
  Typing-Sub-⊆ : Typing-Sub rs Γ Δ σ → Typing-Sub rs′ Γ Δ σ

  ≈tm-⊆ (Var≈ x) = Var≈ x
  ≈tm-⊆ (Sym≈ p) = Sym≈ (≈tm-⊆ p)
  ≈tm-⊆ (Trans≈ p q) = Trans≈ (≈tm-⊆ p) (≈tm-⊆ q)
  ≈tm-⊆ (Coh≈ x y) = Coh≈ (≈ty-⊆ x) (≈s-⊆ y)
  ≈tm-⊆ (Rule≈ r p tty) = Rule≈ r (subset p) (Typing-Tm-⊆ tty)

  ≈ty-⊆ Star≈ = Star≈
  ≈ty-⊆ (Arr≈ p q r) = Arr≈ (≈tm-⊆ p) (≈ty-⊆ q) (≈tm-⊆ r)

  ≈s-⊆ (Null≈ x) = Null≈ (≈ty-⊆ x)
  ≈s-⊆ (Ext≈ p x) = Ext≈ (≈s-⊆ p) (≈tm-⊆ x)

  Typing-Ctx-⊆ TyEmp = TyEmp
  Typing-Ctx-⊆ (TyAdd x y) = TyAdd (Typing-Ctx-⊆ x) (Typing-Ty-⊆ y)

  Typing-Tm-⊆ (TyConv x p) = TyConv (Typing-Tm-⊆ x) (≈ty-⊆ p)
  Typing-Tm-⊆ (TyVar i) = TyVar i
  Typing-Tm-⊆ (TyCoh x y z) = TyCoh x (Typing-Ty-⊆ y) (Typing-Sub-⊆ z)

  Typing-Ty-⊆ TyStar = TyStar
  Typing-Ty-⊆ (TyArr x y z) = TyArr (Typing-Tm-⊆ x) (Typing-Ty-⊆ y) (Typing-Tm-⊆ z)

  Typing-Sub-⊆ (TyNull x) = TyNull (Typing-Ty-⊆ x)
  Typing-Sub-⊆ (TyExt x y) = TyExt (Typing-Sub-⊆ x) (Typing-Tm-⊆ y)
