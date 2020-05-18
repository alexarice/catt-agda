{-# OPTIONS --safe --without-K #-}

module Catt.FreeVars.Properties where

open import Catt.FreeVars
open import Catt.Syntax
open import Catt.Syntax.Equality
open import Data.Nat
open import Catt.Fin
open import Data.Unit
open import Data.Product
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality
open import Function.Base
open import Relation.Binary

private
  variable
    n m : ℕ
    Γ Γ′ Δ Δ′ : Ctx n
    t t′ u u′ : Term n
    A A′ B B′ : Ty n
    σ σ′ : Sub m n

fv-refl : ∀ {n} → Reflexive {A = FVSet n} _≡fv_
fv-sym : ∀ {n} → Symmetric {A = FVSet n} _≡fv_
fv-trans : ∀ {n} → Transitive {A = FVSet n} _≡fv_

fv-refl i = id , id
fv-sym x≡y i = (proj₂ (x≡y i)) , (proj₁ (x≡y i))
fv-trans x≡y y≡z i = (proj₁ (y≡z i) ∘ proj₁ (x≡y i)) , proj₂ (x≡y i) ∘ proj₂ (y≡z i)

fv-isEquiv : ∀ {n} → IsEquivalence {A = FVSet n} _≡fv_
fv-isEquiv = record
  { refl = fv-refl
  ; sym = fv-sym
  ; trans = fv-trans
  }

fv-setoid : ℕ → Setoid _ _
fv-setoid n = record
  { Carrier = FVSet n
  ; _≈_ = _≡fv_
  ; isEquivalence = fv-isEquiv
  }

∪-cong : {a b c d : FVSet n} → a ≡fv c → b ≡fv d → a ∪ b ≡fv c ∪ d
∪-cong p q i = S.map (proj₁ (p i)) (proj₁ (q i)) , S.map (proj₂ (p i)) (proj₂ (q i))

ewf-cong : {f g : FVSet n} → f ≡fv g → ewf f ≡fv ewf g
ewf-cong p (fromℕ _) = id , id
ewf-cong p (inject i) = p i

ewt-cong : {f g : FVSet n} → f ≡fv g → ewt f ≡fv ewt g
ewt-cong p (fromℕ _) = id , id
ewt-cong p (inject i) = p i

drop-cong : {f g : FVSet (suc n)} → f ≡fv g → drop f ≡fv drop g
drop-cong p = ewf-cong (λ i → p (inject i))

transport-fv-ctx : Γ ≡ctx Γ′ → FVCtx Γ ≡fv FVCtx Γ′
transport-fv-ty : A ≡ty A′ → FVTy A ≡fv FVTy A′
transport-fv-tm : t ≡tm t′ → FVTerm t ≡fv FVTerm t′
transport-fv-sub : σ ≡sub σ′ → FVSub σ ≡fv FVSub σ′

transport-fv-ctx p = fv-refl

transport-fv-ty Star≡ = fv-refl
transport-fv-ty (Arr≡ a b c) = ∪-cong (∪-cong (transport-fv-ty b) (transport-fv-tm a)) (transport-fv-tm c)

transport-fv-tm (Var≡ refl) i = id , id
transport-fv-tm (Coh≡ p q r) = transport-fv-sub r

transport-fv-sub p i = (λ where (x₁ , x₂) → x₁ , (proj₁ (transport-fv-tm (p x₁) i) x₂)) , λ where (x₁ , x₂) → x₁ , (proj₂ (transport-fv-tm (p x₁) i) x₂)
