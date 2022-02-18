module Catt.Discs.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Catt.Globular
open import Catt.Globular.Properties
open import Relation.Nullary
open import Catt.Tree

disc-≡ : .(d ≡ d′) → Disc d ≃c Disc d′
disc-≡ p with recompute (_ ≟ _) p
... | refl = refl≃c

disc-susp : (n : ℕ) → suspCtx (Disc n) ≃c Disc (suc n)
sphere-susp : (n : ℕ) → suspCtx (Sphere n) ≃c Sphere (suc n)
sphere-type-susp : (n : ℕ) → suspTy (sphere-type n) ≃ty sphere-type (suc n)

disc-susp zero = refl≃c
disc-susp (suc n) = Add≃ (sphere-susp (suc n)) (sphere-type-susp (suc n))

sphere-susp zero = refl≃c
sphere-susp (suc n) = Add≃ (disc-susp n) (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n)))

sphere-type-susp zero = refl≃ty
sphere-type-susp (suc n) = Arr≃ (refl≃tm) (trans≃ty (susp-ty-lift (liftType (sphere-type n))) (lift-ty-≃ (trans≃ty (susp-ty-lift (sphere-type n)) (lift-ty-≃ (sphere-type-susp n))))) (refl≃tm)

linear-tree-compat : (T : Tree n) → .⦃ _ : is-linear T ⦄ → tree-to-ctx T ≃c Disc (tree-dim T)
linear-tree-compat Sing = Add≃ Emp≃ (Star≃ refl)
linear-tree-compat (Join S Sing) = trans≃c (susp-ctx-≃ (linear-tree-compat S)) (disc-susp (tree-dim S))

sub-from-sphere-prop : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → sphere-type d [ sub-from-sphere d A p ]ty ≃ty A
sub-from-sphere-prop zero ⋆ p = refl≃ty
sub-from-sphere-prop (suc d) (s ─⟨ A ⟩⟶ t) p = Arr≃ refl≃tm (trans≃ty (lift-sub-comp-lem-ty ⟨ sub-from-sphere d A (cong pred p) , s ⟩ (liftType (sphere-type _))) (trans≃ty (lift-sub-comp-lem-ty (sub-from-sphere d A (cong pred p)) (sphere-type _)) (sub-from-sphere-prop d A (cong pred p)))) refl≃tm

sub-from-disc-≃ : (d₁ d₂ : ℕ) → A ≃ty B → .(p : ty-dim A ≡ d₁) → .(q : ty-dim B ≡ d₂) → s ≃tm t → sub-from-disc d₁ A p s ≃s sub-from-disc d₂ B q t
sub-from-sphere-≃ : (d₁ d₂ : ℕ) → A ≃ty B → .(p : ty-dim A ≡ d₁) → .(q : ty-dim B ≡ d₂) → sub-from-sphere d₁ A p ≃s sub-from-sphere d₂ B q

sub-from-disc-≃ d₁ d₂ a b c d = Ext≃ (sub-from-sphere-≃ d₁ d₂ a b c) d

sub-from-sphere-≃ zero zero (Star≃ x) p q = Null≃ (Star≃ x)
sub-from-sphere-≃ (suc d₁) (suc d₂) (Arr≃ a b c) p q = Ext≃ (Ext≃ (sub-from-sphere-≃ d₁ d₂ b (cong pred p) (cong pred q)) a) c

sub-from-sphere-sub : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (σ : Sub n m ⋆) → sub-from-sphere d (A [ σ ]ty) (trans (sym (sub-dim σ A)) p) ≃s σ ∘ sub-from-sphere d A p
sub-from-sphere-sub zero ⋆ p σ = refl≃s
sub-from-sphere-sub (suc d) (s ─⟨ A ⟩⟶ t) p σ = Ext≃ (Ext≃ (sub-from-sphere-sub d A (cong pred p) σ) refl≃tm) refl≃tm

sub-from-disc-sub : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (s : Tm n) → (σ : Sub n m ⋆) → sub-from-disc d (A [ σ ]ty) (trans (sym (sub-dim σ A)) p) (s [ σ ]tm) ≃s σ ∘ sub-from-disc d A p s
sub-from-disc-sub d A p s σ = Ext≃ (sub-from-sphere-sub d A p σ) refl≃tm

identity-lem : n ≡ m → σ ≃s τ → Coh (Disc n) (0V ─⟨ liftType (sphere-type n) ⟩⟶ 0V) σ ≃tm Coh (Disc m) (0V ─⟨ liftType (sphere-type m) ⟩⟶ 0V) τ
identity-lem refl p = Coh≃ refl≃c refl≃ty p

identity-≃ : s ≃tm t → A ≃ty B → identity s A ≃tm identity t B
identity-≃ p q = identity-lem (ty-dim-≃ q) (sub-from-disc-≃ (ty-dim _) (ty-dim _) q refl refl p)

identity-sub : (t : Tm n) → (A : Ty n) → (σ : Sub n m ⋆) → identity t A [ σ ]tm ≃tm identity (t [ σ ]tm) (A [ σ ]ty)
identity-sub t A σ = identity-lem (sub-dim σ A) (trans≃s (sym≃s (sub-from-disc-sub (ty-dim A) A refl t σ)) (sub-from-disc-≃ (ty-dim A) (ty-dim (A [ σ ]ty)) refl≃ty (trans (sym (sub-dim σ A)) refl) refl refl≃tm))
