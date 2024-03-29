module Catt.Discs.Properties where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Discs

disc-≡ : .(d ≡ d′) → Disc d ≃c Disc d′
disc-≡ p with recompute (_ ≟ _) p
... | refl = refl≃c

sphere-≡ : .(d ≡ d′) → sphere-type d ≃ty sphere-type d′
sphere-≡ p with recompute (_ ≟ _) p
... | refl = refl≃ty

sphere-type-dim : (n : ℕ) → ty-dim (sphere-type n) ≡ n
sphere-type-dim zero = refl
sphere-type-dim (suc n) = cong suc (begin
  ty-dim (wk-ty (wk-ty (sphere-type n)))
    ≡⟨ wk-ty-dim (wk-ty (sphere-type n)) ⟩
  ty-dim (wk-ty (sphere-type n))
    ≡⟨ wk-ty-dim (sphere-type n) ⟩
  ty-dim (sphere-type n)
    ≡⟨ sphere-type-dim n ⟩
  n ∎)
  where
    open ≡-Reasoning

sphere-dim : (n : ℕ) → ctx-dim (Sphere n) ≡ pred n
disc-dim : (n : ℕ) → ctx-dim (Disc n) ≡ n

sphere-dim zero = refl
sphere-dim (suc n) = begin
  ctx-dim (Disc n) ⊔ ty-dim (wk-ty (sphere-type n))
    ≡⟨ cong₂ _⊔_ (disc-dim n) (trans (wk-ty-dim (sphere-type n)) (sphere-type-dim n)) ⟩
  n ⊔ n
    ≡⟨ ⊔-idem n ⟩
  n ∎
  where
    open ≡-Reasoning

disc-dim n = begin
  ctx-dim (Sphere n) ⊔ ty-dim (sphere-type n)
    ≡⟨ cong₂ _⊔_ (sphere-dim n) (sphere-type-dim n) ⟩
  pred n ⊔ n
    ≡⟨ m≤n⇒m⊔n≡n pred[n]≤n ⟩
  n ∎
  where
    open ≡-Reasoning

disc-susp : (n : ℕ) → susp-ctx (Disc n) ≃c Disc (suc n)
sphere-susp : (n : ℕ) → susp-ctx (Sphere n) ≃c Sphere (suc n)
sphere-type-susp : (n : ℕ) → susp-ty (sphere-type n) ≃ty sphere-type (suc n)

disc-susp zero = refl≃c
disc-susp (suc n) = Add≃ (sphere-susp (suc n)) (sphere-type-susp (suc n))

sphere-susp zero = refl≃c
sphere-susp (suc n) = Add≃ (disc-susp n) (trans≃ty (susp-ty-wk (sphere-type n)) (wk-ty-≃ (sphere-type-susp n)))

sphere-type-susp zero = refl≃ty
sphere-type-susp (suc n) = Arr≃ (refl≃tm) (trans≃ty (susp-ty-wk (wk-ty (sphere-type n))) (wk-ty-≃ (trans≃ty (susp-ty-wk (sphere-type n)) (wk-ty-≃ (sphere-type-susp n))))) (refl≃tm)

disc-term-susp : (n : ℕ) → (σ : Sub (disc-size n) m ⋆) → susp-tm (disc-term n σ) ≃tm disc-term (suc n) (susp-sub σ)
disc-term-susp n σ = Coh≃ (disc-susp n) (trans≃ty (susp-ty-wk (sphere-type n)) (wk-ty-≃ (sphere-type-susp n))) refl≃s

sub-from-disc-≃ : (d₁ d₂ : ℕ) → A ≃ty B → .(p : ty-dim A ≡ d₁) → .(q : ty-dim B ≡ d₂) → s ≃tm t → sub-from-disc d₁ A p s ≃s sub-from-disc d₂ B q t
sub-from-sphere-≃ : (d₁ d₂ : ℕ) → A ≃ty B → .(p : ty-dim A ≡ d₁) → .(q : ty-dim B ≡ d₂) → sub-from-sphere d₁ A p ≃s sub-from-sphere d₂ B q

sub-from-disc-≃ d₁ d₂ a b c d = Ext≃ (sub-from-sphere-≃ d₁ d₂ a b c) d

sub-from-sphere-≃ zero zero (Star≃ x) p q = Null≃ (Star≃ x)
sub-from-sphere-≃ (suc d₁) (suc d₂) (Arr≃ a b c) p q = Ext≃ (Ext≃ (sub-from-sphere-≃ d₁ d₂ b (cong pred p) (cong pred q)) a) c

sub-from-sphere-sub : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (σ : Sub n m ⋆) → sub-from-sphere d (A [ σ ]ty) (trans (sym (sub-dim σ A)) p) ≃s (sub-from-sphere d A p ● σ)
sub-from-sphere-sub zero ⋆ p σ = refl≃s
sub-from-sphere-sub (suc d) (s ─⟨ A ⟩⟶ t) p σ = Ext≃ (Ext≃ (sub-from-sphere-sub d A (cong pred p) σ) refl≃tm) refl≃tm

sub-from-disc-sub : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (s : Tm n) → (σ : Sub n m ⋆) → sub-from-disc d (A [ σ ]ty) (trans (sym (sub-dim σ A)) p) (s [ σ ]tm) ≃s sub-from-disc d A p s ● σ
sub-from-disc-sub d A p s σ = Ext≃ (sub-from-sphere-sub d A p σ) refl≃tm

sub-from-sphere-prop : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → sphere-type d [ sub-from-sphere d A p ]ty ≃ty A
sub-from-sphere-prop zero ⋆ p = refl≃ty
sub-from-sphere-prop (suc d) (s ─⟨ A ⟩⟶ t) p = Arr≃ refl≃tm lem refl≃tm
  where
    open Reasoning ty-setoid

    lem : wk-ty (wk-ty (sphere-type d)) [ ⟨ ⟨ sub-from-sphere d A _ , s ⟩ , t ⟩ ]ty ≃ty A
    lem = begin
      < wk-ty (wk-ty (sphere-type d)) [ ⟨ ⟨ sub-from-sphere d A _ , s ⟩ , t ⟩ ]ty >ty
        ≈⟨ apply-sub-wk-ty-≃ (wk-ty (sphere-type d)) ⟨ ⟨ sub-from-sphere d A _ , s ⟩ , t ⟩ ⟩
      < wk-ty (sphere-type d) [ ⟨ sub-from-sphere d A _ , s ⟩ ]ty >ty
        ≈⟨ apply-sub-wk-ty-≃ (sphere-type d) ⟨ sub-from-sphere d A _ , s ⟩ ⟩
      < sphere-type d [ sub-from-sphere d A _ ]ty >ty
        ≈⟨ sub-from-sphere-prop d A _ ⟩
      < A >ty ∎

identity-≃ : n ≡ m → σ ≃s τ → identity n σ ≃tm identity m τ
identity-≃ refl p = Coh≃ refl≃c refl≃ty p

identity-term-≃ : A ≃ty B → s ≃tm t → identity-term A s ≃tm identity-term B t
identity-term-≃ p q = identity-≃ (ty-dim-≃ p) (sub-from-disc-≃ (ty-dim _) (ty-dim _) p refl refl q)

wk-sub-from-sphere : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → wk-sub (sub-from-sphere d A p) ≃s sub-from-sphere d (wk-ty A) (trans (wk-ty-dim A) p)
wk-sub-from-sphere zero ⋆ p = refl≃s
wk-sub-from-sphere (suc d) (s ─⟨ A ⟩⟶ t) p = Ext≃ (Ext≃ (wk-sub-from-sphere d A (cong pred p)) refl≃tm) refl≃tm

wk-sub-from-disc : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (t : Tm n) → wk-sub (sub-from-disc d A p t) ≃s sub-from-disc d (wk-ty A) (trans (wk-ty-dim A) p) (wk-tm t)
wk-sub-from-disc d A p t = Ext≃ (wk-sub-from-sphere d A p) refl≃tm

susp-sub-from-sphere : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → susp-sub (sub-from-sphere d A p) ≃s sub-from-sphere (suc d) (susp-ty A) (trans (susp-dim A) (cong suc p))
susp-sub-from-sphere zero ⋆ p = refl≃s
susp-sub-from-sphere (suc d) (s ─⟨ A ⟩⟶ t) p = Ext≃ (Ext≃ (susp-sub-from-sphere d A (cong pred p)) refl≃tm) refl≃tm

susp-sub-from-disc : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (t : Tm n) → susp-sub (sub-from-disc d A p t) ≃s sub-from-disc (suc d) (susp-ty A) (trans (susp-dim A) (cong suc p)) (susp-tm t)
susp-sub-from-disc d A p t = Ext≃ (susp-sub-from-sphere d A p) refl≃tm

prop-sub-from-sphere : (n : ℕ) → (σ : Sub (sphere-size n) m ⋆)
                     → σ
                       ≃s
                       sub-from-sphere n (sphere-type n [ σ ]ty)
                                         (trans (sym (sub-dim σ (sphere-type n)))
                                                (sphere-type-dim n))
prop-sub-from-sphere zero ⟨ .⋆ ⟩′ = refl≃s
prop-sub-from-sphere (suc n) ⟨ ⟨ σ , s ⟩ , t ⟩
  = Ext≃ (Ext≃ (begin
    < σ >s
      ≈⟨ prop-sub-from-sphere n σ ⟩
    < sub-from-sphere n (sphere-type n [ σ ]ty) _ >s
      ≈⟨ sub-from-sphere-≃ n n lem _ _ ⟩
    < sub-from-sphere n (wk-ty (wk-ty (sphere-type n)) [ ⟨ ⟨ σ , s ⟩ , t ⟩ ]ty) _ >s ∎
    ) refl≃tm) refl≃tm
    where
      lem : sphere-type n [ σ ]ty ≃ty wk-ty (wk-ty (sphere-type n)) [ ⟨ ⟨ σ , s ⟩ , t ⟩ ]ty
      lem = begin
        < sphere-type n [ σ ]ty >ty
          ≈˘⟨ apply-sub-wk-ty-≃ (sphere-type n) ⟨ σ , s ⟩ ⟩
        < wk-ty (sphere-type n) [ ⟨ σ , s ⟩ ]ty >ty
          ≈˘⟨ apply-sub-wk-ty-≃ (wk-ty (sphere-type n)) ⟨ ⟨ σ , s ⟩ , t ⟩ ⟩
        < wk-ty (wk-ty (sphere-type n)) [ ⟨ ⟨ σ , s ⟩ , t ⟩ ]ty >ty ∎
        where
          open Reasoning ty-setoid
      open Reasoning sub-setoid


prop-sub-from-disc : (n : ℕ) → (σ : Sub (disc-size n) m ⋆)
                   → σ
                     ≃s
                     sub-from-disc n (wk-ty (sphere-type n) [ σ ]ty)
                                     (trans (sym (sub-dim σ _))
                                            (trans (wk-ty-dim (sphere-type n))
                                                   (sphere-type-dim n)))
                                     (0V [ σ ]tm)
prop-sub-from-disc n ⟨ σ , t ⟩
  = Ext≃ (begin
    < σ >s
      ≈⟨ prop-sub-from-sphere n σ ⟩
    < sub-from-sphere n (sphere-type n [ σ ]ty) _ >s
      ≈˘⟨ sub-from-sphere-≃ n n (apply-sub-wk-ty-≃ (sphere-type n) ⟨ σ , t ⟩) _ _ ⟩
    < sub-from-sphere n (wk-ty (sphere-type n) [ ⟨ σ , t ⟩ ]ty) _ >s ∎) refl≃tm
    where
      open Reasoning sub-setoid


identity-term-sub : (A : Ty m) → (s : Tm m) → (σ : Sub m l ⋆) → identity-term A s [ σ ]tm ≃tm identity-term (A [ σ ]ty) (s [ σ ]tm)
identity-term-sub A s σ = begin
  < identity-term A s [ σ ]tm >tm
    ≈⟨ sub-action-≃-tm (identity-≃ (sub-dim σ A) (sub-from-disc-≃ (ty-dim A) (ty-dim (A [ σ ]ty)) refl≃ty refl (sub-dim σ A) (refl≃tm {s = s}))) (refl≃s {σ = σ}) ⟩
  < (identity (ty-dim (A [ σ ]ty)) (sub-from-disc (ty-dim (A [ σ ]ty)) A _ s ● σ)) >tm
    ≈˘⟨ identity-≃ refl (sub-from-disc-sub (ty-dim (A [ σ ]ty)) A (sub-dim σ A) s σ) ⟩
  < identity-term (A [ σ ]ty) (s [ σ ]tm) >tm ∎
  where open Reasoning tm-setoid

identity-term-wk : (A : Ty m) → (s : Tm m) → wk-tm (identity-term A s) ≃tm identity-term (wk-ty A) (wk-tm s)
identity-term-wk A s
  = Coh≃ (disc-≡ (sym (wk-ty-dim A)))
         (Arr≃ (Var≃ (cong (suc ∘ double) (sym (wk-ty-dim A))) refl)
               (wk-ty-≃ (sphere-≡ (sym (wk-ty-dim A))))
               (Var≃ (cong (suc ∘ double) (sym (wk-ty-dim A))) refl))
         (trans≃s (wk-sub-from-disc (ty-dim A) A refl s)
                  (sub-from-disc-≃ (ty-dim A) (ty-dim (wk-ty A)) refl≃ty (trans (wk-ty-dim A) refl) refl refl≃tm))

identity-term-susp : (A : Ty m) → (s : Tm m) → susp-tm (identity-term A s) ≃tm identity-term (susp-ty A) (susp-tm s)
identity-term-susp A s
  = Coh≃ (trans≃c (disc-susp (ty-dim A)) (disc-≡ (sym (susp-dim A))))
         (Arr≃ (Var≃ (cong (λ - → suc (double -)) (sym (susp-dim A))) refl)
               (trans≃ty (susp-ty-wk (sphere-type (ty-dim A)))
                         (wk-ty-≃ (trans≃ty (sphere-type-susp (ty-dim A))
                                              (sphere-≡ (sym (susp-dim A))))))
               (Var≃ (cong (λ - → suc (double -)) (sym (susp-dim A))) refl))
         (trans≃s (susp-sub-from-disc (ty-dim A) A refl s) (sub-from-disc-≃ (suc (ty-dim A)) (ty-dim (susp-ty A)) refl≃ty (trans (susp-dim A) (cong suc refl)) refl refl≃tm))
