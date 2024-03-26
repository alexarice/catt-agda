module Catt.Dyck.Pruning.Properties where

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
open import Catt.Discs.Properties
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pruning
open import Catt.Dyck.Support
open import Catt.Support.Context

dyck-type-prune : (p : Peak dy) → dyck-type (dy // p) ≃ty dyck-type dy [ π p ]ty
dyck-term-prune : (p : Peak dy) → dyck-term (dy // p) ≃tm dyck-term dy [ π p ]tm

dyck-type-prune (⇕pk dy) = begin
  < dyck-type dy >ty
    ≈˘⟨ id-on-ty (dyck-type dy) ⟩
  < dyck-type dy [ idSub ]ty >ty
    ≈˘⟨ apply-sub-wk-ty-≃ (dyck-type dy) ⟨ idSub , dyck-term dy ⟩ ⟩
  < wk-ty (dyck-type dy) [ ⟨ idSub , dyck-term dy ⟩ ]ty >ty
    ≈˘⟨ apply-sub-wk-ty-≃ (wk-ty (dyck-type dy)) (π (⇕pk dy)) ⟩
  < dyck-type (⇓ (⇑ dy)) [ π (⇕pk dy) ]ty >ty ∎
  where
    open Reasoning ty-setoid
dyck-type-prune (⇑pk {dy = dy} p) = Arr≃ l1 l2 refl≃tm
  where
    l1 : wk-tm (wk-tm (dyck-term (dy // p))) ≃tm
           (wk-tm (wk-tm (dyck-term dy)) [ π (⇑pk p) ]tm)
    l1 = begin
      < wk-tm (wk-tm (dyck-term (dy // p))) >tm
        ≈⟨ wk-tm-≃ (wk-tm-≃ (dyck-term-prune p)) ⟩
      < wk-tm (wk-tm (dyck-term dy [ π p ]tm)) >tm
        ≈˘⟨ wk-tm-≃ (apply-wk-sub-tm-≃ (dyck-term dy) (π p)) ⟩
      < wk-tm (dyck-term dy [ wk-sub (π p) ]tm) >tm
        ≈˘⟨ apply-wk-sub-tm-≃ (dyck-term dy) (wk-sub (π p)) ⟩
      < dyck-term dy [ wk-sub (wk-sub (π p)) ]tm >tm
        ≈˘⟨ apply-sub-wk-tm-≃ (dyck-term dy) ⟨ wk-sub (wk-sub (π p)) , 1V ⟩ ⟩
      < wk-tm (dyck-term dy) [ ⟨ wk-sub (wk-sub (π p)) , 1V ⟩ ]tm >tm
        ≈˘⟨ apply-sub-wk-tm-≃  (wk-tm (dyck-term dy)) ⟨ ⟨ wk-sub (wk-sub (π p)) , 1V ⟩ , 0V ⟩ ⟩
      < wk-tm (wk-tm (dyck-term dy)) [ ⟨ ⟨ (wk-sub (wk-sub (π p))) , 1V ⟩ , 0V ⟩ ]tm >tm ∎
      where
        open Reasoning tm-setoid

    l2 : wk-ty (wk-ty (dyck-type (dy // p))) ≃ty
           (wk-ty (wk-ty (dyck-type dy)) [ π (⇑pk p) ]ty)
    l2 = begin
      < wk-ty (wk-ty (dyck-type (dy // p))) >ty
        ≈⟨ wk-ty-≃ (wk-ty-≃ (dyck-type-prune p)) ⟩
      < wk-ty (wk-ty (dyck-type dy [ π p ]ty)) >ty
        ≈˘⟨ wk-ty-≃ (apply-wk-sub-ty-≃ (dyck-type dy) (π p)) ⟩
      < wk-ty (dyck-type dy [ wk-sub (π p) ]ty) >ty
        ≈˘⟨ apply-wk-sub-ty-≃ (dyck-type dy) (wk-sub (π p)) ⟩
      < dyck-type dy [ wk-sub (wk-sub (π p)) ]ty >ty
        ≈˘⟨ apply-sub-wk-ty-≃ (dyck-type dy) ⟨ wk-sub (wk-sub (π p)) , 1V ⟩ ⟩
      < wk-ty (dyck-type dy) [ ⟨ wk-sub (wk-sub (π p)) , 1V ⟩ ]ty >ty
        ≈˘⟨ apply-sub-wk-ty-≃ (wk-ty (dyck-type dy)) ⟨ ⟨ wk-sub (wk-sub (π p)) , 1V ⟩ , 0V ⟩ ⟩
      < wk-ty (wk-ty (dyck-type dy)) [ ⟨ ⟨ (wk-sub (wk-sub (π p))) , 1V ⟩ , 0V ⟩ ]ty >ty ∎
      where
        open Reasoning ty-setoid
dyck-type-prune (⇓pk {dy = dy} p) = begin
  < dyck-type (⇓ dy // (⇓pk p)) >ty
    ≈˘⟨ ty-base-wk (dyck-pre-type (dy // p)) ⟩
  < ty-base (dyck-type (dy // p)) >ty
    ≈⟨ ty-base-≃ (dyck-type-prune p) ⟩
  < ty-base (dyck-type dy [ π p ]ty) >ty
    ≈˘⟨ ty-base-sub (dyck-type dy) (π p) ⟩
  < ty-base (dyck-type dy) [ π p ]ty >ty
    ≈⟨ sub-action-≃-ty (ty-base-wk (dyck-pre-type dy)) refl≃s ⟩
  < dyck-type (⇓ dy) [ π (⇓pk p) ]ty >ty ∎
  where
    open Reasoning ty-setoid

dyck-term-prune (⇕pk dy) = refl≃tm
dyck-term-prune (⇑pk p) = refl≃tm
dyck-term-prune (⇓pk {dy = dy} p) = begin
  < ty-tgt′ (dyck-type (dy // p)) >tm
    ≈⟨ ty-tgt′-≃ (dyck-type-prune p) ⟩
  < ty-tgt′ (dyck-type dy [ π p ]ty) >tm
    ≈˘⟨ ty-tgt′-sub (dyck-type dy) (π p) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄ ⟩
  < dyck-term (⇓ dy) [ π (⇓pk p) ]tm >tm ∎
  where
    open Reasoning tm-setoid

wk-//s : (p : Peak dy) → (σ : Sub _ n ⋆) → wk-sub σ //s p ≃s wk-sub (σ //s p)
wk-//s (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ = refl≃s
wk-//s (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ = Ext≃ (Ext≃ (wk-//s p σ) refl≃tm) refl≃tm
wk-//s (⇓pk p) σ = wk-//s p σ

prune-susp-peak : (p : Peak dy) → susp-dyck dy // (susp-peak p) ≃d susp-dyck (dy // p)
prune-susp-peak (⇕pk dy) = refl≃d
prune-susp-peak (⇑pk p) = ⇑≃ (prune-susp-peak p)
prune-susp-peak (⇓pk p) = ⇓≃ (prune-susp-peak p)

susp-π : (p : Peak dy) → π (susp-peak p) ≃s susp-sub (π p)
susp-π (⇕pk dy) = Ext≃ (Ext≃ (sym≃s susp-functorial-id) (susp-dyck-term dy)) (begin
  < identity-term (dyck-type (susp-dyck dy)) (dyck-term (susp-dyck dy)) >tm
    ≈⟨ identity-term-≃ (susp-dyck-type dy) (susp-dyck-term dy) ⟩
  < identity-term (susp-ty (dyck-type dy)) (susp-tm (dyck-term dy)) >tm
    ≈˘⟨ identity-term-susp (dyck-type dy) (dyck-term dy) ⟩
  < susp-tm (identity-term (dyck-type dy) (dyck-term dy)) >tm ∎)
  where
    open Reasoning tm-setoid
susp-π (⇑pk p)
  = Ext≃ (Ext≃ lem
               refl≃tm)
         refl≃tm
  where
    lem : wk-sub (wk-sub (π (susp-peak p)))
          ≃s
          susp-sub (wk-sub (wk-sub (π p)))
    lem = begin
      < wk-sub (wk-sub (π (susp-peak p))) >s
        ≈⟨ wk-sub-≃ (wk-sub-≃ (susp-π p)) ⟩
      < wk-sub (wk-sub (susp-sub (π p))) >s
        ≈˘⟨ wk-sub-≃ (susp-sub-wk (π p)) ⟩
      < wk-sub (susp-sub (wk-sub (π p))) >s
        ≈˘⟨ susp-sub-wk (wk-sub (π p)) ⟩
      < susp-sub (wk-sub (wk-sub (π p))) >s ∎
      where
        open Reasoning sub-setoid
susp-π (⇓pk p) = susp-π p

susp-//s : {dy : Dyck (suc n) d} → (p : Peak dy) → (σ : Sub (3 + double n) m ⋆)
         → susp-sub σ //s susp-peak p ≃s susp-sub (σ //s p)
susp-//s (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ = refl≃s
susp-//s (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ = Ext≃ (Ext≃ (susp-//s p σ) refl≃tm) refl≃tm
susp-//s (⇓pk p) σ = susp-//s p σ

//s-sub : {dy : Dyck (suc n) d} → (p : Peak dy) → (σ : Sub (3 + double n) m ⋆) → (τ : Sub m l ⋆)
        → σ ● τ //s p ≃s (σ //s p) ● τ
//s-sub (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ τ = refl≃s
//s-sub (⇑pk p) ⟨ ⟨ σ , s ⟩ , t ⟩ τ = Ext≃ (Ext≃ (//s-sub p σ τ) refl≃tm) refl≃tm
//s-sub (⇓pk p) σ τ = //s-sub p σ τ

prune-dim : {dy : Dyck (suc n) d} → (p : Peak dy) → dyck-dim (dy // p) ≤ dyck-dim dy
prune-dim (⇕pk {d = d} dy) = m≤m⊔n (dyck-dim (⇓ (⇑ dy) // ⇕pk dy)) (suc d)
prune-dim (⇑pk {d = d} p) = ⊔-monoˡ-≤ (suc d) (prune-dim p)
prune-dim (⇓pk p) = prune-dim p

peak-1-lem : {dy : Dyck 1 d} → (p q : Peak dy) → p ≡ q
peak-1-lem (⇕pk dy) (⇕pk .dy) = refl
peak-1-lem (⇓pk p) (⇓pk q) = cong ⇓pk (peak-1-lem p q)

prune-peak : {dy : Dyck (suc n) d} → (p q : Peak dy) → .(p ≢ q) → Peak (dy // p)
prune-peak (⇕pk dy) (⇕pk .dy) x = ⊥-elim (x refl)
prune-peak (⇕pk dy) (⇓pk (⇑pk q)) x = q
prune-peak {n = suc zero} (⇑pk p) (⇑pk q) x = ⊥-elim (x (cong ⇑pk (peak-1-lem p q)))
prune-peak {n = 2+ n} (⇑pk p) (⇑pk q) x = ⇑pk (prune-peak p q (x ∘ cong ⇑pk))
prune-peak (⇓pk p) (⇓pk q) x = ⇓pk (prune-peak p q (x ∘ cong ⇓pk))
prune-peak (⇓pk (⇑pk p)) (⇕pk dy) x = ⇕pk (dy // p)

prune-peak-prop : {dy : Dyck (suc n) d} → (p q : Peak dy) → .(x : p ≢ q) → peak-term (prune-peak p q x) ≃tm peak-term q [ π p ]tm
prune-peak-prop (⇕pk dy) (⇕pk .dy) x = ⊥-elim (x refl)
prune-peak-prop (⇕pk dy) (⇓pk (⇑pk q)) x = begin
  < peak-term q >tm
    ≈˘⟨ id-on-tm (peak-term q) ⟩
  < peak-term q [ idSub ]tm >tm
    ≈˘⟨ apply-sub-wk-tm-≃ (peak-term q) _ ⟩
  < wk-tm (peak-term q) [ ⟨ idSub , dyck-term dy ⟩ ]tm >tm
    ≈˘⟨ apply-sub-wk-tm-≃ (wk-tm (peak-term q)) _ ⟩
  < wk-tm (wk-tm (peak-term q))
    [ ⟨ ⟨ idSub , dyck-term dy ⟩ , identity-term (dyck-type dy) (dyck-term dy) ⟩ ]tm >tm ∎
  where
    open Reasoning tm-setoid
prune-peak-prop {n = suc zero} (⇑pk p) (⇑pk q) x = ⊥-elim (x (cong ⇑pk (peak-1-lem p q)))
prune-peak-prop {n = 2+ n} (⇑pk p) (⇑pk q) x = begin
  < wk-tm (wk-tm (peak-term (prune-peak p q _))) >tm
    ≈⟨ wk-tm-≃ (wk-tm-≃ (prune-peak-prop p q _)) ⟩
  < wk-tm (wk-tm (peak-term q [ π p ]tm)) >tm
    ≈˘⟨ wk-tm-≃ (apply-wk-sub-tm-≃ (peak-term q) (π p)) ⟩
  < wk-tm (peak-term q [ wk-sub (π p) ]tm) >tm
    ≈˘⟨ apply-wk-sub-tm-≃ (peak-term q) (wk-sub (π p)) ⟩
  < peak-term q [ wk-sub (wk-sub (π p)) ]tm >tm
    ≈˘⟨ apply-sub-wk-tm-≃ (peak-term q) _ ⟩
  < wk-tm (peak-term q) [ ⟨ wk-sub (wk-sub (π p)) , Var 1F ⟩ ]tm >tm
    ≈˘⟨ apply-sub-wk-tm-≃ (wk-tm (peak-term q)) _ ⟩
  < wk-tm (wk-tm (peak-term q)) [ ⟨ ⟨ wk-sub (wk-sub (π p)) , Var 1F ⟩ , Var 0F ⟩ ]tm >tm ∎
  where
    open Reasoning tm-setoid
prune-peak-prop (⇓pk p) (⇓pk q) x = prune-peak-prop p q (x ∘ cong ⇓pk)
prune-peak-prop (⇓pk (⇑pk p)) (⇕pk dy) x = refl≃tm

prune-conf : {dy : Dyck (2+ n) d} → (p q : Peak dy) → (x : p ≢ q) → dy // p // prune-peak p q x ≃d dy // q // prune-peak q p (≢-sym x)
prune-conf (⇕pk dy) (⇕pk .dy) x = ⊥-elim (x refl)
prune-conf (⇕pk dy) (⇓pk (⇑pk q)) x = refl≃d
prune-conf {n = zero} (⇑pk p) (⇑pk q) x = ⊥-elim (x (cong ⇑pk (peak-1-lem p q)))
prune-conf {n = suc n} (⇑pk p) (⇑pk q) x = ⇑≃ (prune-conf p q (x ∘ cong ⇑pk))
prune-conf (⇓pk p) (⇓pk q) x = ⇓≃ (prune-conf p q (x ∘ cong ⇓pk))
prune-conf (⇓pk (⇑pk p)) (⇕pk dy) x = refl≃d

prune-sub-conf : {dy : Dyck (2+ n) d} → (p q : Peak dy) → (σ : Sub (5 + double n) m ⋆) → (x : p ≢ q) → σ //s p //s prune-peak p q x ≃s σ //s q //s prune-peak q p (≢-sym x)
prune-sub-conf (⇕pk dy) (⇕pk .dy) σ x = ⊥-elim (x refl)
prune-sub-conf (⇕pk dy) (⇓pk (⇑pk q)) ⟨ ⟨ σ , s ⟩ , t ⟩ x = refl≃s
prune-sub-conf {n = zero} (⇑pk p) (⇑pk q) σ x = ⊥-elim (x (cong ⇑pk (peak-1-lem p q)))
prune-sub-conf {n = suc n} (⇑pk p) (⇑pk q) ⟨ ⟨ σ , s ⟩ , t ⟩ x = Ext≃ (Ext≃ (prune-sub-conf p q σ (x ∘ cong ⇑pk)) refl≃tm) refl≃tm
prune-sub-conf (⇓pk p) (⇓pk q) σ x = prune-sub-conf p q σ (x ∘ cong ⇓pk)
prune-sub-conf (⇓pk (⇑pk p)) (⇕pk dy) ⟨ ⟨ σ , s ⟩ , t ⟩ x = refl≃s

π-conf-lem-1 : {dy : Dyck (suc n) d} → (q : Peak dy)
             → identity-term (dyck-type dy) (dyck-term dy) [ π q ]tm
               ≃tm
               identity-term (dyck-type (dy // q)) (dyck-term (dy // q))
π-conf-lem-1 {dy = dy} q = begin
  < identity-term (dyck-type dy) (dyck-term dy) [ π q ]tm >tm
    ≈⟨ identity-term-sub (dyck-type dy) (dyck-term dy) (π q) ⟩
  < identity-term (dyck-type dy [ π q ]ty) (dyck-term dy [ π q ]tm) >tm
    ≈˘⟨ identity-term-≃ (dyck-type-prune q) (dyck-term-prune q) ⟩
  < identity-term (dyck-type (dy // q)) (dyck-term (dy // q)) >tm ∎
  where
    open Reasoning tm-setoid

π-conf-lem-2 : {dy : Dyck (suc n) d} → (q : Peak dy)
             → idSub ● π q
               ≃s
               wk-sub (wk-sub (π q)) ● π (⇕pk (dy // q))
π-conf-lem-2 {dy = dy} q = begin
  < idSub ● π q >s
    ≈⟨ id-left-unit (π q) ⟩
  < π q >s
    ≈˘⟨ id-right-unit (π q) ⟩
  < π q ● idSub >s
    ≈˘⟨ apply-sub-wk-sub-≃ (π q) (sub-proj₁ (π (⇕pk (dy // q)))) ⟩
  < wk-sub (π q) ● sub-proj₁ (π (⇕pk (dy // q))) >s
    ≈˘⟨ apply-sub-wk-sub-≃ (wk-sub (π q)) (π (⇕pk (dy // q))) ⟩
  < wk-sub (wk-sub (π q)) ● π (⇕pk (dy // q)) >s ∎
  where
    open Reasoning sub-setoid


π-conf : {dy : Dyck (2+ n) d} → (p q : Peak dy) → (x : p ≢ q) → π p ● π (prune-peak p q x) ≃s π q ● π (prune-peak q p (≢-sym x))
π-conf (⇕pk dy) (⇕pk .dy) x = ⊥-elim (x refl)
π-conf (⇕pk dy) (⇓pk (⇑pk q)) x = Ext≃ (Ext≃ (π-conf-lem-2 q)
                                             (sym≃tm (dyck-term-prune q)))
                                       (π-conf-lem-1 q)
π-conf {n = zero} (⇑pk p) (⇑pk q) x = ⊥-elim (x (cong ⇑pk (peak-1-lem p q)))
π-conf {n = suc n} (⇑pk p) (⇑pk q) x = Ext≃ (Ext≃ lem refl≃tm) refl≃tm
  where
    open Reasoning sub-setoid
    lem : wk-sub (wk-sub (π p)) ● π (prune-peak (⇑pk p) (⇑pk q) x)
          ≃s
          wk-sub (wk-sub (π q)) ● π (prune-peak (⇑pk q) (⇑pk p) (≢-sym x))
    lem = begin
      < wk-sub (wk-sub (π p)) ● π (prune-peak (⇑pk p) (⇑pk q) x) >s
        ≈⟨ apply-sub-wk-sub-≃ (wk-sub (π p)) _ ⟩
      < wk-sub (π p) ● sub-proj₁ (π (prune-peak (⇑pk p) (⇑pk q) x)) >s
        ≈⟨ apply-sub-wk-sub-≃ (π p) _ ⟩
      < π p ● wk-sub (wk-sub (π (prune-peak p q _))) >s
        ≈⟨ apply-wk-sub-sub-≃ (π p) (wk-sub (π (prune-peak p q _))) ⟩
      < wk-sub (π p ● wk-sub (π (prune-peak p q _))) >s
        ≈⟨ wk-sub-≃ (apply-wk-sub-sub-≃ (π p) (π (prune-peak p q _))) ⟩
      < wk-sub (wk-sub (π p ● π (prune-peak p q _))) >s
        ≈⟨ wk-sub-≃ (wk-sub-≃ (π-conf p q (x ∘ cong ⇑pk))) ⟩
      < wk-sub (wk-sub (π q ● π (prune-peak q p _))) >s
        ≈˘⟨ wk-sub-≃ (apply-wk-sub-sub-≃ (π q) (π (prune-peak q p _))) ⟩
      < wk-sub (π q ● wk-sub (π (prune-peak q p _))) >s
        ≈˘⟨ apply-wk-sub-sub-≃ (π q) (wk-sub (π (prune-peak q p _))) ⟩
      < π q ● wk-sub (wk-sub (π (prune-peak q p _))) >s
        ≈˘⟨ apply-sub-wk-sub-≃ (π q) _ ⟩
      < wk-sub (π q) ● sub-proj₁ (π (prune-peak (⇑pk q) (⇑pk p) (≢-sym x))) >s
        ≈˘⟨ apply-sub-wk-sub-≃ (wk-sub (π q)) _ ⟩
      < wk-sub (wk-sub (π q)) ● π (prune-peak (⇑pk q) (⇑pk p) (≢-sym x)) >s ∎
π-conf (⇓pk p) (⇓pk q) x = π-conf p q (x ∘ cong ⇓pk)
π-conf (⇓pk (⇑pk p)) (⇕pk dy) x = Ext≃ (Ext≃ (sym≃s (π-conf-lem-2 p))
                                             (dyck-term-prune p))
                                       (sym≃tm (π-conf-lem-1 p))

disc-prune : (n : ℕ) → ⇓ (dyck-disc (suc n)) // dyck-disc-peak n ≃d dyck-disc n
disc-prune n = refl≃d

sub-from-disc-prune : (d : ℕ) → (A : Ty n) → .(p : ty-dim A ≡ d) → (s u t : Tm n)
                    → sub-from-disc (suc d) (s ─⟨ A ⟩⟶ u) (cong suc p) t //s dyck-disc-peak d
                      ≃s
                      sub-from-disc d A p s
sub-from-disc-prune d A p s u t = refl≃s
