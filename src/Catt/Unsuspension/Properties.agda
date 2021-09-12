{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Unsuspension.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Unsuspension
open import Data.Nat
open import Data.Fin.Properties using (toℕ-injective)
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Relation.Nullary
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Data.Empty
open import Catt.Globular.Properties

-- is-unsuspendable-preserve-getFst : (σ : Sub (suc (suc n)) (suc (suc m)))
--                                  → .⦃ is-unsuspendable-sub σ ⦄
--                                  → getFst [ σ ]tm ≃tm getFst {n = m}
-- is-unsuspendable-preserve-getFst ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ ⦃ u ⦄ = sym≃tm (recompute (≃tm-dec getFst (getFst [ ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ ]tm)) (proj₁ u))
-- is-unsuspendable-preserve-getFst ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ ⦃ u ⦄ = is-unsuspendable-preserve-getFst ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ ⦃ proj₁ u ⦄

-- is-unsuspendable-preserve-getSnd : (σ : Sub (suc (suc n)) (suc (suc m)))
--                                  → .⦃ is-unsuspendable-sub σ ⦄
--                                  → getSnd [ σ ]tm ≃tm getSnd {n = m}
-- is-unsuspendable-preserve-getSnd ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ ⦃ u ⦄ = sym≃tm (recompute (≃tm-dec getSnd (getSnd [ ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ ]tm)) (proj₁ u))
-- is-unsuspendable-preserve-getSnd ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ ⦃ u ⦄ = is-unsuspendable-preserve-getFst ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ ⦃ proj₁ u ⦄

is-unsuspendable-ctx-≃ : Γ ≃c Δ → ⦃ is-unsuspendable-ctx Γ ⦄ → is-unsuspendable-ctx Δ
is-unsuspendable-ty-≃ : A ≃ty B → ⦃ is-unsuspendable-ty A ⦄ → is-unsuspendable-ty B
is-unsuspendable-tm-≃ : s ≃tm t → ⦃ is-unsuspendable-tm s ⦄ → is-unsuspendable-tm t
is-unsuspendable-sub-≃ : σ ≃s τ → ⦃ is-unsuspendable-sub σ ⦄ → is-unsuspendable-sub τ

is-unsuspendable-ctx-≃ (Add≃ (Add≃ Emp≃ (Star≃ x₁)) (Star≃ x)) = _
is-unsuspendable-ctx-≃ (Add≃ (Add≃ (Add≃ p z) y) x) ⦃ a ,, b ⦄ = is-unsuspendable-ctx-≃ (Add≃ (Add≃ p z) y) ⦃ a ⦄ ,, is-unsuspendable-ty-≃ x ⦃ b ⦄

is-unsuspendable-ty-≃ (Arr≃ p (Star≃ refl) r) ⦃ a ,, b ⦄ = (trans≃tm a p) ,, trans≃tm b r
is-unsuspendable-ty-≃ (Arr≃ p q@(Arr≃ _ _ _) r) ⦃ a ,, (b ,, c) ⦄ = (is-unsuspendable-ty-≃ q ⦃ a ⦄) ,, (is-unsuspendable-tm-≃ p ⦃ b ⦄ ,, is-unsuspendable-tm-≃ r ⦃ c ⦄)

is-unsuspendable-tm-≃ (Var≃ p q) ⦃ u ⦄ = ≤-trans (≤-reflexive (sym (cong suc q))) (≤-trans u (≤-reflexive (cong pred (cong pred p))))
is-unsuspendable-tm-≃ (Coh≃ {suc (suc n)} {_} {zero} p q r) ⦃ u ⦄ with cong pred (≃c-preserve-length p)
... | ()
is-unsuspendable-tm-≃ (Coh≃ {suc (suc n)} {_} {suc zero} p q r) ⦃ u ⦄ with cong pred (cong pred (≃c-preserve-length p))
... | ()
is-unsuspendable-tm-≃ (Coh≃ {suc (suc n)} {_} {suc (suc m)} p q r) ⦃ a ,, (b ,, c) ⦄ = is-unsuspendable-ctx-≃ p ⦃ a ⦄ ,, (is-unsuspendable-ty-≃ q ⦃ b ⦄ ,, is-unsuspendable-sub-≃ r ⦃ c ⦄)

is-unsuspendable-sub-≃ (Ext≃ (Ext≃ (Null≃ refl) q) r) ⦃ a ,, b ⦄ = (trans≃tm a q) ,, trans≃tm b r
is-unsuspendable-sub-≃ (Ext≃ (Ext≃ (Ext≃ p q) r) s) ⦃ a ,, b ⦄ = is-unsuspendable-sub-≃ (Ext≃ (Ext≃ p q) r) ⦃ a ⦄ ,, is-unsuspendable-tm-≃ s ⦃ b ⦄

unsuspend-ctx-≃ : (p : Γ ≃c Δ)
                → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                → unsuspend-ctx Γ ≃c unsuspend-ctx Δ ⦃ is-unsuspendable-ctx-≃ p ⦄
unsuspend-ty-≃ : (p : A ≃ty B)
               → .⦃ _ : is-unsuspendable-ty A ⦄
               → unsuspend-ty A ≃ty unsuspend-ty B ⦃ is-unsuspendable-ty-≃ p ⦄
unsuspend-tm-≃ : (p : s ≃tm t)
               → .⦃ _ : is-unsuspendable-tm s ⦄
               → unsuspend-tm s ≃tm unsuspend-tm t ⦃ is-unsuspendable-tm-≃ p ⦄
unsuspend-sub-≃ : (p : σ ≃s τ)
               → .⦃ _ : is-unsuspendable-sub σ ⦄
               → unsuspend-sub σ ≃s unsuspend-sub τ ⦃ is-unsuspendable-sub-≃ p ⦄



unsuspend-ctx-≃ (Add≃ (Add≃ Emp≃ (Star≃ x₁)) (Star≃ x)) = Emp≃
unsuspend-ctx-≃ (Add≃ (Add≃ (Add≃ p z) y) x) ⦃ u ⦄ = Add≃ (unsuspend-ctx-≃ (Add≃ (Add≃ p z) y) ⦃ proj₁ u ⦄) (unsuspend-ty-≃ x ⦃ proj₂ u ⦄)

unsuspend-ty-≃ (Arr≃ x (Star≃ refl) x₁) = Star≃ refl
unsuspend-ty-≃ (Arr≃ p q@(Arr≃ _ _ _) r) ⦃ u ⦄ = Arr≃ (unsuspend-tm-≃ p ⦃ proj₁ (proj₂ u) ⦄) (unsuspend-ty-≃ q ⦃ proj₁ u ⦄) (unsuspend-tm-≃ r ⦃ proj₂ (proj₂ u) ⦄)

unsuspend-tm-≃ (Var≃ refl q) with toℕ-injective q
... | refl = refl≃tm
unsuspend-tm-≃ (Coh≃ {suc (suc n)} {_} {zero} p q r) with cong pred (≃c-preserve-length p)
... | ()
unsuspend-tm-≃ (Coh≃ {suc (suc n)} {_} {suc zero} p q r) with cong pred (cong pred (≃c-preserve-length p))
... | ()
unsuspend-tm-≃ (Coh≃ {suc (suc n)} {_} {suc (suc m)} p q r) ⦃ u ⦄ = Coh≃ (unsuspend-ctx-≃ p ⦃ proj₁ u ⦄) (unsuspend-ty-≃ q ⦃ proj₁ (proj₂ u) ⦄) (unsuspend-sub-≃ r ⦃ proj₂ (proj₂ u) ⦄)

unsuspend-sub-≃ (Ext≃ (Ext≃ (Null≃ refl) y) x) = Null≃ refl
unsuspend-sub-≃ (Ext≃ (Ext≃ (Ext≃ p z) y) x) ⦃ u ⦄ = Ext≃ (unsuspend-sub-≃ (Ext≃ (Ext≃ p z) y) ⦃ proj₁ u ⦄) (unsuspend-tm-≃ x ⦃ proj₂ u ⦄)

is-unsuspendable-functorial-ty-lem : (A : Ty (suc (suc n)) d)
                                   → .⦃ _ : is-unsuspendable-ty A ⦄
                                   → (σ : Sub (suc (suc n)) (suc (suc m)))
                                   → .⦃ _ : is-unsuspendable-sub σ ⦄
                                   → suspTy (unsuspend-ty A [ unsuspend-sub σ ]ty) ≃ty A [ σ ]ty
is-unsuspendable-functorial-ty-lem A σ = begin
  < suspTy (unsuspend-ty A [ unsuspend-sub σ ]ty) >ty ≈⟨ susp-functorial-ty (unsuspend-sub σ) (unsuspend-ty A) ⟩
  < suspTy (unsuspend-ty A) [ suspSub (unsuspend-sub σ) ]ty >ty ≈⟨ sub-action-≃-ty (unsuspend-ty-compat A) (unsuspend-sub-compat σ) ⟩
  < A [ σ ]ty >ty ∎
  where
    open Reasoning ty-setoid

is-unsuspendable-functorial-ty : (A : Ty (suc (suc n)) d)
                               → .⦃ is-unsuspendable-ty A ⦄
                               → (σ : Sub (suc (suc n)) (suc (suc m)))
                               → .⦃ is-unsuspendable-sub σ ⦄
                               → is-unsuspendable-ty (A [ σ ]ty)
is-unsuspendable-functorial-ty A σ = is-unsuspendable-ty-≃ (is-unsuspendable-functorial-ty-lem A σ) ⦃ suspension-is-unsuspendable-ty (unsuspend-ty A [ unsuspend-sub σ ]ty) ⦄


unsuspend-functorial-ty : (A : Ty (suc (suc n)) d)
                        → .⦃ _ : is-unsuspendable-ty A ⦄
                        → (σ : Sub (suc (suc n)) (suc (suc l)))
                        → .⦃ _ : is-unsuspendable-sub σ ⦄
                        → unsuspend-ty (A [ σ ]ty) ⦃ is-unsuspendable-functorial-ty A σ ⦄ ≃ty unsuspend-ty A [ unsuspend-sub σ ]ty
unsuspend-functorial-ty A σ = let
  instance _ = is-unsuspendable-functorial-ty A σ
  instance _ = suspension-is-unsuspendable-ty (unsuspend-ty A [ unsuspend-sub σ ]ty)
  in begin
  < unsuspend-ty (A [ σ ]ty) >ty ≈˘⟨ unsuspend-ty-≃ (is-unsuspendable-functorial-ty-lem A σ) ⟩
  < unsuspend-ty (suspTy (unsuspend-ty A [ unsuspend-sub σ ]ty)) >ty ≈⟨ unsusp-susp-compat-ty (unsuspend-ty A [ unsuspend-sub σ ]ty) ⟩
  < unsuspend-ty A [ unsuspend-sub σ ]ty >ty ∎
  where
    open Reasoning ty-setoid

is-unsuspendable-ty-lift : (A : Ty (suc (suc n)) d) → ⦃ is-unsuspendable-ty A ⦄ → is-unsuspendable-ty (liftType A)
is-unsuspendable-tm-lift : (t : Tm (suc (suc n))) → ⦃ is-unsuspendable-tm t ⦄ → is-unsuspendable-tm (liftTerm t)
is-unsuspendable-sub-lift : (σ : Sub (suc (suc n)) (suc (suc m))) → ⦃ is-unsuspendable-sub σ ⦄ → is-unsuspendable-sub (liftSub σ)

is-unsuspendable-ty-lift (s ─⟨ ⋆ ⟩⟶ t) ⦃ a ,, b ⦄ = (lift-tm-≃ a) ,, lift-tm-≃ b
is-unsuspendable-ty-lift (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) ⦃ a ,, b ,, c ⦄ = is-unsuspendable-ty-lift A ⦃ a ⦄ ,, (is-unsuspendable-tm-lift s ⦃ b ⦄) ,, (is-unsuspendable-tm-lift t ⦃ c ⦄)

is-unsuspendable-tm-lift (Var i) = s≤s it
is-unsuspendable-tm-lift (Coh {n = suc (suc n)} Δ A σ) ⦃ a ,, b ,, c ⦄ = a ,, b ,, is-unsuspendable-sub-lift σ ⦃ c ⦄

is-unsuspendable-sub-lift ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ ⦃ a ,, b ⦄ = (lift-tm-≃ a) ,, lift-tm-≃ b
is-unsuspendable-sub-lift ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ ⦃ a ,, b ⦄ = is-unsuspendable-sub-lift (⟨ ⟨ σ , u ⟩ , s ⟩) ⦃ a ⦄ ,, is-unsuspendable-tm-lift t ⦃ b ⦄

unsuspend-ty-lift : (A : Ty (suc (suc n)) d) → .⦃ _ : is-unsuspendable-ty A ⦄ → unsuspend-ty (liftType A) ⦃ is-unsuspendable-ty-lift A ⦄ ≃ty liftType (unsuspend-ty A)
unsuspend-tm-lift : (t : Tm (suc (suc n))) → .⦃ _ : is-unsuspendable-tm t ⦄ → unsuspend-tm (liftTerm t) ⦃ is-unsuspendable-tm-lift t ⦄ ≃tm liftTerm (unsuspend-tm t)
unsuspend-sub-lift : (σ : Sub (suc (suc n)) (suc (suc m))) → .⦃ _ : is-unsuspendable-sub σ ⦄ → unsuspend-sub (liftSub σ) ⦃ is-unsuspendable-sub-lift σ ⦄ ≃s liftSub (unsuspend-sub σ)

unsuspend-ty-lift (s ─⟨ ⋆ ⟩⟶ t) = refl≃ty
unsuspend-ty-lift (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) ⦃ u ⦄
  = Arr≃ (unsuspend-tm-lift s ⦃ proj₁ (proj₂ u) ⦄)
         (unsuspend-ty-lift A ⦃ proj₁ u ⦄)
         (unsuspend-tm-lift t ⦃ proj₂ (proj₂ u) ⦄)

unsuspend-tm-lift (Var i) = refl≃tm
unsuspend-tm-lift (Coh {n = suc (suc n)} Δ A σ) ⦃ u ⦄ = Coh≃ refl≃c refl≃ty (unsuspend-sub-lift σ ⦃ proj₂ (proj₂ u) ⦄)

unsuspend-sub-lift ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ = refl≃s
unsuspend-sub-lift ⟨ σ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , t ⟩ ⦃ u ⦄
  = Ext≃ (unsuspend-sub-lift σ ⦃ proj₁ u ⦄) (unsuspend-tm-lift t ⦃ proj₂ u ⦄)

is-unsuspendable-src : (A : Ty (suc (suc n)) (suc (suc d))) → ⦃ is-unsuspendable-ty A ⦄ → is-unsuspendable-tm (ty-src A)
is-unsuspendable-src (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) ⦃ u ⦄ = proj₁ (proj₂ u)

is-unsuspendable-tgt : (A : Ty (suc (suc n)) (suc (suc d))) → ⦃ is-unsuspendable-ty A ⦄ → is-unsuspendable-tm (ty-tgt A)
is-unsuspendable-tgt (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) ⦃ u ⦄ = proj₂ (proj₂ u)

is-unsuspendable-base : (A : Ty (suc (suc n)) (suc (suc d))) → ⦃ is-unsuspendable-ty A ⦄ → is-unsuspendable-ty (ty-base A)
is-unsuspendable-base (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) ⦃ u ⦄ = proj₁ u

unsuspend-src : (A : Ty (suc (suc n)) (suc (suc d))) → .⦃ _ : is-unsuspendable-ty A ⦄ → unsuspend-tm (ty-src A) ⦃ is-unsuspendable-src A ⦄ ≃tm ty-src (unsuspend-ty A)
unsuspend-src (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) = refl≃tm

unsuspend-tgt : (A : Ty (suc (suc n)) (suc (suc d))) → .⦃ _ : is-unsuspendable-ty A ⦄ → unsuspend-tm (ty-tgt A) ⦃ is-unsuspendable-tgt A ⦄ ≃tm ty-tgt (unsuspend-ty A)
unsuspend-tgt (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) = refl≃tm

unsuspend-base : (A : Ty (suc (suc n)) (suc (suc d))) → .⦃ _ : is-unsuspendable-ty A ⦄ → unsuspend-ty (ty-base A) ⦃ is-unsuspendable-base A ⦄ ≃ty ty-base (unsuspend-ty A)
unsuspend-base (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) = refl≃ty

unsuspend-ty-suc-≃ : (s : Tm (suc (suc n))) → (A : Ty (suc (suc n)) (suc d)) → (t : Tm (suc (suc n))) → .⦃ _ : is-unsuspendable-ty (s ─⟨ A ⟩⟶ t) ⦄ → unsuspend-ty (s ─⟨ A ⟩⟶ t) ≃ty unsuspend-tm s ⦃ is-unsuspendable-src (s ─⟨ A ⟩⟶ t) ⦄ ─⟨ unsuspend-ty A ⦃ is-unsuspendable-base (s ─⟨ A ⟩⟶ t)  ⦄ ⟩⟶ unsuspend-tm t ⦃ is-unsuspendable-tgt (s ─⟨ A ⟩⟶ t) ⦄
unsuspend-ty-suc-≃ s (s₁ ─⟨ A ⟩⟶ t₁) t = refl≃ty

build-unsuspendable-ty : (s : Tm (suc (suc n))) → (A : Ty (suc (suc n)) d) → (t : Tm (suc (suc n)))
                       → ⦃ is-unsuspendable-tm s ⦄ → ⦃ is-unsuspendable-ty A ⦄ → ⦃ is-unsuspendable-tm t ⦄
                       → is-unsuspendable-ty (s ─⟨ A ⟩⟶ t)
build-unsuspendable-ty s (s₁ ─⟨ A ⟩⟶ t₁) t = it ,, (it ,, it)

unsuspend-pdb : (pdb : Γ ⊢pd[ submax ][ suc d ]) → .⦃ _ : is-unsuspendable-ctx Γ ⦄ → unsuspend-ctx Γ ⊢pd[ submax ][ d ]
is-unsuspendable-pdb-focus-ty : (pdb : Γ ⊢pd[ submax ][ suc d ])
                              → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                              → is-unsuspendable-ty (getFocusType pdb)
is-unsuspendable-pdb-focus-tm : (pdb : Γ ⊢pd[ submax ][ suc d ])
                              → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                              → is-unsuspendable-tm (getFocusTerm pdb)

unsuspend-pdb-focus-ty : (pdb : Γ ⊢pd[ submax ][ suc d ])
                       → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                       → unsuspend-ty (getFocusType pdb) ⦃ is-unsuspendable-pdb-focus-ty pdb ⦄ ≃ty getFocusType (unsuspend-pdb pdb)
unsuspend-pdb-focus-tm : (pdb : Γ ⊢pd[ submax ][ suc d ])
                       → .⦃ _ : is-unsuspendable-ctx Γ ⦄
                       → unsuspend-tm (getFocusTerm pdb) ⦃ is-unsuspendable-pdb-focus-tm pdb ⦄ ≃tm getFocusTerm (unsuspend-pdb pdb)

unsuspend-pdb (Extend {Γ = ∅ , ⋆} Base) = Base
unsuspend-pdb (Extend {Γ = ∅ , ⋆} (Restr pdb)) with pdb-dim-lem pdb
... | ()
unsuspend-pdb (Extend {Γ = ∅ , B , A} pdb) with pdb-len-lem pdb
... | ()
unsuspend-pdb {d = zero} (Extend {Γ = Γ , C , B , A} {d = .0} pdb) ⦃ u ⦄ with getFocusType pdb
... | ⋆ with .(proj₂ (proj₁ u))
... | ()
unsuspend-pdb {d = suc d} (Extend {Γ = Γ , C , B , A} {d = .(suc d)} pdb) ⦃ u ⦄ = let
  instance .x : _
           x = proj₁ (proj₁ u)
           _ = is-unsuspendable-pdb-focus-tm pdb
           _ = is-unsuspendable-pdb-focus-ty pdb
  in extend-pd-eq (unsuspend-pdb pdb)
                  (unsuspend-pdb-focus-ty pdb)
                  (trans≃ty (unsuspend-ty-suc-≃ (liftTerm (getFocusTerm pdb)) (liftType (getFocusType pdb)) 0V
                              ⦃ build-unsuspendable-ty (liftTerm (getFocusTerm pdb)) (liftType (getFocusType pdb)) 0V ⦃ is-unsuspendable-tm-lift (getFocusTerm pdb) ⦄ ⦃ is-unsuspendable-ty-lift (getFocusType pdb) ⦄ ⦃ s≤s z≤n ⦄ ⦄)
                            (Arr≃ (trans≃tm (unsuspend-tm-lift (getFocusTerm pdb)) (lift-tm-≃ (unsuspend-pdb-focus-tm pdb)))
                                  (trans≃ty (unsuspend-ty-lift (getFocusType pdb)) (lift-ty-≃ (unsuspend-pdb-focus-ty pdb)))
                                  refl≃tm))
unsuspend-pdb (Restr pdb) = Restr (unsuspend-pdb pdb)

is-unsuspendable-pdb-focus-ty (Extend {Γ = ∅ , ⋆} Base) = refl≃tm ,, refl≃tm
is-unsuspendable-pdb-focus-ty (Extend {Γ = ∅ , ⋆} (Restr pdb)) with pdb-dim-lem pdb
... | ()
is-unsuspendable-pdb-focus-ty (Extend {Γ = ∅ , B , A} pdb) with pdb-len-lem pdb
... | ()
is-unsuspendable-pdb-focus-ty {d = zero} (Extend {Γ = Γ , C , B , A} {d = .zero} pdb) ⦃ u ⦄ with getFocusType pdb
... | ⋆ with .(proj₂ (proj₁ u))
... | ()
is-unsuspendable-pdb-focus-ty {d = suc d} (Extend {Γ = Γ , C , B , A} {d = .(suc d)} pdb) ⦃ u ⦄ = let
  instance .x : _
           x = proj₁ (proj₁ u)
  in build-unsuspendable-ty (liftTerm (liftTerm (getFocusTerm pdb))) (liftType (liftType (getFocusType pdb))) 1V ⦃ is-unsuspendable-tm-lift _ ⦃ is-unsuspendable-tm-lift _ ⦃ is-unsuspendable-pdb-focus-tm pdb ⦄ ⦄ ⦄ ⦃ is-unsuspendable-ty-lift _ ⦃ is-unsuspendable-ty-lift _ ⦃ is-unsuspendable-pdb-focus-ty pdb ⦄ ⦄ ⦄ ⦃ s≤s (s≤s z≤n) ⦄
is-unsuspendable-pdb-focus-ty (Restr pdb) = is-unsuspendable-base (getFocusType pdb) ⦃ is-unsuspendable-pdb-focus-ty pdb ⦄

is-unsuspendable-pdb-focus-tm (Extend pdb) = s≤s z≤n
is-unsuspendable-pdb-focus-tm (Restr pdb) = is-unsuspendable-tgt (getFocusType pdb) ⦃ is-unsuspendable-pdb-focus-ty pdb ⦄

unsuspend-pdb-focus-ty (Extend {Γ = ∅ , ⋆} Base) = refl≃ty
unsuspend-pdb-focus-ty (Extend {Γ = ∅ , ⋆} (Restr pdb)) with pdb-dim-lem pdb
... | ()
unsuspend-pdb-focus-ty (Extend {Γ = ∅ , B , A} pdb) with pdb-len-lem pdb
... | ()
unsuspend-pdb-focus-ty {d = zero} (Extend {Γ = Γ , C , B , A} {d = .zero} pdb) ⦃ u ⦄ with getFocusType pdb
... | ⋆ with .(proj₂ (proj₁ u))
... | ()
unsuspend-pdb-focus-ty {d = suc d} (Extend {Γ = Γ , C , B , A} {d = .(suc d)} pdb) ⦃ u ⦄ = let
  instance .x : _
           x = proj₁ (proj₁ u)
           _ = is-unsuspendable-pdb-focus-tm pdb
           _ = is-unsuspendable-pdb-focus-ty pdb
           _ = build-unsuspendable-ty (liftTerm (getFocusTerm pdb)) (liftType (getFocusType pdb)) 0V ⦃ is-unsuspendable-tm-lift (getFocusTerm pdb) ⦄ ⦃ is-unsuspendable-ty-lift (getFocusType pdb) ⦄ ⦃ s≤s z≤n ⦄
  in trans≃ty (unsuspend-ty-lift _)
             (extend-pd-eq-foc-ty (unsuspend-pdb pdb)
                  (unsuspend-pdb-focus-ty pdb)
                  (trans≃ty (unsuspend-ty-suc-≃ (liftTerm (getFocusTerm pdb)) (liftType (getFocusType pdb)) 0V
                              ⦃ build-unsuspendable-ty (liftTerm (getFocusTerm pdb)) (liftType (getFocusType pdb)) 0V ⦃ is-unsuspendable-tm-lift (getFocusTerm pdb) ⦄ ⦃ is-unsuspendable-ty-lift (getFocusType pdb) ⦄ ⦃ s≤s z≤n ⦄ ⦄)
                            (Arr≃ (trans≃tm (unsuspend-tm-lift (getFocusTerm pdb)) (lift-tm-≃ (unsuspend-pdb-focus-tm pdb)))
                                  (trans≃ty (unsuspend-ty-lift (getFocusType pdb)) (lift-ty-≃ (unsuspend-pdb-focus-ty pdb)))
                                  refl≃tm)))
unsuspend-pdb-focus-ty (Restr pdb)
  = trans≃ty (unsuspend-base (getFocusType pdb) ⦃ is-unsuspendable-pdb-focus-ty pdb ⦄) (ty-base-≃ (unsuspend-pdb-focus-ty pdb))

unsuspend-pdb-focus-tm (Extend {Γ = ∅ , ⋆} Base) = refl≃tm
unsuspend-pdb-focus-tm (Extend {Γ = ∅ , ⋆} (Restr pdb)) with pdb-dim-lem pdb
... | ()
unsuspend-pdb-focus-tm (Extend {Γ = ∅ , B , A} pdb) with pdb-len-lem pdb
... | ()
unsuspend-pdb-focus-tm {d = zero} (Extend {Γ = Γ , C , B , A} {d = .zero} pdb) ⦃ u ⦄ with getFocusType pdb
... | ⋆ with .(proj₂ (proj₁ u))
... | ()
unsuspend-pdb-focus-tm {d = suc d} (Extend {Γ = Γ , C , B , A} {d = .(suc d)} pdb) ⦃ u ⦄ = let
  instance .x : _
           x = proj₁ (proj₁ u)
           _ = is-unsuspendable-pdb-focus-tm pdb
           _ = is-unsuspendable-pdb-focus-ty pdb
  in extend-pd-eq-foc-tm (unsuspend-pdb pdb)
                  (unsuspend-pdb-focus-ty pdb)
                  (trans≃ty (unsuspend-ty-suc-≃ (liftTerm (getFocusTerm pdb)) (liftType (getFocusType pdb)) 0V
                              ⦃ build-unsuspendable-ty (liftTerm (getFocusTerm pdb)) (liftType (getFocusType pdb)) 0V ⦃ is-unsuspendable-tm-lift (getFocusTerm pdb) ⦄ ⦃ is-unsuspendable-ty-lift (getFocusType pdb) ⦄ ⦃ s≤s z≤n ⦄ ⦄)
                            (Arr≃ (trans≃tm (unsuspend-tm-lift (getFocusTerm pdb)) (lift-tm-≃ (unsuspend-pdb-focus-tm pdb)))
                                  (trans≃ty (unsuspend-ty-lift (getFocusType pdb)) (lift-ty-≃ (unsuspend-pdb-focus-ty pdb)))
                                  refl≃tm))
unsuspend-pdb-focus-tm (Restr pdb) = trans≃tm (unsuspend-tgt (getFocusType pdb) ⦃ is-unsuspendable-pdb-focus-ty pdb ⦄) (ty-tgt-≃ (unsuspend-pdb-focus-ty pdb))

unsuspend-pd : (pd : Γ ⊢pd₀ d) → .⦃ _ : is-unsuspendable-ctx Γ ⦄ → unsuspend-ctx Γ ⊢pd₀ pred d
unsuspend-pd (Finish (Restr pdb)) = Finish (unsuspend-pdb pdb)
