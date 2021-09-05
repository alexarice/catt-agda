{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality

connect : (Γ : Ctx (suc n)) → (x : Tm Γ) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-inc-right : (Γ : Ctx (suc n)) → (x : Tm Γ) → (Δ : Ctx (suc m)) → Sub Δ (connect Γ x Δ)

connect Γ x (∅ , A) = Γ
connect Γ x (Δ , A , B) = (connect Γ x (Δ , A)) , B [ connect-inc-right Γ x (Δ , A) ]ty

connect-inc-right Γ x (∅ , A) = ⟨ ⟨⟩ , x ⟩
connect-inc-right Γ x (Δ , A , B) = ⟨ liftSub (connect-inc-right Γ x (Δ , A)) , 0V ⟩

connect-inc-left : (Γ : Ctx (suc n)) → (x : Tm Γ) → (Δ : Ctx (suc m)) → Sub Γ (connect Γ x Δ)
connect-inc-left Γ x (∅ , A) = idSub Γ
connect-inc-left Γ x (Δ , A , B) = liftSub (connect-inc-left Γ x (Δ , A))

connect-pdb : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-pdb {Γ = Γ} pdb Δ = connect Γ (getFocusTerm pdb) Δ

connect-pdb-inc-left : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → Sub Γ (connect-pdb pdb Δ)
connect-pdb-inc-left {Γ = Γ} pdb Δ = connect-inc-left Γ (getFocusTerm pdb) Δ

connect-pdb-inc-right : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → Sub Δ (connect-pdb pdb Δ)
connect-pdb-inc-right {Γ = Γ} pdb Δ = connect-inc-right Γ (getFocusTerm pdb) Δ

connect-pd : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-pd (Finish pdb) Δ = connect-pdb pdb Δ

connect-pd-inc-left : (pd : Γ ⊢pd₀ d) → (Δ : Ctx (suc m)) → Sub Γ (connect-pd pd Δ)
connect-pd-inc-left (Finish pdb) Δ = connect-pdb-inc-left pdb Δ

connect-pd-inc-right : (pd : Γ ⊢pd₀ d) → (Δ : Ctx (suc m)) → Sub Δ (connect-pd pd Δ)
connect-pd-inc-right (Finish pdb) Δ = connect-pdb-inc-right pdb Δ

new-submax : {Γ : Ctx (suc n)} {Δ : Ctx (suc m)} → (pd : Γ ⊢pd[ d ][ 0 ]) → (pdb : Δ ⊢pd[ submax ][ d′ ]) → ℕ
new-submax {d = d} pdb Base = d
new-submax pdb (Extend pdb2) = pred (new-submax pdb pdb2)
new-submax pdb (Restr pdb2) = suc (new-submax pdb pdb2)

connect-pdb-pdb : (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → connect-pdb pdb Δ ⊢pd[ new-submax pdb pdb2 ][ d′ ]
connect-pdb-foc-ty : (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → (getFocusType pdb2 [ connect-inc-right Γ (getFocusTerm pdb) Δ ]ty) ≃ty getFocusType (connect-pdb-pdb pdb pdb2)
connect-pdb-foc-tm : (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → (getFocusTerm pdb2 [ connect-inc-right Γ (getFocusTerm pdb) Δ ]tm) ≃tm getFocusTerm (connect-pdb-pdb pdb pdb2)

connect-pdb-pdb pdb Base = pdb
connect-pdb-pdb pdb (Extend {Γ = Γ} pdb2) with pdb-is-non-empty pdb2
connect-pdb-pdb pdb (Extend {Γ = Γ , A} pdb2) | ne
  = extend-pd-eq (connect-pdb-pdb pdb pdb2)
                 (connect-pdb-foc-ty pdb pdb2)
                 (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm pdb2) (connect-inc-right _ (getFocusTerm pdb) (Γ , A))) (lift-tm-≃ (connect-pdb-foc-tm pdb pdb2)))
                       (trans≃ty (lift-subbed-ty-≃ (getFocusType pdb2) (connect-inc-right _ (getFocusTerm pdb) (Γ , A))) (lift-ty-≃ (connect-pdb-foc-ty pdb pdb2)))
                       (Var≃ refl))

connect-pdb-pdb pdb (Restr pdb2) = Restr (connect-pdb-pdb pdb pdb2)

connect-pdb-foc-ty pdb Base = pdb-0-focus-ty-is-⋆ pdb
connect-pdb-foc-ty pdb (Extend {Γ = Γ} pdb2) with pdb-is-non-empty pdb2
connect-pdb-foc-ty pdb (Extend {Γ = Γ , A} pdb2) | ne
  = trans≃ty (Arr≃ (lift-subbed-tm-≃ (liftTerm (getFocusTerm pdb2)) (connect-inc-right _ (getFocusTerm pdb) (Γ , A , getFocusType pdb2)))
                   (lift-subbed-ty-≃ (liftType (getFocusType pdb2)) (connect-inc-right _ (getFocusTerm pdb) (Γ , A , getFocusType pdb2)))
                   (Var≃ refl))
             (extend-pd-eq-foc-ty (connect-pdb-pdb pdb pdb2)
                                  (connect-pdb-foc-ty pdb pdb2)
                                  (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm pdb2) (connect-inc-right _ (getFocusTerm pdb) (Γ , A))) (lift-tm-≃ (connect-pdb-foc-tm pdb pdb2)))
                                        (trans≃ty (lift-subbed-ty-≃ (getFocusType pdb2) (connect-inc-right _ (getFocusTerm pdb) (Γ , A))) (lift-ty-≃ (connect-pdb-foc-ty pdb pdb2)))
                                        (Var≃ refl)))
connect-pdb-foc-ty {Γ = Γ} {Δ = Δ} pdb (Restr pdb2)
  = trans≃ty (ty-base-subbed (getFocusType pdb2) (connect-inc-right Γ (getFocusTerm pdb) Δ)) (ty-base-≃ (connect-pdb-foc-ty pdb pdb2))

connect-pdb-foc-tm pdb Base = refl≃tm
connect-pdb-foc-tm pdb (Extend {Γ = Γ} pdb2) with pdb-is-non-empty pdb2
connect-pdb-foc-tm pdb (Extend {Γ = Γ , A} pdb2) | ne
  = extend-pd-eq-foc-tm (connect-pdb-pdb pdb pdb2)
                        (connect-pdb-foc-ty pdb pdb2)
                        (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm pdb2) (connect-inc-right _ (getFocusTerm pdb) (Γ , A))) (lift-tm-≃ (connect-pdb-foc-tm pdb pdb2)))
                              (trans≃ty (lift-subbed-ty-≃ (getFocusType pdb2) (connect-inc-right _ (getFocusTerm pdb) (Γ , A))) (lift-ty-≃ (connect-pdb-foc-ty pdb pdb2)))
                              (Var≃ refl))
connect-pdb-foc-tm {Γ = Γ} {Δ = Δ} pdb (Restr pdb2)
  = trans≃tm (ty-tgt-subbed (getFocusType pdb2) (connect-inc-right Γ (getFocusTerm pdb) Δ)) (ty-tgt-≃ (connect-pdb-foc-ty pdb pdb2))

connected-dim : {Γ : Ctx (suc n)} {Δ : Ctx (suc m)} → (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → ℕ
connected-dim (Finish pdb) (Finish pdb2) = new-submax pdb pdb2

connect-pd-pd : {Γ : Ctx (suc n)} {Δ : Ctx (suc m)} → (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → connect-pd pd Δ ⊢pd₀ connected-dim pd pd2
connect-pd-pd (Finish pdb) (Finish pdb2) = Finish (connect-pdb-pdb pdb pdb2)

sub-from-connect : Sub Γ Υ → (t : Tm Γ) → Sub Δ Υ → Sub (connect Γ t Δ) Υ
sub-from-connect σ s ⟨ ⟨⟩ , t ⟩ = σ
sub-from-connect σ s ⟨ ⟨ τ , u ⟩ , t ⟩ = ⟨ sub-from-connect σ s ⟨ τ , u ⟩ , t ⟩

sub-from-connect-pdb : (pdb : Γ ⊢pd[ submax ][ 0 ]) → Sub Γ Υ → Sub Δ Υ → Sub (connect-pdb pdb Δ) Υ
sub-from-connect-pdb pdb σ τ = sub-from-connect σ (getFocusTerm pdb) τ

sub-from-connect-pd : (pd : Γ ⊢pd₀ d) → Sub Γ Υ → Sub Δ Υ → Sub (connect-pd pd Δ) Υ
sub-from-connect-pd (Finish pdb) σ τ = sub-from-connect-pdb pdb σ τ
