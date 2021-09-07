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

connect : (Γ : Ctx (suc n)) → (x : Tm (suc n)) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-inc-right : (x : Tm (suc n)) → (m : ℕ) → Sub (suc m) (suc (m + n))

connect Γ x (∅ , A) = Γ
connect Γ x (Δ , A , B) = (connect Γ x (Δ , A)) , B [ connect-inc-right x (ctxLength Δ) ]ty

connect-inc-right x zero = ⟨ ⟨⟩ , x ⟩
connect-inc-right x (suc m) = ⟨ liftSub (connect-inc-right x m) , 0V ⟩

connect-inc-left : (x : Tm (suc n)) → (m : ℕ) → Sub (suc n) (suc (m + n))
connect-inc-left x zero = idSub (suc _)
connect-inc-left x (suc m) = liftSub (connect-inc-left x m)

connect-pdb : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-pdb {Γ = Γ} pdb Δ = connect Γ (getFocusTerm pdb) Δ

connect-pdb-inc-left : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → Sub (suc n) (suc (m + n))
connect-pdb-inc-left pdb m = connect-inc-left (getFocusTerm pdb) m

connect-pdb-inc-right : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → Sub (suc m) (suc (m + n))
connect-pdb-inc-right pdb m = connect-inc-right (getFocusTerm pdb) m

connect-pd : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-pd (Finish pdb) Δ = connect-pdb pdb Δ

connect-pd-inc-left : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (m : ℕ) → Sub (suc n) (suc (m + n))
connect-pd-inc-left (Finish pdb) m = connect-pdb-inc-left pdb m

connect-pd-inc-right : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (m : ℕ) → Sub (suc m) (suc (m + n))
connect-pd-inc-right (Finish pdb) m = connect-pdb-inc-right pdb m

new-submax : {Γ : Ctx (suc n)} {Δ : Ctx (suc m)} → (pd : Γ ⊢pd[ d ][ 0 ]) → (pdb : Δ ⊢pd[ submax ][ d′ ]) → ℕ
new-submax {d = d} pdb Base = d
new-submax pdb (Extend pdb2) = pred (new-submax pdb pdb2)
new-submax pdb (Restr pdb2) = suc (new-submax pdb pdb2)

connect-pdb-pdb : (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → connect-pdb pdb Δ ⊢pd[ new-submax pdb pdb2 ][ d′ ]
connect-pdb-foc-ty : (pdb : Γ ⊢pd[ d ][ 0 ]) → {Δ : Ctx (suc m)} → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → (getFocusType pdb2 [ connect-pdb-inc-right pdb m ]ty) ≃ty getFocusType (connect-pdb-pdb pdb pdb2)
connect-pdb-foc-tm : (pdb : Γ ⊢pd[ d ][ 0 ]) → {Δ : Ctx (suc m)} → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → (getFocusTerm pdb2 [ connect-pdb-inc-right pdb m ]tm) ≃tm getFocusTerm (connect-pdb-pdb pdb pdb2)

connect-pdb-pdb pdb Base = pdb
connect-pdb-pdb pdb (Extend {Γ = Γ , A} pdb2)
  = extend-pd-eq (connect-pdb-pdb pdb pdb2)
                 (connect-pdb-foc-ty pdb pdb2)
                 (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm pdb2) (connect-pdb-inc-right pdb (ctxLength Γ))) (lift-tm-≃ (connect-pdb-foc-tm pdb pdb2)))
                       (trans≃ty (lift-subbed-ty-≃ (getFocusType pdb2) (connect-pdb-inc-right pdb (ctxLength Γ))) (lift-ty-≃ (connect-pdb-foc-ty pdb pdb2)))
                       (Var≃ refl refl))

connect-pdb-pdb pdb (Restr pdb2) = Restr (connect-pdb-pdb pdb pdb2)

connect-pdb-foc-ty pdb Base = pdb-0-focus-ty-is-⋆ pdb
connect-pdb-foc-ty pdb (Extend {Γ = Γ , A} pdb2)
  = trans≃ty (Arr≃ (lift-subbed-tm-≃ (liftTerm (getFocusTerm pdb2)) (connect-pdb-inc-right pdb (ctxLength (Γ , A))))
                   (lift-subbed-ty-≃ (liftType (getFocusType pdb2)) (connect-pdb-inc-right pdb (ctxLength (Γ , A))))
                   (Var≃ refl refl))
             (extend-pd-eq-foc-ty (connect-pdb-pdb pdb pdb2)
                                  (connect-pdb-foc-ty pdb pdb2)
                                  (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm pdb2) (connect-pdb-inc-right pdb (ctxLength Γ))) (lift-tm-≃ (connect-pdb-foc-tm pdb pdb2)))
                                        (trans≃ty (lift-subbed-ty-≃ (getFocusType pdb2) (connect-pdb-inc-right pdb (ctxLength Γ))) (lift-ty-≃ (connect-pdb-foc-ty pdb pdb2)))
                                        (Var≃ refl refl)))
connect-pdb-foc-ty {m = m} pdb (Restr pdb2)
  = trans≃ty (ty-base-subbed (getFocusType pdb2) (connect-pdb-inc-right pdb m)) (ty-base-≃ (connect-pdb-foc-ty pdb pdb2))

connect-pdb-foc-tm pdb Base = refl≃tm
connect-pdb-foc-tm pdb (Extend {Γ = Γ , A} pdb2)
  = extend-pd-eq-foc-tm (connect-pdb-pdb pdb pdb2)
                        (connect-pdb-foc-ty pdb pdb2)
                        (Arr≃ (trans≃tm (lift-subbed-tm-≃ (getFocusTerm pdb2) (connect-pdb-inc-right pdb (ctxLength Γ))) (lift-tm-≃ (connect-pdb-foc-tm pdb pdb2)))
                              (trans≃ty (lift-subbed-ty-≃ (getFocusType pdb2) (connect-pdb-inc-right pdb (ctxLength Γ))) (lift-ty-≃ (connect-pdb-foc-ty pdb pdb2)))
                              (Var≃ refl refl))
connect-pdb-foc-tm {m = m} pdb (Restr pdb2)
  = trans≃tm (ty-tgt-subbed (getFocusType pdb2) (connect-pdb-inc-right pdb m)) (ty-tgt-≃ (connect-pdb-foc-ty pdb pdb2))

connected-dim : {Γ : Ctx (suc n)} {Δ : Ctx (suc m)} → (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → ℕ
connected-dim (Finish pdb) (Finish pdb2) = new-submax pdb pdb2

connect-pd-pd : {Γ : Ctx (suc n)} {Δ : Ctx (suc m)} → (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → connect-pd pd Δ ⊢pd₀ connected-dim pd pd2
connect-pd-pd (Finish pdb) (Finish pdb2) = Finish (connect-pdb-pdb pdb pdb2)

sub-from-connect : Sub (suc n) l → (t : Tm (suc n)) → Sub (suc m) l → Sub (suc (m + n)) l
sub-from-connect σ s ⟨ ⟨⟩ , t ⟩ = σ
sub-from-connect σ s ⟨ ⟨ τ , u ⟩ , t ⟩ = ⟨ sub-from-connect σ s ⟨ τ , u ⟩ , t ⟩

sub-from-connect-pdb : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → Sub (suc n) l → Sub (suc m) l → Sub (suc (m + n)) l
sub-from-connect-pdb pdb σ τ = sub-from-connect σ (getFocusTerm pdb) τ

sub-from-connect-pd : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → Sub (suc n) l → Sub (suc m) l → Sub (suc (m + n)) l
sub-from-connect-pd (Finish pdb) σ τ = sub-from-connect-pdb pdb σ τ
