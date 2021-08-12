{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection where

open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Patterns
open import Catt.Dimension
open import Catt.Dimension.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality

no-term-in-empty-context : ¬ (Tm ∅ d)
no-term-in-empty-context (Coh (_ , _) A p ⟨ σ , t ⟩) = no-term-in-empty-context t

connect : (Γ : Ctx (suc n)) → (x : Tm Γ 2) → (Δ : Ctx (suc m)) → Ctx (suc (m + n))
connect-inc-right : (Γ : Ctx (suc n)) → (x : Tm Γ 2) → (Δ : Ctx (suc m)) → Sub Δ (connect Γ x Δ)

connect Γ x (∅ , A) = Γ
connect Γ x (Δ , A , B) = (connect Γ x (Δ , A)) , B [ connect-inc-right Γ x (Δ , A) ]ty

connect-inc-right Γ x (∅ , ⋆) = ⟨ ⟨⟩ , x ⟩
connect-inc-right Γ x (∅ , s ─⟨ A ⟩⟶ t) = ⊥-elim (no-term-in-empty-context s)
connect-inc-right Γ x (Δ , A , B) = ⟨ liftSub (connect-inc-right Γ x (Δ , A)) , 0V ⟩

connect-inc-left : (Γ : Ctx (suc n)) → (x : Tm Γ 2) → (Δ : Ctx (suc m)) → Sub Γ (connect Γ x Δ)
connect-inc-left Γ x (∅ , A) = idSub Γ
connect-inc-left Γ x (Δ , A , B) = liftSub (connect-inc-left Γ x (Δ , A))

connect-pdb : {Γ : Ctx (suc n)} (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc n′)) → Ctx (suc (n′ + n))
connect-pdb {Γ = Γ} pdb Δ = connect Γ (getFocusTerm pdb) Δ

connect-pd : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (Δ : Ctx (suc n′)) → Ctx (suc (n′ + n))
connect-pd (Finish pdb) Δ = connect-pdb pdb Δ

new-submax : {Γ : Ctx (suc n)} {Δ : Ctx (suc n′)} → (pd : Γ ⊢pd[ d ][ 0 ]) → (pdb : Δ ⊢pd[ submax ][ d′ ]) → ℕ
new-submax {d = d} pdb Base = d
new-submax pdb (Extend pdb2) = pred (new-submax pdb pdb2)
new-submax pdb (Restr pdb2) = suc (new-submax pdb pdb2)

connect-pdb-pdb : {Γ : Ctx (suc n)} {Δ : Ctx (suc n′)} → (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → connect-pdb pdb Δ ⊢pd[ new-submax pdb pdb2 ][ d′ ]
connect-pdb-foc-ty : {Γ : Ctx (suc n)} {Δ : Ctx (suc n′)} → (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → (getFocusType pdb2 [ connect-inc-right Γ (getFocusTerm pdb) Δ ]ty) ≡ getFocusType (connect-pdb-pdb pdb pdb2)
connect-pdb-foc-tm : {Γ : Ctx (suc n)} {Δ : Ctx (suc n′)} → (pdb : Γ ⊢pd[ d ][ 0 ]) → (pdb2 : Δ ⊢pd[ submax ][ d′ ]) → (getFocusTerm pdb2 [ connect-inc-right Γ (getFocusTerm pdb) Δ ]tm) ≡ getFocusTerm (connect-pdb-pdb pdb pdb2)

connect-pdb-pdb pdb Base = pdb
connect-pdb-pdb {Γ = Γ} pdb (Extend {Γ = Γ′ , A} pdb2)
  = extend-pd-eq (connect-pdb-pdb pdb pdb2)
                 (connect-pdb-foc-ty pdb pdb2)
                 (arr-equality (trans (lift-subbed-tm (getFocusTerm pdb2) (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                      (cong liftTerm (connect-pdb-foc-tm pdb pdb2)))
                               (trans (lift-subbed-ty (getFocusType pdb2) (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                      (cong liftType (connect-pdb-foc-ty pdb pdb2)))
                               refl)
connect-pdb-pdb pdb (Restr pdb2) = Restr (connect-pdb-pdb pdb pdb2)

connect-pdb-foc-ty pdb Base with getFocusType pdb
... | ⋆ = refl
connect-pdb-foc-ty {Γ = Γ} pdb (Extend {Γ = Γ′ , A} pdb2)
  = trans (arr-equality (trans (lift-subbed-tm (liftTerm (getFocusTerm pdb2)) ⟨ (liftSub (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A))) , 0V ⟩)
                               (cong liftTerm (trans (lift-subbed-tm (getFocusTerm pdb2) (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                                     (cong liftTerm (connect-pdb-foc-tm pdb pdb2)))))
                        (trans (lift-subbed-ty (liftType (getFocusType pdb2)) ⟨ (liftSub (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A))) , 0V ⟩)
                               (cong liftType (trans (lift-subbed-ty (getFocusType pdb2) (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                                     (cong liftType (connect-pdb-foc-ty pdb pdb2)))))
                        refl)
          (extend-pd-eq-foc-ty (connect-pdb-pdb pdb pdb2)
                               (connect-pdb-foc-ty pdb pdb2)
                               (arr-equality (trans (lift-subbed-tm (getFocusTerm pdb2) (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                                    (cong liftTerm (connect-pdb-foc-tm pdb pdb2)))
                                             (trans (lift-subbed-ty (getFocusType pdb2) (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                                    (cong liftType (connect-pdb-foc-ty pdb pdb2)))
                                             refl))
connect-pdb-foc-ty {Γ = Γ} {Δ = Δ} pdb (Restr pdb2)
  = trans (base-subbed (getFocusType pdb2) (connect-inc-right Γ (getFocusTerm pdb) Δ))
          (cong ty-base (connect-pdb-foc-ty pdb pdb2))

connect-pdb-foc-tm pdb Base = refl
connect-pdb-foc-tm {Γ = Γ} pdb (Extend {Γ = Γ′ , A} pdb2)
  = extend-pd-eq-foc-tm (connect-pdb-pdb pdb pdb2)
                        (connect-pdb-foc-ty pdb pdb2)
                          (arr-equality (trans (lift-subbed-tm (getFocusTerm pdb2) (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                               (cong liftTerm (connect-pdb-foc-tm pdb pdb2)))
                                        (trans (lift-subbed-ty (getFocusType pdb2) (connect-inc-right Γ (getFocusTerm pdb) (Γ′ , A)))
                                               (cong liftType (connect-pdb-foc-ty pdb pdb2)))
                                        refl)
connect-pdb-foc-tm {Γ = Γ} {Δ = Δ} pdb (Restr pdb2)
  = trans (tgt-subbed (getFocusType pdb2) (connect-inc-right Γ (getFocusTerm pdb) Δ))
          (cong ty-tgt (connect-pdb-foc-ty pdb pdb2))

connected-dim : {Γ : Ctx (suc n)} {Δ : Ctx (suc n′)} → (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → ℕ
connected-dim (Finish pdb) (Finish pdb2) = new-submax pdb pdb2

connect-pd-pd : {Γ : Ctx (suc n)} {Δ : Ctx (suc n′)} → (pd : Γ ⊢pd₀ d) → (pd2 : Δ ⊢pd₀ d′) → connect-pd pd Δ ⊢pd₀ connected-dim pd pd2
connect-pd-pd (Finish pdb) (Finish pdb2) = Finish (connect-pdb-pdb pdb pdb2)
