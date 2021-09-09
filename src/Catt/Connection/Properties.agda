{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Connection.Properties where

open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Connection
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles
open import Catt.Variables
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; T; if_then_else_; not)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary

connect-≃ : Γ ≃c Γ′ → t ≃tm t′ → Δ ≃c Δ′ → connect Γ t Δ ≃c connect Γ′ t′ Δ′
connect-inc-right-≃ : {t : Tm (suc n)} → {t′ : Tm (suc n′)} → n ≡ n′ → t ≃tm t′ → m ≡ m′ → connect-inc-right t m ≃s connect-inc-right t′ m′

connect-≃ p q (Add≃ Emp≃ r) = p
connect-≃ p q (Add≃ (Add≃ r s) t) = Add≃ (connect-≃ p q (Add≃ r s)) (sub-action-≃-ty t (connect-inc-right-≃ (cong pred (≃c-preserve-length p)) q (cong pred (≃c-preserve-length (Add≃ r s)))))

connect-inc-right-≃ {m = zero} refl q refl = Ext≃ (Null≃ refl) q
connect-inc-right-≃ {m = suc m} refl q refl = Ext≃ (lift-sub-≃ (connect-inc-right-≃ refl q refl)) (Var≃ refl refl)
-- Ext≃ (Null≃ p) q
--  Ext≃ (lift-sub-≃ (sub-action-≃-ty t (connect-inc-right-≃ p q (Add≃ r s))) (connect-inc-right-≃ p q (Add≃ r s))) (Var≃ (connect-≃ p q (Add≃ (Add≃ r s) t)) refl)

-- connect-is-non-empty : ⦃ _ : NonZero′ (ctxLength Γ) ⦄ ⦃ _ : NonZero′ (ctxLength Δ) ⦄ → NonZero′ (ctxLength (connect Γ t Δ))
-- connect-is-non-empty {Δ = ∅ , A} = it
-- connect-is-non-empty {Δ = Δ , A , B} = it

-- connect left unit

-- connect-left-unit : (Γ : Ctx) → .⦃ _ : NonZero′ (ctxLength Γ) ⦄ → connect (∅ , ⋆) 0V Γ ≃c Γ
-- connect-inc-right-left-unit : (Γ : Ctx) → .⦃ _ : NonZero′ (ctxLength Γ) ⦄ → connect-inc-right (∅ , ⋆) 0V Γ ≃s idSub Γ

-- connect-left-unit (∅ , A) = Add≃ Emp≃ {!!}
-- connect-left-unit (Γ , A , B) = Add≃ (connect-left-unit (Γ , A)) (trans≃ty (sub-action-≃-ty refl≃ty (connect-inc-right-left-unit (Γ , A))) (id-on-ty B))

-- connect-inc-right-left-unit (∅ , A) = {!!}
-- connect-inc-right-left-unit (Γ , A , B) = Ext≃ (lift-sub-≃ (connect-inc-right-left-unit (Γ , A))) (Var≃ refl)

-- connect-pdb-left-unit : (Γ : Ctx) → .⦃ _ : NonZero′ (ctxLength Γ) ⦄ → connect-pdb Base Γ ≃c Γ
-- connect-pdb-left-unit Γ = connect-left-unit Γ

sub-from-connect-inc-left : (σ : Sub (suc n) l) → (t : Tm (suc n)) → (τ : Sub (suc m) l) → sub-from-connect σ t τ ∘ connect-inc-left t m ≃s σ
sub-from-connect-inc-left σ t τ@(⟨ ⟨⟩ , s ⟩) = id-right-unit (sub-from-connect σ t τ)
sub-from-connect-inc-left σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = trans≃s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-left t _)) (sub-from-connect-inc-left σ t ⟨ τ , s ⟩)

sub-from-connect-pdb-inc-left : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → sub-from-connect-pdb pdb σ τ ∘ connect-pdb-inc-left pdb m ≃s σ
sub-from-connect-pdb-inc-left pdb σ τ = sub-from-connect-inc-left σ (getFocusTerm pdb) τ

sub-from-connect-pd-inc-left : (pd : Γ ⊢pd₀ d) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → sub-from-connect-pd pd σ τ ∘ connect-pd-inc-left pd m ≃s σ
sub-from-connect-pd-inc-left (Finish pdb) σ τ = sub-from-connect-pdb-inc-left pdb σ τ

sub-from-connect-inc-right : (σ : Sub (suc n) l) → (t : Tm (suc n)) → (τ : Sub (suc m) l) → (t [ σ ]tm ≃tm Var (fromℕ _) [ τ ]tm) → sub-from-connect σ t τ ∘ connect-inc-right t m ≃s τ
sub-from-connect-inc-right σ t ⟨ ⟨⟩ , s ⟩ p = Ext≃ (Null≃ refl) p
sub-from-connect-inc-right σ t ⟨ ⟨ τ , s ⟩ , u ⟩ p = Ext≃ (trans≃s (lift-sub-comp-lem-sub (sub-from-connect σ t ⟨ τ , s ⟩) (connect-inc-right t _)) (sub-from-connect-inc-right σ t ⟨ τ , s ⟩ p)) refl≃tm

sub-from-connect-pdb-inc-right : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → (getFocusTerm pdb [ σ ]tm ≃tm (Var (fromℕ _) [ τ ]tm)) → sub-from-connect-pdb pdb σ τ ∘ connect-pdb-inc-right pdb m ≃s τ
sub-from-connect-pdb-inc-right pdb σ τ p = sub-from-connect-inc-right σ (getFocusTerm pdb) τ p

sub-from-connect-pd-inc-right : (pd : Γ ⊢pd₀ d) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → (pd-focus-tm pd [ σ ]tm ≃tm (Var (fromℕ _) [ τ ]tm)) → sub-from-connect-pd pd σ τ ∘ connect-pd-inc-right pd m ≃s τ
sub-from-connect-pd-inc-right (Finish pdb) σ τ p = sub-from-connect-pdb-inc-right pdb σ τ p

connect-inc-fst-var : (t : Tm (suc n)) → (m : ℕ) → t [ connect-inc-left t m ]tm ≃tm Var (fromℕ _) [ connect-inc-right t m ]tm
connect-inc-fst-var t zero = id-on-tm t
connect-inc-fst-var t (suc m) = begin
  < t [ connect-inc-left t (suc m) ]tm >tm ≈⟨ apply-lifted-sub-tm-≃ t (connect-inc-left t m) ⟩
  < liftTerm (t [ connect-inc-left t m ]tm) >tm ≈⟨ lift-tm-≃ (connect-inc-fst-var t m) ⟩
  < liftTerm (Var (fromℕ _) [ connect-inc-right t m ]tm) >tm ≈˘⟨ apply-lifted-sub-tm-≃ (Var (fromℕ _)) (connect-inc-right t m) ⟩
  < Var (fromℕ (suc _)) [ connect-inc-right t (suc m) ]tm >tm ∎
  where
    open Reasoning tm-setoid

connect-pdb-inc-fst-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → (getFocusTerm pdb) [ connect-pdb-inc-left pdb m ]tm ≃tm Var (fromℕ _) [ connect-pdb-inc-right pdb m ]tm
connect-pdb-inc-fst-var pdb = connect-inc-fst-var (getFocusTerm pdb)

connect-pd-inc-fst-var : (pd : Γ ⊢pd₀ d) → (m : ℕ)
  → pd-focus-tm pd [ connect-pd-inc-left pd m ]tm ≃tm Var (fromℕ _) [ connect-pd-inc-right pd m ]tm
connect-pd-inc-fst-var (Finish pdb) = connect-pdb-inc-fst-var pdb

connect-inc-left-fst-var : (t : Tm (suc n)) → (m : ℕ) → Var (fromℕ _) [ connect-inc-left t m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
connect-inc-left-fst-var t zero = id-on-tm (Var (fromℕ _))
connect-inc-left-fst-var t (suc m) = trans≃tm (apply-lifted-sub-tm-≃ (Var (fromℕ _)) (connect-inc-left t m)) (lift-tm-≃ (connect-inc-left-fst-var t m))

connect-pdb-inc-left-fst-var : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → Var (fromℕ _) [ connect-pdb-inc-left pdb m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
connect-pdb-inc-left-fst-var pdb = connect-inc-left-fst-var (getFocusTerm pdb)

connect-pd-inc-left-fst-var : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (m : ℕ) → Var (fromℕ _) [ connect-pd-inc-left pd m ]tm ≃tm Var {suc (m + n)} (fromℕ _)
connect-pd-inc-left-fst-var (Finish pdb) = connect-pdb-inc-left-fst-var pdb

sub-from-connect-fst-var : (σ : Sub (suc n) l) → (t : Tm (suc n)) → (τ : Sub (suc m) l) → Var (fromℕ _) [ sub-from-connect σ t τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-fst-var σ t ⟨ ⟨⟩ , s ⟩ = refl≃tm
sub-from-connect-fst-var σ t ⟨ ⟨ τ , s ⟩ , u ⟩ = sub-from-connect-fst-var σ t ⟨ τ , s ⟩

sub-from-connect-pdb-fst-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) → Var (fromℕ _) [ sub-from-connect-pdb pdb σ τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-pdb-fst-var pdb σ τ = sub-from-connect-fst-var σ (getFocusTerm pdb) τ

sub-from-connect-pd-fst-var : (pd : Γ ⊢pd₀ d) → (σ : Sub (ctxLength Γ) l) → (τ : Sub (suc m) l) →
  Var (fromℕ _) [ sub-from-connect-pd pd σ τ ]tm ≃tm Var (fromℕ _) [ σ ]tm
sub-from-connect-pd-fst-var (Finish pdb) σ τ = sub-from-connect-pdb-fst-var pdb σ τ

connect-var-split : (t : Tm (suc n)) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-var-split t zero i = inj₁ i
connect-var-split t (suc m) zero = inj₂ zero
connect-var-split t (suc m) (suc i) with connect-var-split t m i
... | inj₁ j = inj₁ j
... | inj₂ j = inj₂ (suc j)

connect-var-split-compat : (t : Tm (suc n)) → (m : ℕ) → VarSplitCompat (connect-inc-left t m) (connect-inc-right t m) (connect-var-split t m)
connect-var-split-compat t zero i = id-on-tm (Var i)
connect-var-split-compat t (suc m) zero = refl≃tm
connect-var-split-compat t (suc m) (suc i) with connect-var-split t m i | connect-var-split-compat t m i
... | inj₁ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-left t m)) (lift-tm-≃ p)
... | inj₂ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-right t m)) (lift-tm-≃ p)

connect-pdb-var-split : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-pdb-var-split pdb = connect-var-split (getFocusTerm pdb)

connect-pdb-var-split-compat : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → VarSplitCompat (connect-pdb-inc-left pdb m) (connect-pdb-inc-right pdb m) (connect-pdb-var-split pdb m)
connect-pdb-var-split-compat pdb = connect-var-split-compat (getFocusTerm pdb)

connect-pd-var-split : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-pd-var-split (Finish pdb) Δ = connect-pdb-var-split pdb Δ

connect-pd-var-split-compat : (pd : Γ ⊢pd₀ d) → (m : ℕ) → VarSplitCompat (connect-pd-inc-left pd m) (connect-pd-inc-right pd m) (connect-pd-var-split pd m)
connect-pd-var-split-compat (Finish pdb) = connect-pdb-var-split-compat pdb

connect-var-split-right : (t : Tm (suc n)) → .⦃ isVar t ⦄ → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-var-split-right t zero i with toℕ (getVarFin t) ≡ᵇ toℕ i
... | true = inj₂ zero
... | false = inj₁ i
connect-var-split-right t (suc m) zero = inj₂ zero
connect-var-split-right t (suc m) (suc i) with connect-var-split-right t m i
... | inj₁ j = inj₁ j
... | inj₂ j = inj₂ (suc j)

-- record Reveal_·_is-bool_ {A : Set}
--                     (f : (x : A) → Bool) (x : A) (y : Bool):
--                     Set where
--   constructor [_]
--   field eq : if y then T (f x) else T (not (f x))

-- inspect-bool : ∀ {A : Set} (f : (x : A) → Bool) (x : A) → Reveal f · x is-bool f x
-- inspect-bool f x with f x | inspect f x
-- ... | false | [ eq ] = [ subst (λ - → T (not -)) (sym eq) tt ]
-- ... | true | [ eq ] = [ subst T (sym eq) tt ]

connect-var-split-right-compat : (t : Tm (suc n)) → .⦃ _ : isVar t ⦄ → (m : ℕ) → VarSplitCompat (connect-inc-left t m) (connect-inc-right t m) (connect-var-split-right t m)
connect-var-split-right-compat t zero i with toℕ (getVarFin t) ≡ᵇ toℕ i | inspect (λ i → toℕ (getVarFin t) ≡ᵇ toℕ i) i
... | false | p = id-on-tm (Var i)
... | true | [ eq ] = trans≃tm (getVarFinProp t) (Var≃ refl (≡ᵇ⇒≡ (toℕ (getVarFin t)) (toℕ i) (subst T (sym eq) tt)))
connect-var-split-right-compat t (suc m) zero = refl≃tm
connect-var-split-right-compat t (suc m) (suc i) with connect-var-split-right t m i | connect-var-split-right-compat t m i
... | inj₁ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-left t m)) (lift-tm-≃ p)
... | inj₂ j | p = trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-right t m)) (lift-tm-≃ p)

connect-pdb-var-split-right : {Γ : Ctx (suc n)} → (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-pdb-var-split-right pdb = connect-var-split-right (getFocusTerm pdb) ⦃ focus-term-is-var pdb ⦄

connect-pdb-var-split-right-compat : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → VarSplitCompat (connect-pdb-inc-left pdb m) (connect-pdb-inc-right pdb m) (connect-pdb-var-split-right pdb m)
connect-pdb-var-split-right-compat pdb = connect-var-split-right-compat (getFocusTerm pdb) ⦃ focus-term-is-var pdb ⦄

connect-pd-var-split-right : {Γ : Ctx (suc n)} → (pd : Γ ⊢pd₀ d) → (m : ℕ) → VarSplit (suc (m + n)) (suc n) (suc m)
connect-pd-var-split-right (Finish pdb) = connect-pdb-var-split-right pdb

connect-pd-var-split-right-compat : (pd : Γ ⊢pd₀ d) → (m : ℕ) → VarSplitCompat (connect-pd-inc-left pd m) (connect-pd-inc-right pd m) (connect-pd-var-split-right pd m)
connect-pd-var-split-right-compat (Finish pdb) = connect-pdb-var-split-right-compat pdb

-- connect-var-split : (Γ : Ctx (suc n)) → (t : Tm Γ 2) → (Δ : Ctx (suc m)) → VarSplit (connect Γ t Δ) (connect-inc-left Γ t Δ) (connect-inc-right Γ t Δ)
-- connect-var-split Γ t (∅ , A) i = inj₁ (i ,, id-on-tm (Var i))
-- connect-var-split Γ t (Δ , A , B) zero = inj₂ (zero ,, Var≃ refl)
-- connect-var-split Γ t (Δ , A , B) (suc i) with connect-var-split Γ t (Δ , A) i
-- ... | inj₁ (j ,, p) = inj₁ (j ,, trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-left Γ t (Δ , A))) (lift-tm-≃ p))
-- ... | inj₂ (j ,, p) = inj₂ (suc j ,, trans≃tm (apply-lifted-sub-tm-≃ (Var j) (connect-inc-right Γ t (Δ , A))) (lift-tm-≃ p))

-- connect-pdb-var-split : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → VarSplit (connect-pdb pdb Δ) (connect-pdb-inc-left pdb Δ) (connect-pdb-inc-right pdb Δ)
-- connect-pdb-var-split pdb Δ = connect-var-split _ (getFocusTerm pdb) Δ

connect-inc-left-var-to-var : (t : Tm (suc n)) → (m : ℕ) → varToVar (connect-inc-left t m)
connect-inc-left-var-to-var {n = n} t zero = id-is-var-to-var (suc n)
connect-inc-left-var-to-var t (suc m) = liftSub-preserve-var-to-var (connect-inc-left t m) ⦃ connect-inc-left-var-to-var t m ⦄

connect-pdb-inc-left-var-to-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → varToVar (connect-pdb-inc-left pdb m)
connect-pdb-inc-left-var-to-var pdb = connect-inc-left-var-to-var (getFocusTerm pdb)

connect-pd-inc-left-var-to-var : (pd : Γ ⊢pd₀ d) → (m : ℕ) → varToVar (connect-pd-inc-left pd m)
connect-pd-inc-left-var-to-var (Finish pdb) = connect-pdb-inc-left-var-to-var pdb

connect-inc-right-var-to-var : (t : Tm (suc n)) → (m : ℕ) → .⦃ isVar t ⦄ → varToVar (connect-inc-right t m)
connect-inc-right-var-to-var t zero = extend-var-to-var ⟨⟩ t
connect-inc-right-var-to-var t (suc m) = liftSub-preserve-var-to-var (connect-inc-right t m) ⦃ connect-inc-right-var-to-var t m ⦄

connect-pdb-inc-right-var-to-var : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (m : ℕ) → varToVar (connect-pdb-inc-right pdb m)
connect-pdb-inc-right-var-to-var pdb m = connect-inc-right-var-to-var (getFocusTerm pdb) m ⦃ focus-term-is-var pdb ⦄

connect-pd-inc-right-var-to-var : (pd : Γ ⊢pd₀ d) → (m : ℕ) → varToVar (connect-pd-inc-right pd m)
connect-pd-inc-right-var-to-var (Finish pdb) = connect-pdb-inc-right-var-to-var pdb

{-
ty-dim-≥-1 : Ty Γ d → d ≥ 1
ty-dim-≥-1 ⋆ = ≤-refl
ty-dim-≥-1 (s ─⟨ A ⟩⟶ t) = s≤s z≤n

non-empty-context-dim-≥-1 : (Γ : Ctx (suc n)) → ctx-dim Γ ≥ 1
non-empty-context-dim-≥-1 (Γ , A) = m≤n⇒m≤o⊔n (ctx-dim Γ) (ty-dim-≥-1 A)

connect-ctx-dim : (Γ : Ctx (suc n)) → (t : Tm Γ 2) → (Δ : Ctx (suc m)) → ctx-dim (connect Γ t Δ) ≡ ctx-dim Γ ⊔ ctx-dim Δ
connect-ctx-dim Γ t (∅ , ⋆) = sym (m≥n⇒m⊔n≡m (non-empty-context-dim-≥-1 Γ))
connect-ctx-dim Γ t (∅ , s ─⟨ A ⟩⟶ t₁) = ⊥-elim (no-term-in-empty-context s)
connect-ctx-dim Γ t (Δ , A , B) = begin
  ctx-dim (connect Γ t (Δ , A , B)) ≡⟨⟩
  ctx-dim (connect Γ t (Δ , A)) ⊔
      ty-dim (B [ connect-inc-right Γ t (Δ , A) ]ty) ≡⟨ cong (_⊔ ty-dim B) (connect-ctx-dim Γ t (Δ , A)) ⟩
  (ctx-dim Γ ⊔ ctx-dim (Δ , A)) ⊔ ty-dim B ≡⟨ ⊔-assoc (ctx-dim Γ) (ctx-dim (Δ , A)) (ty-dim B) ⟩
  ctx-dim Γ ⊔ (ctx-dim (Δ , A) ⊔ ty-dim B) ≡⟨⟩
  ctx-dim Γ ⊔ ctx-dim (Δ , A , B) ∎
  where
    open ≡-Reasoning

connect-pdb-ctx-dim : (pdb : Γ ⊢pd[ submax ][ 0 ]) → (Δ : Ctx (suc m)) → ctx-dim (connect-pdb pdb Δ) ≡ ctx-dim Γ ⊔ ctx-dim Δ
connect-pdb-ctx-dim pdb Δ = connect-ctx-dim _ (getFocusTerm pdb) Δ
-}
