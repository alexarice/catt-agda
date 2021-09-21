{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.PartialSubstitution.Properties where

open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.PartialSubstitution
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Nullary
open import Data.Empty
open import Catt.Tree
open import Catt.Tree.Properties
open import Relation.Binary.PropositionalEquality
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Variables
open import Data.Product renaming (_,_ to _,,_)


⋆-comp-is-comp : (σ : Sub l o) → (τ : Sub m l) → σ ∘⟨ ⋆ ⟩ τ ≃s σ ∘ τ
⋆-sub-is-sub-tm : (t : Tm l) → (σ : Sub l o) → t [ σ ]⟨ ⋆ ⟩tm ≃tm t [ σ ]tm

⋆-comp-is-comp σ ⟨⟩ = refl≃s
⋆-comp-is-comp σ ⟨ τ , t ⟩ = Ext≃ (⋆-comp-is-comp σ τ) (⋆-sub-is-sub-tm t σ)

⋆-sub-is-sub-tm (Var zero) ⟨ σ , t ⟩ = refl≃tm
⋆-sub-is-sub-tm (Var (suc i)) ⟨ σ , t ⟩ = ⋆-sub-is-sub-tm (Var i) σ
⋆-sub-is-sub-tm (Coh {m = zero} S A τ) σ = ⊥-elim (n-to-0-sub-impossible τ)
⋆-sub-is-sub-tm (Coh {m = (suc m)} S A τ) σ = refl≃tm

unrestrict-comp : (A : Ty o (suc d)) → (σ : Sub l o) → (τ : Sub m l) → unrestrict (σ ∘⟨ A ⟩ τ) A ≃s unrestrict σ A ∘⟨ ty-base A ⟩ suspSub τ
unrestrict-comp-tm : (A : Ty o (suc d)) → (t : Tm l) → (σ : Sub l o) → t [ σ ]⟨ A ⟩tm ≃tm suspTm t [ unrestrict σ A ]⟨ ty-base A ⟩tm
unrestrict-fst : (A : Ty o (suc d)) → (σ : Sub l o) → ty-src A ≃tm getFst [ unrestrict σ A ]⟨ ty-base A ⟩tm
unrestrict-snd : (A : Ty o (suc d)) → (σ : Sub l o) → ty-tgt A ≃tm getSnd [ unrestrict σ A ]⟨ ty-base A ⟩tm

unrestrict-comp (s ─⟨ A ⟩⟶ t) σ ⟨⟩ = Ext≃ (Ext≃ refl≃s (unrestrict-fst (s ─⟨ A ⟩⟶ t) σ)) (unrestrict-snd (s ─⟨ A ⟩⟶ t) σ)
unrestrict-comp (s ─⟨ A ⟩⟶ t) σ ⟨ τ , u ⟩ = Ext≃ (unrestrict-comp (s ─⟨ A ⟩⟶ t) σ τ) (unrestrict-comp-tm (s ─⟨ A ⟩⟶ t) u σ)

unrestrict-comp-tm A (Var zero) ⟨ σ , t ⟩ = refl≃tm
unrestrict-comp-tm A (Var (suc i)) ⟨ σ , t ⟩ = unrestrict-comp-tm A (Var i) σ
unrestrict-comp-tm A (Coh {m = zero} S B τ) σ = ⊥-elim (n-to-0-sub-impossible τ)
unrestrict-comp-tm A (Coh {m = suc m} S B τ) σ = refl≃tm

unrestrict-fst (s ─⟨ A ⟩⟶ t) ⟨⟩ = refl≃tm
unrestrict-fst (s ─⟨ A ⟩⟶ t) ⟨ σ , u ⟩ = unrestrict-fst (s ─⟨ A ⟩⟶ t) σ

unrestrict-snd (s ─⟨ A ⟩⟶ t) ⟨⟩ = refl≃tm
unrestrict-snd (s ─⟨ A ⟩⟶ t) ⟨ σ , u ⟩ = unrestrict-snd (s ─⟨ A ⟩⟶ t) σ

unrestrict-restrict : (τ : Sub (suc (suc n)) m) → (A : Ty m d) → unrestrict (restrict τ) ((getFst [ τ ]⟨ A ⟩tm) ─⟨ A ⟩⟶ (getSnd [ τ ]⟨ A ⟩tm)) ≃s τ
unrestrict-restrict ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ A = refl≃s
unrestrict-restrict ⟨ τ@(⟨ ⟨ _ , _ ⟩ , _ ⟩) , t ⟩ A = Ext≃ (unrestrict-restrict τ A) refl≃tm

unrestrict-≃ : σ ≃s τ → A ≃ty B → unrestrict σ A ≃s unrestrict τ B
unrestrict-≃ (Null≃ x) (Arr≃ a b c) = Ext≃ (Ext≃ (Null≃ x) a) c
unrestrict-≃ (Ext≃ q x) p = Ext≃ (unrestrict-≃ q p) x

full-unrestrict-≃ : A ≃ty B → σ ≃s τ → full-unrestrict σ A ≃s full-unrestrict τ B
full-unrestrict-≃ (Star≃ x) q = q
full-unrestrict-≃ (Arr≃ a b c) q = full-unrestrict-≃ b (unrestrict-≃ q (Arr≃ a b c))

full-unrestrict-comp : (A : Ty o d) → (σ : Sub (suc l) o) → (τ : Sub (suc m) (suc l)) → full-unrestrict (σ ∘⟨ A ⟩ τ) A ≃s full-unrestrict σ A ∘ n-fold-suspSub (ty-dim A) τ
full-unrestrict-comp ⋆ σ τ = ⋆-comp-is-comp σ τ
full-unrestrict-comp (s ─⟨ A ⟩⟶ t) σ τ = trans≃s (full-unrestrict-≃ {A = A} refl≃ty (unrestrict-comp (s ─⟨ A ⟩⟶ t) σ τ)) (full-unrestrict-comp A (unrestrict σ (s ─⟨ A ⟩⟶ t)) (suspSub τ))

n-fold-suspSub-≃ : d ≡ d′ → σ ≃s τ → n-fold-suspSub d σ ≃s n-fold-suspSub d′ τ
n-fold-suspSub-≃ {zero} {zero} p q = q
n-fold-suspSub-≃ {suc d} {suc d′} p q = n-fold-suspSub-≃ {d} {d′} (cong pred p) (susp-sub-≃ q)

n-fold-suspTree-≃ : d ≡ d′ → S ≃ T → n-fold-suspTree d S ≃ n-fold-suspTree d′ T
n-fold-suspTree-≃ {zero} {zero} p q = q
n-fold-suspTree-≃ {suc d} {suc d′} p q = n-fold-suspTree-≃ {d} {d′} (cong pred p) (Join≃ q Sing≃)

n-fold-suspTy-≃ : d ≡ d′ → A ≃ty B → n-fold-suspTy d A ≃ty n-fold-suspTy d′ B
n-fold-suspTy-≃ {zero} {zero} p q = q
n-fold-suspTy-≃ {suc d} {suc d′} p q = n-fold-suspTy-≃ {d} {d′} (cong pred p) (susp-ty-≃ q)

n-fold-suspSub-functorial : (d : ℕ) → (σ : Sub (suc n) (suc m)) → (τ : Sub (suc l) (suc n)) → n-fold-suspSub d (σ ∘ τ) ≃s n-fold-suspSub d σ ∘ n-fold-suspSub d τ
n-fold-suspSub-functorial zero σ τ = refl≃s
n-fold-suspSub-functorial (suc d) σ τ = trans≃s (n-fold-suspSub-≃ {d} refl (susp-functorial σ τ)) (n-fold-suspSub-functorial d (suspSub σ) (suspSub τ))

∘⟨⟩-assoc : (A : Ty o d) → (σ : Sub l o) → (τ : Sub m l) → (μ : Sub n m) → σ ∘⟨ A ⟩ (τ ∘ μ) ≃s σ ∘⟨ A ⟩ τ ∘⟨ A ⟩ μ
⟨⟩-assoc-tm : (A : Ty o d) → (t : Tm m) → (σ : Sub l o) → (τ : Sub m l)  → (t [ τ ]tm) [ σ ]⟨ A ⟩tm ≃tm (t [ σ ∘⟨ A ⟩ τ ]⟨ A ⟩tm)

∘⟨⟩-assoc A σ τ ⟨⟩ = refl≃s
∘⟨⟩-assoc A σ τ ⟨ μ , t ⟩ = Ext≃ (∘⟨⟩-assoc A σ τ μ) (⟨⟩-assoc-tm A t σ τ)

⟨⟩-assoc-tm A (Var zero) σ ⟨ τ , t ⟩ = refl≃tm
⟨⟩-assoc-tm A (Var (suc i)) σ ⟨ τ , t ⟩ = ⟨⟩-assoc-tm A (Var i) σ τ
⟨⟩-assoc-tm {m = zero} A (Coh S B μ) σ τ = ⊥-elim (n-to-0-sub-impossible μ)
⟨⟩-assoc-tm {m = suc m} {l = zero} A (Coh S B μ) σ τ = ⊥-elim (n-to-0-sub-impossible τ)
⟨⟩-assoc-tm {m = suc m} {l = suc l} A (Coh S B μ) σ τ =  Coh≃ refl≃ refl≃ty (begin
  < full-unrestrict σ A ∘ n-fold-suspSub (ty-dim A) (τ ∘ μ) >s
    ≈⟨ sub-action-≃-sub (n-fold-suspSub-functorial (ty-dim A) τ μ) refl≃s ⟩
  < full-unrestrict σ A ∘ (n-fold-suspSub (ty-dim A) τ ∘ n-fold-suspSub (ty-dim A) μ) >s
    ≈˘⟨ ∘-assoc (full-unrestrict σ A) (n-fold-suspSub (ty-dim A) τ) (n-fold-suspSub (ty-dim A) μ) ⟩
  < full-unrestrict σ A ∘ n-fold-suspSub (ty-dim A) τ ∘ n-fold-suspSub (ty-dim A) μ  >s
    ≈˘⟨ sub-action-≃-sub refl≃s (full-unrestrict-comp A σ τ) ⟩
  < full-unrestrict (σ ∘⟨ A ⟩ τ) A ∘ n-fold-suspSub (ty-dim A) μ >s ∎)
  where
    open Reasoning sub-setoid

sub-⟨⟩-action-≃-sub : σ ≃s σ′ → A ≃ty B → τ ≃s τ′ → σ ∘⟨ A ⟩ τ ≃s σ′ ∘⟨ B ⟩ τ′
sub-⟨⟩-action-≃-tm : t ≃tm t′ → σ ≃s σ′ → A ≃ty B → t [ σ ]⟨ A ⟩tm ≃tm (t′ [ σ′ ]⟨ B ⟩tm)

sub-⟨⟩-action-≃-sub p q (Null≃ x) = Null≃ (≃s-to-codomain-≡ p)
sub-⟨⟩-action-≃-sub p q (Ext≃ r x) = Ext≃ (sub-⟨⟩-action-≃-sub p q r) (sub-⟨⟩-action-≃-tm x p q)

sub-⟨⟩-action-≃-tm (Var≃ x y) q r = lem _ _ y q r
  where
    lem : (i : Fin n) → (j : Fin n′) → toℕ i ≡ toℕ j → σ ≃s τ → A ≃ty B → Var i [ σ ]⟨ A ⟩tm ≃tm Var j [ τ ]⟨ B ⟩tm
    lem zero zero p (Ext≃ q x) r = x
    lem (suc i) (suc j) p (Ext≃ q x) r = lem i j (cong pred p) q r
sub-⟨⟩-action-≃-tm (Coh≃ {m = zero} {m′ = zero} {σ = σ} a b c) q r = ⊥-elim (n-to-0-sub-impossible σ)
sub-⟨⟩-action-≃-tm (Coh≃ {m = suc m} {m′ = suc m′} a b c) q r = Coh≃ (n-fold-suspTree-≃ (≃ty-preserve-height r) a) (n-fold-suspTy-≃ (≃ty-preserve-height r) b) (sub-action-≃-sub (n-fold-suspSub-≃ (≃ty-preserve-height r) c) (full-unrestrict-≃ r q))

⟨⟩-var-to-var : (σ : Sub n m) → (A : Ty m d) → (τ : Sub l n) → .⦃ varToVar τ ⦄ → σ ∘⟨ A ⟩ τ ≃s σ ∘ τ
⟨⟩-is-var : (t : Tm n) → .⦃ isVar t ⦄ → (σ : Sub n m) → (A : Ty m d) → t [ σ ]⟨ A ⟩tm ≃tm t [ σ ]tm

⟨⟩-var-to-var σ A ⟨⟩ = refl≃s
⟨⟩-var-to-var σ A ⟨ τ , t ⟩ ⦃ v ⦄ = Ext≃ (⟨⟩-var-to-var σ A τ ⦃ proj₁ v ⦄) (⟨⟩-is-var t ⦃ proj₂ v ⦄ σ A)

⟨⟩-is-var (Var zero) ⟨ σ , t ⟩ A = refl≃tm
⟨⟩-is-var (Var (suc i)) ⟨ σ , t ⟩ A = ⟨⟩-is-var (Var i) σ A
