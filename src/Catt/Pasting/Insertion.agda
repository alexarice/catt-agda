{-# OPTIONS --without-K --exact-split #-}

module Catt.Pasting.Insertion where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Catt.Dimension
open import Data.Nat
open import Data.Nat.Properties
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Catt.Pasting.Properties
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Data.Empty
open import Data.Unit using (⊤;tt)
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Product renaming (_,_ to _,,_)
open import Data.Fin using (Fin; toℕ; zero; suc)
open import Relation.Binary.PropositionalEquality

data Path : Tree n → Set where
  PHere : (T : Tree n) → Path T
  PExt : {S : Tree m} {T : Tree n} → Path S → Path (Join S T)
  PShift : {S : Tree m} {T : Tree n} → Path T → Path (Join S T)

path-length : {T : Tree n} → Path T → ℕ
path-length (PHere _) = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P

has-linear-height : ℕ → Tree n → Set
has-linear-height zero T = ⊤
has-linear-height (suc n) Sing = ⊥
has-linear-height (suc n) (Join T Sing) = has-linear-height n T
has-linear-height (suc n) (Join T (Join _ _)) = ⊥

insertion-tree-size :  (S : Tree n) → (P : Path S) → (T : Tree m) → .(has-linear-height (path-length P) T) → ℕ
insertion-tree : (S : Tree n) → (P : Path S) → (T : Tree m) → .(lh : has-linear-height (path-length P) T) → Tree (insertion-tree-size S P T lh)

insertion-tree-size {m = m} S (PHere .S) T lh = m
insertion-tree-size (Join {m = m} S₁ S₂) (PExt P) (Join T Sing) lh = m + suc (suc (insertion-tree-size S₁ P T lh))
insertion-tree-size (Join {n = n} S₁ S₂) (PShift P) T lh = insertion-tree-size S₂ P T lh + suc (suc n)

insertion-tree S (PHere .S) T lh = T
insertion-tree (Join S₁ S₂) (PExt P) (Join T Sing) lh = Join (insertion-tree S₁ P T lh) S₂
insertion-tree (Join S₁ S₂) (PShift P) T lh = Join S₁ (insertion-tree S₂ P T lh)


interior-sub : (S : Tree n) → (P : Path S) → (T : Tree m) → .(lh : has-linear-height (path-length P) T) → Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S P T lh))
interior-sub S (PHere .S) T lh = idSub (tree-to-ctx T)
interior-sub (Join S₁ S₂) (PExt P) (Join T Sing) lh = connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂) ∘ suspSub (interior-sub S₁ P T lh)
interior-sub (Join S₁ S₂) (PShift P) T lh = connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ interior-sub S₂ P T lh

is-branching-path : {T : Tree n} → Path T → Set
is-branching-path (PHere T) = is-linear T
is-branching-path (PExt P) = is-branching-path P
is-branching-path (PShift P) = is-branching-path P

height-of-branching : {T : Tree n} → (P : Path T) → .(is-branching-path P) → ℕ
height-of-branching (PHere T) bp = height-of-linear T bp
height-of-branching (PExt P) bp = suc (height-of-branching P bp)
height-of-branching (PShift P) bp = height-of-branching P bp

is-unsuspendable-ctx : (Γ : Ctx n) → Set
unsuspend-ctx : (Γ : Ctx (suc (suc n))) → (us : is-unsuspendable-ctx Γ) → Ctx n

unsuspend-ctx-compat : (Γ : Ctx (suc (suc n))) → (us : is-unsuspendable-ctx Γ) → suspCtx (unsuspend-ctx Γ us) ≃c Γ
dim-of-unsuspend : (Γ : Ctx (suc (suc n))) → (us : is-unsuspendable-ctx Γ) → suc (ctx-dim (unsuspend-ctx Γ us)) ≡ ctx-dim Γ
is-unsuspendable-ty : (Γ : Ctx n) → (A : Ty Δ d) → suspCtx Γ ≃c Δ → Set
unsuspend-ty : (A : Ty Δ d)
             → (Γ : Ctx n)
             → (p : suspCtx Γ ≃c Δ)
             → (ust : is-unsuspendable-ty Γ A p)
             → Ty Γ (pred d)
unsuspend-ty-compat : (A : Ty Δ d)
                    → (Γ : Ctx n)
                    → (p : suspCtx Γ ≃c Δ)
                    → (ust : is-unsuspendable-ty Γ A p)
                    → suspTy (unsuspend-ty A Γ p ust) ≃ty A
is-unsuspendable-tm : (Γ : Ctx n) → (t : Tm Δ d) → suspCtx Γ ≃c Δ → Set
unsuspend-tm : (t : Tm Δ d)
             → (Γ : Ctx n)
             → (p : suspCtx Γ ≃c Δ)
             → (ust : is-unsuspendable-tm Γ t p)
             → Tm Γ (pred d)
unsuspend-tm-compat : (t : Tm Δ d)
                    → (Γ : Ctx n)
                    → (p : suspCtx Γ ≃c Δ)
                    → (ust : is-unsuspendable-tm Γ t p)
                    → suspTm (unsuspend-tm t Γ p ust) ≃tm t
is-unsuspendable-sub : (Γ : Ctx n) → (Δ : Ctx m) → Sub Γ′ Δ′ → suspCtx Γ ≃c Γ′ → suspCtx Δ ≃c Δ′ → Set
unsuspend-sub : (σ : Sub Γ′ Δ′)
              → (Γ : Ctx n)
              → (Δ : Ctx m)
              → (p : suspCtx Γ ≃c Γ′)
              → (q : suspCtx Δ ≃c Δ′)
              → (is-unsuspendable-sub Γ Δ σ p q)
              → Sub Γ Δ
unsuspend-sub-compat : (σ : Sub Γ′ Δ′)
                     → (Γ : Ctx n)
                     → (Δ : Ctx m)
                     → (p : suspCtx Γ ≃c Γ′)
                     → (q : suspCtx Δ ≃c Δ′)
                     → (uss : is-unsuspendable-sub Γ Δ σ p q)
                     → suspSub (unsuspend-sub σ Γ Δ p q uss) ≃s σ

is-unsuspendable-ctx ∅ = ⊥
is-unsuspendable-ctx (∅ , A) = ⊥
is-unsuspendable-ctx (∅ , ⋆ , ⋆) = ⊤
is-unsuspendable-ctx (∅ , ⋆ , _ ─⟨ _ ⟩⟶ _) = ⊥
is-unsuspendable-ctx (∅ , _ ─⟨ _ ⟩⟶ _ , _) = ⊥
is-unsuspendable-ctx (Γ , A , B , C) = Σ[ p ∈ is-unsuspendable-ctx (Γ , A , B) ] is-unsuspendable-ty (unsuspend-ctx (Γ , A , B) p) C (unsuspend-ctx-compat (Γ , A , B) p)

unsuspend-ctx (∅ , ⋆ , ⋆) usc = ∅
unsuspend-ctx (Γ , A , B , C) usc = (unsuspend-ctx (Γ , A , B) (proj₁ usc)) , unsuspend-ty C (unsuspend-ctx (Γ , A , B) (proj₁ usc)) (unsuspend-ctx-compat (Γ , A , B) _) (proj₂ usc)

unsuspend-ctx-compat (∅ , ⋆ , ⋆) us = refl≃c
unsuspend-ctx-compat (Γ , A , B , C) us = Add≃ (unsuspend-ctx-compat (Γ , A , B) (proj₁ us)) (unsuspend-ty-compat C (unsuspend-ctx (Γ , A , B) _) (unsuspend-ctx-compat (Γ , A , B) _) (proj₂ us))

dim-of-unsuspend (∅ , ⋆ , ⋆) us = refl
dim-of-unsuspend (Γ , A , B , C) us = cong₂ _⊔_ {u = suc (pred (ty-dim C))} (dim-of-unsuspend (Γ , A , B) (proj₁ us)) (suc[pred[n]]≡n (lem C))
  where
    lem : (A : Ty Γ′ n′) → n′ ≢ 0
    lem ⋆ ()
    lem (s ─⟨ A ⟩⟶ t) ()

is-unsuspendable-ty Γ ⋆ p = ⊥
is-unsuspendable-ty Γ (s ─⟨ ⋆ ⟩⟶ t) p = getFst {Γ = Γ} ≃tm s × getSnd {Γ = Γ} ≃tm t
is-unsuspendable-ty Γ (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) p = is-unsuspendable-ty Γ A p × is-unsuspendable-tm Γ s p × is-unsuspendable-tm Γ t p

unsuspend-ty (s ─⟨ ⋆ ⟩⟶ t) Γ p x = ⋆
unsuspend-ty (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) Γ p x = (unsuspend-tm s Γ p (proj₁ (proj₂ x))) ─⟨ unsuspend-ty A Γ p (proj₁ x) ⟩⟶ unsuspend-tm t Γ p (proj₂ (proj₂ x))

unsuspend-ty-compat (s ─⟨ ⋆ ⟩⟶ t) Γ p x = Arr≃ (proj₁ x) Star≃ (proj₂ x)
unsuspend-ty-compat (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) Γ p x = Arr≃ (unsuspend-tm-compat s Γ p (proj₁ (proj₂ x))) (unsuspend-ty-compat A Γ p (proj₁ x)) (unsuspend-tm-compat t Γ p (proj₂ (proj₂ x)))

is-unsuspendable-tm Γ (Var i) p = toℕ i < ctxLength Γ
is-unsuspendable-tm Γ (Coh {n = zero} Δ A x σ) p = ⊥
is-unsuspendable-tm Γ (Coh {n = suc zero} Δ A x σ) p = ⊥
is-unsuspendable-tm Γ (Coh {n = suc (suc n)} Δ A x σ) p = Σ[ q ∈ is-unsuspendable-ctx Δ ] is-unsuspendable-ty (unsuspend-ctx Δ q) A (unsuspend-ctx-compat Δ q) × is-unsuspendable-sub (unsuspend-ctx Δ q) Γ σ (unsuspend-ctx-compat Δ q) p

unsuspend-var : (Γ : Ctx n)
              → {Δ : Ctx m}
              → (i : Fin m)
              → .(toℕ i < n)
              → (suspCtx Γ ≃c Δ)
              → Tm Γ (lookupDim Δ i)
unsuspend-var (Γ , A) zero x (Add≃ p x₁) with ≃ty-preserve-dim x₁
... | refl = 0V
unsuspend-var (Γ , A) (suc i) x (Add≃ p _) = liftTerm (unsuspend-var Γ i (≤-pred x) p)

unsuspend-var-compat : (Γ : Ctx n)
                     → {Δ : Ctx m}
                     → (i : Fin m)
                     → .(p : toℕ i < n)
                     → (q : suspCtx Γ ≃c Δ)
                     → suspTm (unsuspend-var Γ i p q) ≃tm Var {Γ = Δ} i
unsuspend-var-compat (Γ , A) zero p (Add≃ q x) with ≃ty-preserve-dim x
... | refl = Var≃ refl
unsuspend-var-compat (Γ , A) (suc i) p (Add≃ q x) = trans≃tm (reflexive≃tm (suspLiftTm (unsuspend-var Γ i (≤-pred p) q))) (lift-tm-≃ (unsuspend-var-compat Γ i (≤-pred p) q))

unsuspend-tm (Var i) Γ p x = unsuspend-var Γ i x p
unsuspend-tm (Coh {n = suc (suc n)} {m = (suc m)} Δ A x σ) Γ p y = Coh (unsuspend-ctx Δ (proj₁ y)) (unsuspend-ty A (unsuspend-ctx Δ (proj₁ y)) (unsuspend-ctx-compat Δ (proj₁ y)) (proj₁ (proj₂ y))) (≤-pred (≤-trans (≤-reflexive (dim-of-unsuspend Δ (proj₁ y))) x)) (unsuspend-sub σ (unsuspend-ctx Δ (proj₁ y)) Γ (unsuspend-ctx-compat Δ (proj₁ y)) p (proj₂ (proj₂ y)))

unsuspend-tm-compat (Var i) Γ p x = unsuspend-var-compat Γ i x p
unsuspend-tm-compat (Coh {n = suc (suc n)} {m = (suc m)} Δ A x₁ σ) Γ p x = Coh≃ (unsuspend-ctx-compat Δ (proj₁ x)) (unsuspend-ty-compat A (unsuspend-ctx Δ (proj₁ x)) (unsuspend-ctx-compat Δ (proj₁ x)) (proj₁ (proj₂ x))) (unsuspend-sub-compat σ (unsuspend-ctx Δ (proj₁ x)) Γ (unsuspend-ctx-compat Δ (proj₁ x)) p (proj₂ (proj₂ x)))

is-unsuspendable-sub Γ Δ ⟨ ⟨⟩ , t ⟩ p q = ⊥
is-unsuspendable-sub Γ Δ ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ p q = getFst {Γ = Δ} ≃tm s × getSnd {Γ = Δ} ≃tm t
is-unsuspendable-sub ∅ Δ ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ (Add≃ (Add≃ () x₁) x) q
is-unsuspendable-sub (Γ , A) Δ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ (Add≃ p _) q = is-unsuspendable-sub Γ Δ ⟨ ⟨ σ , u ⟩ , s ⟩ p q × is-unsuspendable-tm Δ t q

subst-dim-tm : Tm Γ n → m ≡ n → Tm Γ m
subst-dim-tm t refl = t

subst-dim-tm-≃ : (t : Tm Γ n) → (p : m ≡ n) → subst-dim-tm t p ≃tm t
subst-dim-tm-≃ t refl = refl≃tm

unsuspend-sub ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ ∅ Δ p q x = ⟨⟩
unsuspend-sub ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ (Γ , A) Δ p q x with cong (λ - → pred (pred -)) (≃c-preserve-len p)
... | ()
unsuspend-sub ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ ∅ Δ (Add≃ (Add≃ () x₂) x₁) q x
unsuspend-sub (⟨_,_⟩ {m = m} ⟨ ⟨ σ , u ⟩ , s ⟩ t) (_,_ {n = n} Γ A) Δ (Add≃ p y) q x = ⟨ (unsuspend-sub ⟨ ⟨ σ , u ⟩ , s ⟩ Γ Δ p q (proj₁ x)) , subst-dim-tm (unsuspend-tm t Δ q (proj₂ x)) (≃ty-preserve-dim y) ⟩


unsuspend-sub-compat ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ ∅ Δ p q x = Ext≃ (Ext≃ Null≃ (proj₁ x)) (proj₂ x)
unsuspend-sub-compat ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ (Γ , A) Δ p q x with cong (λ - → pred (pred -)) (≃c-preserve-len p)
... | ()
unsuspend-sub-compat ⟨ ⟨ ⟨ σ , t₂ ⟩ , t₁ ⟩ , t ⟩ ∅ Δ (Add≃ (Add≃ () x₂) x₁) q x
unsuspend-sub-compat (⟨_,_⟩ {m = m} ⟨ ⟨ σ , u ⟩ , s ⟩ t) (_,_ {n = n} Γ A) Δ (Add≃ p x₁) q x = Ext≃ (unsuspend-sub-compat ⟨ ⟨ σ , u ⟩ , s ⟩ Γ Δ p q (proj₁ x)) (trans≃tm (susp-tm-≃ refl≃c (subst-dim-tm-≃ (unsuspend-tm t Δ q (proj₂ x)) (≃ty-preserve-dim x₁))) (unsuspend-tm-compat t Δ q (proj₂ x)))

type-has-linear-height : (n : ℕ) → {d : ℕ} → (T : Tree m) → .(lh : has-linear-height n T) → (A : Ty (tree-to-ctx T) d) → Set
type-has-linear-height zero T lh A = ⊤
type-has-linear-height (suc n) (Join T Sing) lh A = Σ[ p ∈ is-unsuspendable-ty (tree-to-ctx T) A refl≃c ] type-has-linear-height n T lh (unsuspend-ty A (tree-to-ctx T) refl≃c p)

exterior-sub : (S : Tree n)
             → (P : Path S)
             → .(bp : is-branching-path P)
             → (T : Tree m)
             → .(lh : has-linear-height (path-length P) T)
             → (A : Ty (tree-to-ctx T) (suc (height-of-branching P bp)))
             → .(ctx-dim (tree-to-ctx T) ≤ suc (height-of-branching P bp))
             → (type-has-linear-height (path-length P) T lh A)
             → Sub (tree-to-ctx S) (tree-to-ctx (insertion-tree S P T lh))
exterior-sub S (PHere .S) bp T lh A x tlh = sub-from-disc (Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T))) ∘ (idSub≃ (linear-tree-compat S bp))
exterior-sub (Join S₁ S₂) (PExt P) bp (Join T Sing) lh A x tlh =
  sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       ((connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂)) ∘ suspSub (exterior-sub S₁ P bp T lh (unsuspend-ty A (tree-to-ctx T) refl≃c (proj₁ tlh)) (≤-pred (≤-trans (≤-reflexive (sym (ctx-susp-dim (tree-to-ctx T)))) x)) (proj₂ tlh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero (insertion-tree S₁ P T lh) tt))) (tree-to-ctx S₂))
exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh =
  sub-from-connect-pdb (Restr (susp-pdb (tree-to-pdb zero S₁ tt)))
                       (connect-pdb-inc-left (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)))
                       (connect-pdb-inc-right (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) (tree-to-ctx (insertion-tree S₂ P T lh)) ∘ exterior-sub S₂ P bp T lh A x tlh)
