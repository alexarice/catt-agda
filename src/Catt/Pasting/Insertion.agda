{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Insertion where

open import Catt.Syntax
open import Data.Nat
open import Data.Nat.Properties
open import Catt.Pasting
open import Catt.Pasting.Tree
open import Catt.Pasting.Properties
open import Catt.Discs
open import Catt.Syntax.SyntacticEquality
open import Catt.Suspension
open import Data.Empty
open import Data.Unit using (⊤)
open import Catt.Connection
open import Catt.Connection.Properties
open import Data.Product

data Path : Tree n → Set where
  PHere : (T : Tree n) → Path T
  PExt : {S : Tree m} {T : Tree n} → Path T → Path (Join S T)
  PShift : {S : Tree m} {T : Tree n} → Path S → Path (Join S T)

path-length : {T : Tree n} → Path T → ℕ
path-length (PHere _) = 0
path-length (PExt P) = suc (path-length P)
path-length (PShift P) = path-length P

has-linear-height : ℕ → Tree n → Set
has-linear-height zero T = ⊤
has-linear-height (suc n) Sing = ⊥
has-linear-height (suc n) (Join Sing T) = has-linear-height n T
has-linear-height (suc n) (Join (Join T T₂) T₁) = ⊥

insertion-tree-size :  (S : Tree n) → (P : Path S) → (T : Tree m) → .(has-linear-height (path-length P) T) → ℕ
insertion-tree : (S : Tree n) → (P : Path S) → (T : Tree m) → .(lh : has-linear-height (path-length P) T) → Tree (insertion-tree-size S P T lh)

insertion-tree-size {m = m} S (PHere .S) T lh = m
insertion-tree-size (Join {n} S₁ S₂) (PExt P) (Join Sing T) lh = suc (suc (insertion-tree-size S₂ P T lh + n))
insertion-tree-size (Join {m = m} S₁ S₂) (PShift P) T lh = suc (suc (m + insertion-tree-size S₁ P T lh))

insertion-tree S (PHere .S) T lh = T
insertion-tree (Join S₁ S₂) (PExt P) (Join Sing T) lh = Join S₁ (insertion-tree S₂ P T lh)
insertion-tree (Join S₁ S₂) (PShift P) T lh = Join (insertion-tree S₁ P T lh) S₂

interior-sub : (S : Tree n) → (P : Path S) → (T : Tree m) → .(lh : has-linear-height (path-length P) T) → Sub (tree-to-ctx T) (tree-to-ctx (insertion-tree S P T lh))
interior-sub S (PHere .S) T lh = idSub (tree-to-ctx T)
interior-sub (Join S₁ S₂) (PExt P) (Join Sing T) lh = connect-pdb-inc-right (tree-to-pdb zero S₁ _) (suspCtx (tree-to-ctx (insertion-tree S₂ P T _))) ∘ suspSub (interior-sub S₂ P T lh) ∘ idSub≃ (connect-pdb-left-unit (suspCtx (tree-to-ctx T)))
interior-sub (Join S₁ S₂) (PShift P) T lh = connect-pdb-inc-left (tree-to-pdb zero (insertion-tree S₁ P T _) _) (suspCtx (tree-to-ctx S₂)) ∘ interior-sub S₁ P T lh

is-branching-path : {T : Tree n} → Path T → Set
is-branching-path (PHere T) = is-linear T
is-branching-path (PExt P) = is-branching-path P
is-branching-path (PShift P) = is-branching-path P

height-of-branching : {T : Tree n} → (P : Path T) → .(is-branching-path P) → ℕ
height-of-branching (PHere T) bp = height-of-linear T bp
height-of-branching (PExt P) bp = suc (height-of-branching P bp)
height-of-branching (PShift P) bp = height-of-branching P bp

unsuspend-ctx-len : (T : Tree m) → .(has-linear-height (suc n) T) → ℕ
unsuspend-ctx-len (Join {m = m} Sing T) lh = m

unsuspend-ctx : (T : Tree m) → .(lh : has-linear-height (suc n) T) → Tree (unsuspend-ctx-len T lh)
unsuspend-ctx (Join Sing T) lh = T

unsuspend-ctx-lin-height : (T : Tree m) → (lh : has-linear-height (suc n) T) → (has-linear-height n (unsuspend-ctx T lh))
unsuspend-ctx-lin-height (Join Sing T) lh = lh

-- is-unsuspendable-ty : (T : Ctx m) → (A : Ty (suspCtx Γ) n) → Set
-- is-unsuspendable-tm : (Γ : Ctx m) → (A )

-- is-unsuspendable-ty Γ ⋆ = ⊥
-- is-unsuspendable-ty Γ (s ─⟨ ⋆ ⟩⟶ t) = (s ≃tm getFst {Γ = Γ}) × (t ≃tm getSnd {Γ = Γ})
-- is-unsuspendable-ty Γ (s ─⟨ s′ ─⟨ A ⟩⟶ t′ ⟩⟶ t) = is-unsuspendable-ty Γ (s′ ─⟨ A ⟩⟶ t′)

-- unsuspend-ty : (Γ : Ctx m) → (A : Ty (suspCtx Γ) (suc n)) → .(is-unsuspendable-ty Γ A) → Ty Γ n
-- unsuspend-ty Γ (s ─⟨ ⋆ ⟩⟶ t) iu = ⋆
-- unsuspend-ty Γ (s ─⟨ s₁ ─⟨ A ⟩⟶ t₁ ⟩⟶ t) iu = {!!}

type-has-linear-height : (n : ℕ) → {d : ℕ} → (T : Tree m) → .(lh : has-linear-height n T) → (A : Ty (tree-to-ctx T) d) → Set
type-has-linear-height zero T lh A = ⊤
type-has-linear-height (suc n) {suc d} T lh A = Σ[ B ∈ Ty (tree-to-ctx (unsuspend-ctx T lh)) d ] type-has-linear-height n (unsuspend-ctx T lh) (unsuspend-ctx-lin-height T lh) B × suspTy B ≃ty A

unsuspend-ty : (T : Tree m) → .(lh : has-linear-height (suc n) T) → (A : Ty (tree-to-ctx T) (suc d)) → (type-has-linear-height (suc n) T lh A) → Ty (tree-to-ctx (unsuspend-ctx T lh)) d
unsuspend-ty T lh A tlh = proj₁ tlh

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
exterior-sub (Join S₁ S₂) (PExt P) bp (Join Sing T) lh A x tlh = sub-from-connect-pdb {Δ = suspCtx (tree-to-ctx S₂)} (tree-to-pdb zero S₁ _) (connect-pdb-inc-left (tree-to-pdb zero S₁ _) (suspCtx (tree-to-ctx (insertion-tree S₂ P T _)))) ((connect-pdb-inc-right (tree-to-pdb zero S₁ _) (suspCtx (tree-to-ctx (insertion-tree S₂ P T _)))) ∘ suspSub (exterior-sub S₂ P bp T lh (proj₁ tlh) {!!} (proj₁ (proj₂ tlh))))
exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh = sub-from-connect-pdb {Δ = suspCtx (tree-to-ctx S₂)} (tree-to-pdb zero S₁ _) (connect-pdb-inc-left (tree-to-pdb zero (insertion-tree S₁ P T _) _) (suspCtx (tree-to-ctx S₂)) ∘ exterior-sub S₁ P bp T lh A x tlh) (connect-pdb-inc-right (tree-to-pdb zero (insertion-tree S₁ P T _) _) (suspCtx (tree-to-ctx S₂)))
