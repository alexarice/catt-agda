{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Insertion where

open import Catt.Syntax
open import Catt.Syntax.Patterns
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
unsuspend-ctx : (Γ : Ctx n) → .(us : is-unsuspendable-ctx Γ) → Ctx (pred (pred n))
dim-of-unsuspend : (Γ : Ctx n) → .(us : is-unsuspendable-ctx Γ) → ctx-dim (unsuspend-ctx Γ us) ≡ pred (ctx-dim Γ)
is-unsuspendable-ty : (Γ : Ctx n) → (A : Ty Γ d) → Set
unsuspend-ty : (Γ : Ctx n)
             → .(usc : is-unsuspendable-ctx Γ)
             → (A : Ty Γ d)
             → .(ust : is-unsuspendable-ty Γ A)
             → Ty (unsuspend-ctx Γ usc) (pred d)
is-unsuspendable-tm : (Γ : Ctx n) → (t : Tm Γ d) → Set
unsuspend-tm : (Γ : Ctx n)
             → .(usc : is-unsuspendable-ctx Γ)
             → (t : Tm Γ d)
             → .(ust : is-unsuspendable-tm Γ t)
             → Tm (unsuspend-ctx Γ usc) (pred d)
is-unsuspendable-sub : (Γ : Ctx n) → (Δ : Ctx m) → Sub Γ Δ → Set
unsuspend-sub : (Γ : Ctx n)
              → .(usc1 : is-unsuspendable-ctx Γ)
              → (Δ : Ctx m)
              → .(usc2 : is-unsuspendable-ctx Δ)
              → (σ : Sub Γ Δ)
              → .(is-unsuspendable-sub Γ Δ σ)
              → Sub (unsuspend-ctx Γ usc1) (unsuspend-ctx Δ usc2)

is-unsuspendable-ctx ∅ = ⊥
is-unsuspendable-ctx (∅ , A) = ⊥
is-unsuspendable-ctx (∅ , ⋆ , ⋆) = ⊤
is-unsuspendable-ctx (∅ , ⋆ , _ ─⟨ _ ⟩⟶ _) = ⊥
is-unsuspendable-ctx (∅ , _ ─⟨ _ ⟩⟶ _ , _) = ⊥
is-unsuspendable-ctx (Γ , A , B , C) = is-unsuspendable-ctx (Γ , A , B) × is-unsuspendable-ty (Γ , A , B) C

unsuspend-ctx (∅ , ⋆ , ⋆) usc = ∅
unsuspend-ctx (Γ , A , B , C) usc = (unsuspend-ctx (Γ , A , B) (proj₁ usc)) , (unsuspend-ty (Γ , A , B) (proj₁ usc) C (proj₂ usc))

dim-of-unsuspend (∅ , ⋆ , ⋆) us = refl
dim-of-unsuspend (_,_ {n = n} (Γ , A , B) C) us = trans (cong (λ - → - ⊔ pred n) (dim-of-unsuspend (Γ , A , B) (proj₁ us))) (lem (ctx-dim (Γ , A , B)) n)
  where
    lem : (n m : ℕ) → pred n ⊔ pred m ≡ pred (n ⊔ m)
    lem zero m = refl
    lem (suc zero) zero = refl
    lem (suc zero) (suc m) = refl
    lem (suc (suc n)) zero = refl
    lem (suc (suc n)) (suc m) = refl

is-unsuspendable-ty Γ ⋆ = ⊥
is-unsuspendable-ty Γ (s ─⟨ ⋆ ⟩⟶ t) = ⊤ -- s ≃tm getFst {Γ = Γ} × t ≃tm getSnd {Γ = Γ}
is-unsuspendable-ty Γ (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) = is-unsuspendable-ty Γ A × is-unsuspendable-tm Γ s × is-unsuspendable-tm Γ t

unsuspend-ty Γ usc (s ─⟨ ⋆ ⟩⟶ t) usct = ⋆
unsuspend-ty Γ usc (s ─⟨ A@(_ ─⟨ _ ⟩⟶ _) ⟩⟶ t) usct = unsuspend-tm Γ usc s (proj₁ (proj₂ usct)) ─⟨ unsuspend-ty Γ usc A (proj₁ usct) ⟩⟶ unsuspend-tm Γ usc t (proj₂ (proj₂ usct))

is-unsuspendable-tm Γ (Var i) = toℕ i < pred (pred (ctxLength Γ))
is-unsuspendable-tm Γ (Coh {n} Δ A x σ) = is-unsuspendable-ctx Δ × is-unsuspendable-ty Δ A × is-unsuspendable-sub Δ Γ σ × n > 1

unsuspend-var : (Γ : Ctx n) → .(usc : is-unsuspendable-ctx Γ) → (i : Fin (ctxLength Γ)) → .(toℕ i < pred (pred (ctxLength Γ))) → Tm (unsuspend-ctx Γ usc) (lookupDim Γ i)
unsuspend-var (_,_ {n = suc n} (Γ , A , B) C) usc zero p = 0V
unsuspend-var (_,_ {n = suc n} (Γ , A , B) C) usc (suc i) p = liftTerm (unsuspend-var (Γ , A , B) (proj₁ usc) i (≤-pred p))

unsuspend-tm Γ usc (Var i) usct = unsuspend-var Γ usc i usct
unsuspend-tm Γ usc (Coh {suc zero} Δ A x σ) usct = γ (1+n≰n (proj₂ (proj₂ (proj₂ usct))))
  where
    γ : .(⊥) → Tm (unsuspend-ctx Γ _) (pred (suc _))
    γ ()
unsuspend-tm Γ usc (Coh {suc (suc n)} {m = suc m} Δ A x σ) usct = Coh (unsuspend-ctx Δ (proj₁ usct)) (unsuspend-ty Δ (proj₁ usct) A (proj₁ (proj₂ usct))) (≤-trans (≤-reflexive (dim-of-unsuspend Δ (proj₁ usct))) (≤-pred (≤-trans (≤-reflexive (lem Δ)) x))) (unsuspend-sub Δ (proj₁ usct) Γ usc σ (proj₁ (proj₂ (proj₂ usct))))
   where
     lem : (Υ : Ctx (suc n′)) → suc (pred (ctx-dim Υ)) ≡ ctx-dim Υ
     lem (Υ , ⋆) with ctx-dim Υ
     ... | zero = refl
     ... | suc n = refl
     lem (Υ , s ─⟨ A ⟩⟶ t) with ctx-dim Υ
     ... | zero = refl
     ... | suc n = refl

is-unsuspendable-sub .∅ Δ ⟨⟩ = ⊥
is-unsuspendable-sub .(∅ , _) Δ ⟨ ⟨⟩ , t ⟩ = ⊥
is-unsuspendable-sub .(∅ , _ , _) Δ ⟨ ⟨ ⟨⟩ , s ⟩ , t ⟩ = ⊤
is-unsuspendable-sub (_ , A , B , _) Δ ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ = is-unsuspendable-sub (_ , A , B) Δ ⟨ ⟨ σ , u ⟩ , s ⟩ × is-unsuspendable-tm Δ t

unsuspend-sub (∅ , ⋆ , ⋆) usc1 Δ usc2 ⟨ ⟨ ⟨⟩ , t₁ ⟩ , t ⟩ uss = ⟨⟩
unsuspend-sub (_,_ {n = suc n} (_ , _ , _) A) usc1 Δ usc2 ⟨ ⟨ ⟨ σ , u ⟩ , s ⟩ , t ⟩ uss = ⟨ (unsuspend-sub (_ , _ , _) (proj₁ usc1) Δ usc2 ⟨ ⟨ σ , u ⟩ , s ⟩ (proj₁ uss)) , unsuspend-tm Δ usc2 t (proj₂ uss) ⟩

type-has-linear-height : (n : ℕ) → {d : ℕ} → (T : Tree m) → .(lh : has-linear-height n T) → (A : Ty (tree-to-ctx T) d) → Set
type-has-linear-height zero T lh A = {!!}
type-has-linear-height (suc n) T lh A = {!!}

-- unsuspend-ty : (T : Tree m) → .(lh : has-linear-height (suc n) T) → (A : Ty (tree-to-ctx T) (suc d)) → (type-has-linear-height (suc n) T lh A) → Ty (tree-to-ctx (unsuspend-ctx T lh)) d
-- unsuspend-ty T lh A tlh = proj₁ tlh

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
exterior-sub (Join S₁ S₂) (PExt P) bp (Join T Sing) lh A x tlh = sub-from-connect-pdb {Δ = tree-to-ctx S₂}
                                                                   (Restr (susp-pdb (tree-to-pdb zero S₁ tt))) ((connect-pdb-inc-left ? ?) ∘ {!!}) {!!}
exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh = {!!}
-- exterior-sub S (PHere .S) bp T lh A x tlh = sub-from-disc (Coh (tree-to-ctx T) A x (idSub (tree-to-ctx T))) ∘ (idSub≃ (linear-tree-compat S bp))
-- exterior-sub (Join S₁ S₂) (PExt P) bp (Join Sing T) lh A x tlh = sub-from-connect-pdb {Δ = suspCtx (tree-to-ctx S₂)} (tree-to-pdb zero S₁ _) (connect-pdb-inc-left (tree-to-pdb zero S₁ _) (suspCtx (tree-to-ctx (insertion-tree S₂ P T _)))) ((connect-pdb-inc-right (tree-to-pdb zero S₁ _) (suspCtx (tree-to-ctx (insertion-tree S₂ P T _)))) ∘ suspSub (exterior-sub S₂ P bp T lh (proj₁ tlh) {!!} (proj₁ (proj₂ tlh))))
-- exterior-sub (Join S₁ S₂) (PShift P) bp T lh A x tlh = sub-from-connect-pdb {Δ = suspCtx (tree-to-ctx S₂)} (tree-to-pdb zero S₁ _) (connect-pdb-inc-left (tree-to-pdb zero (insertion-tree S₁ P T _) _) (suspCtx (tree-to-ctx S₂)) ∘ exterior-sub S₁ P bp T lh A x tlh) (connect-pdb-inc-right (tree-to-pdb zero (insertion-tree S₁ P T _) _) ?)
