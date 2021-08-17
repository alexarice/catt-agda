{-# OPTIONS --without-K --safe --exact-split #-}

module Catt.Dimension where

open import Catt.Syntax
open import Data.Nat
open import Data.Nat.Properties
open import Induction.WellFounded
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.Construct.Closure.Transitive using () renaming ([_] to [_]p; _∷_ to _∷p_) public
open import Data.Product renaming (_,_ to _,,_)
open import Data.Fin using (Fin;zero;suc)
open import Catt.Tree
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Relation.Binary.PropositionalEquality

ctx-dim : Ctx n → ℕ
ty-dim : Ty n → ℕ
tm-dim : Ctx n → Tm n → ℕ
sub-dim : Ctx m → Sub n m → ℕ

ctx-dim ∅ = 0
ctx-dim (Γ , A) = ctx-dim Γ ⊔ ty-dim A

ty-dim ⋆ = 1
ty-dim (s ─⟨ A ⟩⟶ t) = suc (ty-dim A)

tm-dim Γ (Var i) = suc (ty-dim (Γ ‼ i))
tm-dim Γ (Coh T A σ) = suc (ty-dim A)

sub-dim Δ ⟨⟩ = 0
sub-dim Δ ⟨ σ , t ⟩ = sub-dim Δ σ ⊔ tm-dim Δ t

ctx-is-dim : Ctx n → Set
ty-is-dim : Ctx n → Ty n → Set
tm-is-dim : Ctx n → Tm n → Set
sub-is-dim : Ctx n → Ctx m → Sub n m → Set

ctx-is-dim ∅ = ⊤
ctx-is-dim (Γ , A) = ctx-is-dim Γ × ty-is-dim Γ A

ty-is-dim Γ ⋆ = ⊤
ty-is-dim Γ (s ─⟨ A ⟩⟶ t) = tm-dim Γ s ≡ suc (ty-dim A) × tm-dim Γ t ≡ suc (ty-dim A)

tm-is-dim Γ (Var i) = ⊤
tm-is-dim Γ (Coh T A σ) = ty-is-dim (tree-to-ctx T) A × sub-is-dim (tree-to-ctx T) Γ σ × ctx-dim (tree-to-ctx T) ≤ ty-dim A

sub-is-dim ∅ Δ ⟨⟩ = ⊤
sub-is-dim (Γ , A) Δ ⟨ σ , t ⟩ = sub-is-dim Γ Δ σ × ty-dim A ≡ tm-dim Δ t

-- ctx-dim : .(ctx-is-dim Γ) → ℕ
-- ty-dim : {c : ctx-is-dim Γ} → .(ty-is-dim A) → ℕ
-- tm-dim : {c : ctx-is-dim Γ} → .(tm-is-dim t) → ℕ
-- sub-dim : {c : ctx-is-dim Γ} → {c′ : ctx-is-dim Γ} → .(sub-is-dim σ) → ℕ

-- ctx-is-dim ∅ = ⊤
-- ctx-is-dim (Γ , A) = {!!}
-- ty-is-dim = {!!}
-- tm-is-dim (Var i) = ⊤
-- tm-is-dim (Coh T A σ) = ty-is-dim A × sub-is-dim σ
-- sub-is-dim = {!!}

-- ctx-dim = {!!}
-- ty-dim = {!!}
-- tm-dim = {!!}
-- sub-dim = {!!}

-- data ctx-dim where
--   EmpD : ctx-dim ∅ 0
--   AddD : (c : ctx-dim Γ n) → ty-dim c A m → ctx-dim (Γ , A) (n ⊔ m)

-- data ty-dim where
--   StarD : (c : ctx-dim Γ d) → ty-dim c ⋆ 1
--   ArrD : {c : ctx-dim Γ d} → tm-dim c s (suc (suc n)) → ty-dim c A (suc n) → tm-dim c t (suc (suc n)) → ty-dim c (s ─⟨ A ⟩⟶ t) (suc (suc n))

-- lookupDim : ctx-dim Γ n → (i : Fin (ctxLength Γ)) → ℕ
-- lookupDim (AddD {m = m} c x) zero = m
-- lookupDim (AddD c x) (suc i) = lookupDim c i

-- tree-dim : (T : Tree n) → ℕ

-- tree-is-dim : (T : Tree n) → ctx-dim (tree-to-ctx T) (tree-dim T)

-- data tm-dim where
--   VarD : (c : ctx-dim Γ d) → (i : Fin (ctxLength Γ)) → tm-dim c (Var i) (suc (lookupDim c i))
--   CohD : {T : Tree n} → ty-dim (tree-is-dim T) A d → .(tree-dim T ≤ suc d) → {c : ctx-dim Γ m} → sub-dim (tree-is-dim T) c σ → tm-dim c (Coh T A σ) (suc d)

-- data sub-dim where
--   NullD : (c : ctx-dim Δ d) → sub-dim EmpD c ⟨⟩
--   ExtD : {c : ctx-dim Γ n} {c′ : ctx-dim Δ n′} → sub-dim c c′ σ → (x : ty-dim c A d) → {t : Tm (ctxLength Δ)} → tm-dim c′ t (suc d) → sub-dim (AddD c x) c′ ⟨ σ , t ⟩

-- tree-dim Sing = {!!}
-- tree-dim (Join T T₁) = {!!}
-- tree-is-dim Sing = AddD EmpD (StarD EmpD)
-- tree-is-dim (Join T T₁) = {!!}

-- lift-ty-dim : {c : ctx-dim Γ n} → (x : ty-dim c B d′) → ty-dim c A d → ty-dim (AddD c x) (liftType A) d
-- lift-tm-dim : {c : ctx-dim Γ n} → (x : ty-dim c B d′) → tm-dim c t d → tm-dim (AddD c x) (liftTerm t) d
-- lift-sub-dim : {c : ctx-dim Γ n} {c′ : ctx-dim Δ m} → (x : ty-dim c′ B d′) → sub-dim c c′ σ → sub-dim c (AddD c′ x) (liftSub σ)

-- lift-ty-dim w (StarD x) = (StarD (AddD x w))
-- lift-ty-dim w (ArrD x y z) = ArrD (lift-tm-dim w x) (lift-ty-dim w y) (lift-tm-dim w z)

-- lift-tm-dim w (VarD c i) = VarD (AddD c w) (suc i)
-- lift-tm-dim w (CohD x y z) = CohD x y (lift-sub-dim w z)

-- lift-sub-dim w (NullD x) = NullD (AddD x w)
-- lift-sub-dim w (ExtD x y z) = ExtD (lift-sub-dim w x) y (lift-tm-dim w z)

-- lookupDim-dim : (c : ctx-dim Γ n) → (i : Fin (ctxLength Γ)) → ty-dim c (Γ ‼ i) (lookupDim c i)
-- lookupDim-dim (AddD c x) zero = lift-ty-dim x x
-- lookupDim-dim (AddD c x) (suc i) = lift-ty-dim x (lookupDim-dim c i)

-- sub-preserve-ty-dim : {c : ctx-dim Γ n} → {c′ : ctx-dim Δ m} → (ty-dim c A d) → sub-dim c c′ σ → ty-dim c′ (A [ σ ]ty) d
-- sub-preserve-tm-dim : {c : ctx-dim Γ n} → {c′ : ctx-dim Δ m} → (tm-dim c t d) → sub-dim c c′ σ → tm-dim c′ (t [ σ ]tm) d
-- sub-preserve-sub-dim : {c : ctx-dim Γ n} → {c′ : ctx-dim Δ m} → {x : ctx-dim Υ m′} → (sub-dim x c τ) → sub-dim c c′ σ → sub-dim x c′ (σ ∘ τ)

-- -- sub-dim-to-target-dim : {c : ctx-dim Γ n} → {c′ : ctx-dim Δ m} → sub-dim c c′ σ d → ℕ
-- -- sub-dim-to-target-is-dim : (x : sub-dim Γ Δ σ d) → ctx-dim Δ (sub-dim-to-target-dim x)

-- -- sub-dim-to-target-dim (NullD {d = d} x) = d
-- -- sub-dim-to-target-dim (ExtD x x₁ x₂) = sub-dim-to-target-dim x

-- -- sub-dim-to-target-is-dim (NullD x) = x
-- -- sub-dim-to-target-is-dim (ExtD x x₁ x₂) = sub-dim-to-target-is-dim x

-- -- sub-dim-to-source-dim : sub-dim Γ Δ σ d → ℕ
-- -- sub-dim-to-source-is-dim : (x : sub-dim Γ Δ σ d) → ctx-dim Δ (sub-dim-to-target-dim x)

-- -- sub-dim-to-source-dim (NullD {d = d} x) = d
-- -- sub-dim-to-source-dim (ExtD x x₁ x₂) = sub-dim-to-target-dim x

-- -- sub-dim-to-source-is-dim (NullD x) = x
-- -- sub-dim-to-source-is-dim (ExtD x x₁ x₂) = sub-dim-to-target-is-dim x

-- sub-preserve-ty-dim (StarD x) w = StarD {!!}
-- sub-preserve-ty-dim (ArrD x y z) w = ArrD (sub-preserve-tm-dim x w) (sub-preserve-ty-dim y w) (sub-preserve-tm-dim z w)

-- sub-preserve-tm-dim (VarD c i) w = {!!}
--   -- where
--   --   lem : (i : Fin (ctxLength Γ)) → sub-dim Γ Δ σ d′ → tm-dim Δ (Var i [ σ ]tm) (suc (lookupDim c i))
--   --   lem zero (AddD c x₁) (ExtD x y z) = {!!}
--   --   lem (suc i) c (ExtD x y z) = {!!}
-- sub-preserve-tm-dim (CohD x x₁ x₂) w = {!!}

-- sub-preserve-sub-dim x w = {!!}

-- data DimSyntax : Set where
--   Context : (Γ : Ctx n) → .(ctx-dim Γ d) → DimSyntax
--   Type : (A : Ty n) → {c : ctx-dim Γ d′} → (ty-dim c A d) → DimSyntax
--   Term : (t : Tm n) → {c : ctx-dim Γ d′} → (tm-dim c t d) → DimSyntax
--   Substitution : (σ : Sub n m) → {c : ctx-dim Γ n′} → {c′ : ctx-dim Δ m′} → (sub-dim c c′ σ) → DimSyntax

-- get-sub-dim : {c : ctx-dim Γ n′} → {c′ : ctx-dim Δ m′} → sub-dim c c′ σ → ℕ
-- get-sub-dim = ?

-- syntax-dim : DimSyntax → ℕ
-- syntax-dim (Context {d = d} Γ x) = d
-- syntax-dim (Type {d = d} A x) = d
-- syntax-dim (Term {d = d} t x) = d
-- syntax-dim (Substitution {n′ = n′} σ x) = n′

-- -- syntax-ctx-length : Syntax → ℕ
-- -- syntax-ctx-length (Context {n} Γ) = n
-- -- syntax-ctx-length (Type {n} A) = n
-- -- syntax-ctx-length (Term {n} t) = n
-- -- syntax-ctx-length (Substitution {Δ = Δ} σ) = ctxLength Δ

-- -- syntax-ctx-dim : Syntax → ℕ
-- -- syntax-ctx-dim (Context Γ) = ctx-dim Γ
-- -- syntax-ctx-dim (Type {Γ = Γ} A) = ctx-dim Γ
-- -- syntax-ctx-dim (Term {Γ = Γ} t) = ctx-dim Γ
-- -- syntax-ctx-dim (Substitution {Δ = Δ} σ) = ctx-dim Δ

-- -- syntax-ctx : (x : Syntax) → Ctx (syntax-ctx-length x)
-- -- syntax-ctx (Context Γ) = Γ
-- -- syntax-ctx (Type {Γ = Γ} A) = Γ
-- -- syntax-ctx (Term {Γ = Γ} t) = Γ
-- -- syntax-ctx (Substitution {Δ = Δ} σ) = Δ

-- data _≺_ : DimSyntax → DimSyntax → Set where
--   dim : {x : DimSyntax} → {y : DimSyntax} → .(p : syntax-dim x < syntax-dim y) → x ≺ y
--   ctx1 : {x : ctx-dim Γ d} → {y : ty-dim x A d′} → Context Γ x ≺ Context (Γ , A) (AddD x y)
--   ctx2 : {x : ctx-dim Γ d} → {y : ty-dim x A d′} → Type A y ≺ Context (Γ , A) (AddD x y)
--   ty1 : {c : ctx-dim Γ d′} → {x : tm-dim c s (suc (suc d))} → {y : ty-dim c A (suc d)} → {z : tm-dim c t (suc (suc d))} → Term s x ≺ Type (s ─⟨ A ⟩⟶ t) (ArrD x y z)
--   ty2 : {c : ctx-dim Γ d′} → {x : tm-dim c s (suc (suc d))} → {y : ty-dim c A (suc d)} → {z : tm-dim c t (suc (suc d))} → Type A y ≺ Type (s ─⟨ A ⟩⟶ t) (ArrD x y z)
--   ty3 : {c : ctx-dim Γ d′} → {x : tm-dim c s (suc (suc d))} → {y : ty-dim c A (suc d)} → {z : tm-dim c t (suc (suc d))} → Term t z ≺ Type (s ─⟨ A ⟩⟶ t) (ArrD x y z)
--   tm1 : {c : ctx-dim Γ d′} → {x : ty-dim (tree-is-dim T) A d} → {y : sub-dim (tree-is-dim T) c σ} → .{p : tree-dim T ≤ suc d} → Type A x ≺ Term (Coh T A σ) (CohD x p y)
--   tm2 : {c : ctx-dim Γ d′} → {x : ty-dim (tree-is-dim T) A d} → {y : sub-dim (tree-is-dim T) c σ d′} → .{p : d′ ≤ suc d} →  Substitution σ {!y!} ≺ Term (Coh T A σ) (CohD x p y)
--   sub1 : {c : ctx-dim Γ d′} → {c′ : ctx-dim Δ m} → {x : sub-dim c c′ σ d} → {y : ty-dim c A d} → {z : tm-dim c′ t (suc d)} → Substitution σ x ≺ Substitution ⟨ σ , t ⟩ {!!} -- (ExtD x y z)
--   sub2 : {c : ctx-dim Γ d′} → {c′ : ctx-dim Δ m} → {x : sub-dim c c′ σ d} → {y : ty-dim c A d} → {z : tm-dim c′ t (suc d)} → Term t z ≺ Substitution ⟨ σ , t ⟩ {!!} --(ExtD x y z)

-- not-possible : (A : Set) → (x : ℕ) → .(x < 0) → A
-- not-possible A x ()

-- -- sub-dim-lem : (σ : Sub Γ Δ) → sub-dim σ ≤ suc (ctx-dim Γ)
-- -- sub-dim-lem ⟨⟩ = z≤n
-- -- sub-dim-lem ⟨ σ , t ⟩ = ⊔-monoˡ-≤ (tm-dim t) (sub-dim-lem σ)

-- ctx-dim-lem : (ctx-dim ∅ d) → d ≤ 0
-- ctx-dim-lem EmpD = ≤-refl

-- -- wf : WellFounded _≺_
-- -- wf x = acc (access (syntax-dim x) x ≤-refl)
-- --   where
-- --     access-ctx : (n : ℕ) → (Γ : Ctx m) → .(x : ctx-dim Γ d) → .(d ≤ n) → (y : DimSyntax) → y ≺ (Context Γ x) → Acc _≺_ y
-- --     access-ty : (n : ℕ) → (A : Ty m) → .(x : ty-dim Γ A d) → .(d ≤ n) → (y : DimSyntax) → y ≺ (Type A x) → Acc _≺_ y
-- --     access-tm : (n : ℕ) → (t : Tm m) → .(x : tm-dim Γ t d) → .(d ≤ n) → (y : DimSyntax) → y ≺ (Term t x) → Acc _≺_ y
-- --     access-sub : (n : ℕ) → (σ : Sub m m′) → .(x : sub-dim Γ Δ σ d) → .(d ≤ n) → (y : DimSyntax) → y ≺ (Substitution σ x) → Acc _≺_ y
-- --     access : (n : ℕ) → (x : DimSyntax) → .(syntax-dim x ≤ n) → (y : DimSyntax) → y ≺ x → Acc _≺_ y

-- --     access-ctx zero ∅ x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
-- --     access-ctx zero (Γ , A) x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
-- --     access-ctx zero (Γ , A) x le (Context Γ y) ctx1 = acc (access-ctx zero Γ y (m⊔n≤o⇒m≤o _ _ le))
-- --     access-ctx zero (Γ , A) x le (Type A y) ctx2 = acc (access-ty zero A y (m⊔n≤o⇒n≤o _ _ le))
-- --     access-ctx (suc n) ∅ x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p (ctx-dim-lem x))
-- --     access-ctx (suc n) (Γ , A) x le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
-- --     access-ctx (suc n) (Γ , A) x le (Context Γ y) ctx1 = acc (access-ctx (suc n) Γ y (m⊔n≤o⇒m≤o _ _ le))
-- --     access-ctx (suc n) (Γ , A) x le (Type A y) ctx2 = acc (access-ty (suc n) A y (m⊔n≤o⇒n≤o _ _ le))

-- --     access-ty zero ⋆ x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
-- --     access-ty zero (s ─⟨ A ⟩⟶ t) x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
-- --     access-ty (suc n) ⋆ x le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
-- --     access-ty (suc n) (s ─⟨ A ⟩⟶ t) x le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
-- --     access-ty (suc n) (s ─⟨ A ⟩⟶ t) x le (Term s y) ty1 = acc (access-tm (suc n) s y le)
-- --     access-ty (suc n) (s ─⟨ A ⟩⟶ t) x le (Type A y) ty2 = acc (access-ty n A y (≤-pred le))
-- --     access-ty (suc n) (s ─⟨ A ⟩⟶ t) x le (Term t y) ty3 = acc (access-tm (suc n) t y le)

-- --     access-tm zero (Var i) x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
-- --     access-tm zero (Coh T A σ) x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
-- --     access-tm zero (Coh T A σ) x le (Substitution σ y) (tm2 {p = p}) = acc (access-sub zero σ y (≤-trans p le))
-- --     access-tm (suc n) (Var i) x le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
-- --     access-tm (suc n) (Coh T A σ) x le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
-- --     access-tm (suc n) (Coh T A σ) x le (Type A y) tm1 = acc (access-ty n A y (≤-pred le))
-- --     access-tm (suc n) (Coh T A σ) x le (Substitution σ y) (tm2 {p = p}) = acc (access-sub (suc n) σ y (≤-trans p le))

-- --     access-sub zero ⟨⟩ x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
-- --     access-sub zero ⟨ σ , t ⟩ x le y (dim p) = not-possible (Acc _≺_ y) (syntax-dim y) (<-transˡ p le)
-- --     access-sub zero ⟨ σ , t ⟩ x le (Substitution σ y) sub1 = acc (access-sub zero σ y (m⊔n≤o⇒m≤o _ _ le))
-- --     access-sub zero ⟨ σ , t ⟩ x le (Term t y) sub2 = acc (access-tm zero t y (m⊔n≤o⇒n≤o _ (suc _) le))
-- --     access-sub (suc n) ⟨⟩ x le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
-- --     access-sub (suc n) ⟨ σ , t ⟩ x le y (dim p) = acc (access n y (≤-pred (≤-trans p le)))
-- --     access-sub (suc n) ⟨ σ , t ⟩ x le (Substitution σ y) sub1 = acc (access-sub (suc n) σ y (m⊔n≤o⇒m≤o _ _ le))
-- --     access-sub (suc n) ⟨ σ , t ⟩ x le (Term t y) sub2 = acc (access-tm (suc n) t y (m⊔n≤o⇒n≤o _ _ le))

-- --     access n (Context Γ x) le = access-ctx n Γ x le
-- --     access n (Type A x) le = access-ty n A x le
-- --     access n (Term t x) le = access-tm n t x le
-- --     access n (Substitution σ x) le = access-sub n σ x le

-- -- _≺⁺_ = TransClosure _≺_

-- -- wf⁺ : WellFounded _≺⁺_
-- -- wf⁺ = wellFounded _≺_ wf

-- -- open All wf⁺
