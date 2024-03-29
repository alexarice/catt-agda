module Catt.Ops.Regular where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Typing.Rule
open import Catt.Ops.Pruning
open import Catt.Ops.Insertion

open import Catt.Syntax
open import Catt.Suspension
open import Catt.Suspension.Pasting
open import Catt.Suspension.Support
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Pasting
open import Catt.Pasting.Properties
open import Catt.Tree
open import Catt.Tree.Pasting
open import Catt.Tree.Insertion
open import Catt.Tree.Insertion.Properties
open import Catt.Tree.Insertion.Support
open import Catt.Tree.Insertion.Boundary.Support
open import Catt.Tree.Structured.Support
open import Catt.Tree.Support
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pruning
open import Catt.Dyck.Pruning.Support
open import Catt.Dyck.Pruning.Properties
open import Catt.Dyck.Pasting


data Regular : Op where
  Comp : (Γ : Ctx n)
       → .⦃ _ : Γ ⊢pd ⦄
       → .⦃ NonZero (ctx-dim Γ) ⦄
       → Regular Γ (pd-bd-vs (pred (ctx-dim Γ)) Γ false) (pd-bd-vs (pred (ctx-dim Γ)) Γ true)

  Equiv : (Γ : Ctx n)
        → .⦃ Γ ⊢pd ⦄
        → Regular Γ full full

data Standard : Op where
  Std : (Γ : Ctx n)
      → .⦃ _ : Γ ⊢pd ⦄
      → {xs ys : VarSet n}
      → (d : ℕ)
      → (p : suc d ≥ ctx-dim Γ)
      → (xs ≡ pd-bd-vs d Γ false)
      → (ys ≡ pd-bd-vs d Γ true)
      → Standard Γ xs ys

reg→std : {Γ : Ctx n} → {xs ys : VarSet n} → Regular Γ xs ys → Standard Γ xs ys
reg→std (Comp Γ) = Std Γ (pred (ctx-dim Γ))
                         (suc-pred-≤ (ctx-dim Γ))
                         refl
                         refl
reg→std (Equiv Γ) = Std Γ (ctx-dim Γ)
                          (n≤1+n (ctx-dim Γ))
                          (sym (pd-bd-vs-full (ctx-dim Γ) Γ false ≤-refl))
                          (sym (pd-bd-vs-full (ctx-dim Γ) Γ true ≤-refl))

std→reg : {Γ : Ctx n} → {xs ys : VarSet n} → Standard Γ xs ys → Regular Γ xs ys
std→reg (Std Γ d p q r) with <-cmp (suc d) (ctx-dim Γ)
... | tri< a ¬b ¬c = ⊥-elim (1+n≰n (≤-trans (s≤s p) a))
... | tri≈ ¬a b ¬c = subst₂ (Regular Γ)
                            (sym (trans q (cong (λ - → pd-bd-vs (pred -) Γ false) b)))
                            (sym (trans r (cong (λ - → pd-bd-vs (pred -) Γ true) b)))
                            (Comp Γ ⦃ it ⦄ ⦃ NonZero-subst b it ⦄)
... | tri> ¬a ¬b c = subst₂ (Regular Γ)
                            (sym (trans q (pd-bd-vs-full d Γ false (≤-pred c))))
                            (sym (trans r (pd-bd-vs-full d Γ true (≤-pred c))))
                            (Equiv Γ)

std-susp : SuspOp Standard
std-susp _ _ _ (Std Γ d p q r)
  = Std (susp-ctx Γ)
        ⦃ susp-pd it ⦄
        (suc d)
        (≤-trans (≤-reflexive (susp-ctx-dim Γ ⦃ pd-non-empty it ⦄)) (s≤s p))
        (trans (cong susp-vs q) (susp-pd-bd-compat d Γ false))
        (trans (cong susp-vs r) (susp-pd-bd-compat d Γ true))

reg-susp : SuspOp Regular
reg-susp _ _ _ reg = std→reg (std-susp _ _ _ (reg→std reg))

std-standard : StandardOp Standard
std-standard Γ d p = Std Γ d p refl refl

reg-standard : StandardOp Regular
reg-standard Γ d p = std→reg (std-standard Γ d p)

std-tame : TameOp Standard
std-tame .TameOp.susp-op = std-susp
std-tame .TameOp.standard-op = std-standard

reg-tame : TameOp Regular
reg-tame .TameOp.susp-op = reg-susp
reg-tame .TameOp.standard-op = reg-standard

open import Catt.Typing.Weak Standard

std-pruning : PruningOp Standard
std-pruning dy pk xs ys (Std _ d p q r)
  = Std ⌊ dy // pk ⌋d
        ⦃ dyck-to-pd (dy // pk) ⦄
        d
        dim-lem
        (trans (cong (_[ π pk ]vs) q) (π-boundary-vs pk d false))
        (trans (cong (_[ π pk ]vs) r) (π-boundary-vs pk d true))
  where
    dim-lem : suc d ≥ ctx-dim ⌊ dy // pk ⌋d
    dim-lem = begin
      ctx-dim ⌊ dy // pk ⌋d
        ≡⟨ dyck-dim-to-ctx (dy // pk) ⟩
      dyck-dim (dy // pk)
        ≤⟨ prune-dim pk ⟩
      dyck-dim dy
        ≡˘⟨ dyck-dim-to-ctx dy ⟩
      ctx-dim ⌊ dy ⌋d
        ≤⟨ p ⟩
      suc d ∎
      where
        open ≤-Reasoning

reg-pruning : PruningOp Regular
reg-pruning dy pk xs ys reg = std→reg (std-pruning dy pk xs ys (reg→std reg))

std-ins : InsertionOp Standard
std-ins S P T x xs ys (Std _ d p q r)
  = Std ⌊ S >>[ P ] T ⌋
        ⦃ tree-to-pd (S >>[ P ] T) ⦄
        d
        dim-lem
        (lem xs false q)
        (lem ys true r)
 where
   dim-lem : suc d ≥ ctx-dim ⌊ S >>[ P ] T ⌋
   dim-lem = begin
     ctx-dim ⌊ S >>[ P ] T ⌋
       ≡⟨ tree-dim-ctx-dim (S >>[ P ] T) ⟩
     tree-dim (S >>[ P ] T)
       ≤⟨ insertion-tree-dim S P T x ⟩
     tree-dim S
       ≡˘⟨ tree-dim-ctx-dim S ⟩
     ctx-dim ⌊ S ⌋
       ≤⟨ p ⟩
     suc d ∎
     where
       open ≤-Reasoning

   open ≡-Reasoning

   lem : (zs : VarSet (suc (tree-size S))) → (b : Bool) → zs ≡ pd-bd-vs d ⌊ S ⌋ b
       → zs [ κ S P T ]vl ≡ pd-bd-vs d ⌊ S >>[ P ] T ⌋ ⦃ tree-to-pd (S >>[ P ] T) ⦄ b
   lem zs b pf = begin
     zs [ κ S P T ]vl
       ≡⟨ cong (_[ κ S P T ]vl)
               (trans pf (sym (tree-bd-vs-compat d S b))) ⟩
     tree-bd-vs d S b [ κ S P T ]vl
       ≡⟨ κ-boundary-vs S P T x d b ⟩
     tree-bd-vs d (S >>[ P ] T) b
       ≡⟨ tree-bd-vs-compat d (S >>[ P ] T) b ⟩
     pd-bd-vs d ⌊ S >>[ P ] T ⌋ ⦃ tree-to-pd (S >>[ P ] T) ⦄ b ∎

reg-ins : InsertionOp Regular
reg-ins S P T p xs ys reg = std→reg (std-ins S P T p xs ys (reg→std reg))
