module Catt.Dyck.Pruning.FromInsertion where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Globular
open import Catt.Globular.Properties
open import Catt.Suspension
open import Catt.Wedge
open import Catt.Wedge.Properties
open import Catt.Tree
open import Catt.Tree.Pasting
open import Catt.Tree.Properties
open import Catt.Tree.Insertion
open import Catt.Tree.Path
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.FromTree

extend-tree-path : (n : ℕ) → (T : Tree m) → .⦃ _ : n-extendable n T ⦄ → Path (extend-tree n T)
extend-tree-path zero Sing = PExt PHere
extend-tree-path zero (Join S T) = PShift (extend-tree-path zero T)
extend-tree-path (suc n) (Susp S) = PExt (extend-tree-path n S)
extend-tree-path (suc n) (Join S T@(Join _ _)) = PShift (extend-tree-path (suc n) T)

instance
  extend-tree-path-not-here : .⦃ _ : n-extendable n T ⦄ → not-here (extend-tree-path n T)
  extend-tree-path-not-here {n = zero} {T = Sing} = tt
  extend-tree-path-not-here {n = zero} {T = Join S T} = tt
  extend-tree-path-not-here {n = suc n} {T = Susp S} = tt
  extend-tree-path-not-here {n = suc n} {T = Join S (Join T₁ T₂)} = tt


  extend-tree-path-maximal : .⦃ _ : n-extendable n T ⦄ → is-maximal (extend-tree-path n T)
  extend-tree-path-maximal {n = zero} {T = Sing} = inst
  extend-tree-path-maximal {n = zero} {T = Join S T} = build
  extend-tree-path-maximal {n = suc n} {T = Susp S} = inst
  extend-tree-path-maximal {n = suc n} {T = Join S (Join T₁ T₂)} = build

extend-path : (n : ℕ) → (T : Tree m) → .⦃ _ : n-extendable n T ⦄
            → (P : Path T)
            → Path (extend-tree n T)
extend-path zero Sing P = PHere
extend-path zero (Join S T) PHere = PHere
extend-path zero (Join S T) (PExt P) = PExt P
extend-path zero (Join S T) (PShift P) = PShift (extend-path zero T P)
extend-path (suc n) (Susp S) PHere = PHere
extend-path (suc n) (Susp S) (PExt P) = PExt (extend-path n S P)
extend-path (suc n) (Susp S) (PShift P) = PShift PHere
extend-path (suc n) (Join S T@(Join _ _)) PHere = PHere
extend-path (suc n) (Join S T@(Join _ _)) (PExt P) = PExt P
extend-path (suc n) (Join S T@(Join _ _)) (PShift P) = PShift (extend-path (suc n) T P)

peak-to-path : {dy : Dyck (suc n) d} → (pk : Peak dy) → Path (dyck-to-tree dy)
peak-to-path (⇕pk {d = d} dy) = extend-tree-path d (dyck-to-tree dy) ⦃ dyck-to-tree-is-n-extendable dy ⦄
peak-to-path (⇑pk {d = d} {dy = dy} pk)
  = extend-path d (dyck-to-tree dy) ⦃ dyck-to-tree-is-n-extendable dy ⦄ (peak-to-path pk)
peak-to-path (⇓pk pk) = peak-to-path pk

extend-tree-branch : (n : ℕ) → (T : Tree m) → .⦃ _ : n-extendable n T ⦄ → Branch (extend-tree n T) n
extend-tree-branch zero Sing = BHere
extend-tree-branch zero (Join S T) = BShift (extend-tree-branch zero T)
extend-tree-branch (suc n) (Susp S) = BExt (extend-tree-branch n S)
extend-tree-branch (suc n) (Join S T@(Join _ _)) = BShift (extend-tree-branch (suc n) T)

extend-leaves-branch : (n : ℕ) → (T : Tree m) → .⦃ _ : n-extendable n T ⦄ → Branch T l → Set
extend-leaves-branch zero T B = ⊤
extend-leaves-branch (suc n) (Join S T) (BShift B) = extend-leaves-branch (suc n) T ⦃ lem T B ⦄ B
  where
    lem : (T : Tree m) → (Branch T l) → ⦃ _ : n-extendable (suc n) (Join S T) ⦄ → n-extendable (suc n) T
    lem (Join T T₁) B = it
extend-leaves-branch (suc n) (Susp S) BHere = ⊥
extend-leaves-branch (suc n) (Join S (Join _ _)) BHere = ⊤
extend-leaves-branch (suc n) (Susp S) (BExt B) = extend-leaves-branch n S B
extend-leaves-branch (suc n) (Join S (Join _ _)) (BExt B) = ⊤

extend-leaves-branch-pred : (n : ℕ) → (T : Tree m)
                          → .⦃ _ : n-extendable (suc n) T ⦄
                          → (B : Branch T l)
                          → extend-leaves-branch (suc n) T B
                          → extend-leaves-branch n T ⦃ pred-n-extendable n T ⦄ B
extend-leaves-branch-pred zero T B x = tt
extend-leaves-branch-pred (suc n) (Join S T) (BShift B) x
  = extend-leaves-branch-pred (suc n) T ⦃ _ ⦄ B x
extend-leaves-branch-pred (suc n) (Join S (Join T T₁)) BHere x = tt
extend-leaves-branch-pred (suc n) (Susp S) (BExt B) x
  = extend-leaves-branch-pred n S B x
extend-leaves-branch-pred (suc n) (Join S (Join T T₁)) (BExt B) x = tt

extend-tree-branch-leaves-branch : (n : ℕ)
                                 → (T : Tree m)
                                 → .⦃ _ : n-extendable n T ⦄
                                 → extend-leaves-branch
                                     n (extend-tree n T)
                                     ⦃ pred-n-extendable n (extend-tree n T)
                                       ⦃ extended-tree-is-more-extendable n T ⦄ ⦄
                                     (extend-tree-branch n T)
extend-tree-branch-leaves-branch zero T = tt
extend-tree-branch-leaves-branch (suc n) (Susp S)
  = extend-tree-branch-leaves-branch n S
extend-tree-branch-leaves-branch (suc n) (Join S T@(Join _ _))
  = extend-tree-branch-leaves-branch (suc n) T

extend-branch : (n : ℕ)
              → (T : Tree m)
              → .⦃ _ : n-extendable n T ⦄
              → (B : Branch T l)
              → .(extend-leaves-branch n T B)
              → Branch (extend-tree n T) l
extend-branch zero (Join S₁ S₂) BHere x = BHere
extend-branch zero (Join S₁ S₂) (BExt B) x = BExt B
extend-branch zero (Join S₁ S₂) (BShift B) x = BShift (extend-branch zero S₂ B x)
extend-branch (suc n) (Susp S) (BExt B) x = BExt (extend-branch n S B x)
extend-branch (suc n) (Join S T@(Join _ _)) BHere x = BHere
extend-branch (suc n) (Join S T@(Join _ _)) (BExt B) x = BExt B
extend-branch (suc n) (Join S T@(Join _ _)) (BShift B) x = BShift (extend-branch (suc n) T B x)

extend-tree-leaves-branch : (n : ℕ)
                          → (T : Tree m)
                          → .⦃ _ : n-extendable n T ⦄
                          → (B : Branch T l)
                          → (x : extend-leaves-branch n T B)
                          → extend-leaves-branch (suc n) (extend-tree n T)
                                                 ⦃ extended-tree-is-more-extendable n T ⦄
                                                 (extend-branch n T B x)
extend-tree-leaves-branch zero (Susp S) BHere x = tt
extend-tree-leaves-branch zero (Susp S) (BExt B) x = tt
extend-tree-leaves-branch zero (Join S (Join _ _)) BHere x = tt
extend-tree-leaves-branch zero (Join S (Join _ _)) (BExt B) x = tt
extend-tree-leaves-branch zero (Join S T@(Join _ _)) (BShift B) x = extend-tree-leaves-branch zero T B tt
extend-tree-leaves-branch (suc n) (Susp S) (BExt B) x = extend-tree-leaves-branch n S B x
extend-tree-leaves-branch (suc n) (Join S (Join T₁ T₂)) (BShift B) x = extend-tree-leaves-branch (suc n) (Join T₁ T₂) B x
extend-tree-leaves-branch (suc n) (Join S (Susp T₁)) BHere x = tt
extend-tree-leaves-branch (suc n) (Join S (Join T₁ (Join T₂ T₃))) BHere x = tt
extend-tree-leaves-branch (suc n) (Join S (Susp T₁)) (BExt B) x = tt
extend-tree-leaves-branch (suc n) (Join S (Join T₁ (Join T₂ T₃))) (BExt B) x = tt

peak-to-branch-height : {dy : Dyck (suc n) d} → (pk : Peak dy) → ℕ
peak-to-branch-height (⇕pk {d = d} dy) = d
peak-to-branch-height (⇑pk pk) = peak-to-branch-height pk
peak-to-branch-height (⇓pk pk) = peak-to-branch-height pk

peak-to-branch : {dy : Dyck (suc n) d} → (pk : Peak dy) → Branch (dyck-to-tree dy) (peak-to-branch-height pk)
peak-to-branch-lem : {dy : Dyck (suc n) d}
                   → (pk : Peak dy)
                   → extend-leaves-branch d (dyck-to-tree dy)
                                          ⦃ dyck-to-tree-is-n-extendable dy ⦄
                                          (peak-to-branch pk)

peak-to-branch (⇕pk {d = d} dy) = extend-tree-branch d (dyck-to-tree dy) ⦃ _ ⦄
peak-to-branch (⇑pk {d = d} {dy = dy} pk)
  = extend-branch d (dyck-to-tree dy)
                    ⦃ dyck-to-tree-is-n-extendable dy ⦄
                    (peak-to-branch pk)
                    (peak-to-branch-lem pk)
peak-to-branch (⇓pk pk) = peak-to-branch pk

peak-to-branch-lem (⇕pk {d = d} dy) = extend-tree-branch-leaves-branch d (dyck-to-tree dy) ⦃ dyck-to-tree-is-n-extendable dy ⦄
peak-to-branch-lem (⇑pk {d = d} {dy = dy} pk)
  = extend-tree-leaves-branch d (dyck-to-tree dy)
                              ⦃ dyck-to-tree-is-n-extendable dy ⦄
                              (peak-to-branch pk)
                              (peak-to-branch-lem pk)
peak-to-branch-lem (⇓pk {n} {d} {dy = dy} pk)
  = extend-leaves-branch-pred d (dyck-to-tree dy)
                              ⦃ dyck-to-tree-is-n-extendable dy ⦄
                              (peak-to-branch pk)
                              (peak-to-branch-lem pk)

peak-to-branch-height-prop : {dy : Dyck (suc n) d}
                           → (pk : Peak dy)
                           → peak-to-branch-height pk
                             ≡
                             pred (tm-height ⌊ dy ⌋d (peak-term pk))
peak-to-branch-height-prop (⇕pk {d = d} dy) = begin
  d
    ≡˘⟨ dyck-type-dim dy ⟩
  ty-dim (dyck-type dy)
    ≡˘⟨ wk-ty-dim (dyck-type dy) ⟩
  ty-dim (wk-ty (dyck-type dy))
    ≡˘⟨ wk-ty-dim (wk-ty (dyck-type dy)) ⟩
  ty-dim (wk-ty (wk-ty (dyck-type dy))) ∎
  where
    open ≡-Reasoning
peak-to-branch-height-prop (⇑pk pk) = {!!}
peak-to-branch-height-prop (⇓pk pk) = {!!}
