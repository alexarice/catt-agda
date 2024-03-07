module Catt.Dyck.Support where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Syntax.Bundles
open import Catt.Dyck
open import Catt.Dyck.Properties
open import Catt.Dyck.Pasting
open import Catt.Support
open import Catt.Support.Properties
open import Catt.Globular
open import Catt.Globular.Properties

dyck-bd-supp : (d : ℕ) → (dy : Dyck n m) → (b : Bool) → VarSet (suc (n * 2))
dyck-bd-supp d dy b = pdb-bd-supp d ⌊ dy ⌋d ⦃ dyck-to-pdb dy ⦄ b

dyck-term-fixed : (d m : ℕ) → (dy : Dyck n (m + d)) → Tm (suc (n * 2))
dyck-term-fixed d zero dy = dyck-term dy
dyck-term-fixed d (suc m) dy = ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy)))

private
  lem : (m : ℕ) → (dy : Dyck n d) → truncate′ m (lift-ty (lift-ty (dyck-pre-type dy))) ≃ty lift-ty (lift-ty (truncate′ m (dyck-pre-type dy)))
  lem m dy = begin
    < truncate′ m (lift-ty (lift-ty (dyck-pre-type dy))) >ty
      ≈⟨ truncate′-lift m (lift-ty (dyck-pre-type dy)) ⟩
    < lift-ty (truncate′ m (lift-ty (dyck-pre-type dy))) >ty
      ≈⟨ lift-ty-≃ (truncate′-lift m (dyck-pre-type dy)) ⟩
    < lift-ty (lift-ty (truncate′ m (dyck-pre-type dy))) >ty ∎
    where
      open Reasoning ty-setoid


dyck-bd-drop : (m : ℕ) → (dy : Dyck n (m + d)) → drop (dyck-bd-supp d dy true) ∪ FVTm (dyck-term-fixed d m dy) ≡ dyck-bd-supp d dy true
dyck-bd-drop zero End = refl
dyck-bd-drop zero (⇑ {d = d} dy) with <-cmp (suc d) (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = ⊥-elim (1+n≰n (≤-trans a (≤-trans (≤-reflexive (dyck-type-dim dy)) (n≤1+n d))))
... | tri≈ ¬a b ¬c = ⊥-elim (1+n≢n (trans b (dyck-type-dim dy)))
... | tri> ¬a ¬b c = cong (ewt ∘ ewt) (∪-right-unit (dyck-bd-supp (suc d) dy true))
dyck-bd-drop zero (⇓ dy) = dyck-bd-drop 1 dy
dyck-bd-drop (suc m) (⇓ dy) = dyck-bd-drop (2+ m) dy
dyck-bd-drop {d = d} (suc zero) (⇑ dy) with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = ⊥-elim (1+n≰n (≤-trans a (≤-reflexive (dyck-type-dim dy))))
... | tri≈ ¬a b ¬c = cong (ewf ∘ ewt) (∪-right-unit (drop (dyck-bd-supp d dy true)))
... | tri> ¬a ¬b c = ⊥-elim (1+n≰n (≤-trans c (≤-reflexive (sym (dyck-type-dim dy)))))
dyck-bd-drop {d = d} (2+ m) (⇑ dy) with <-cmp d (ty-dim (dyck-type dy))
... | tri< a ¬b ¬c = begin
  ewf (ewf (drop (dyck-bd-supp d dy true)))
    ∪ FVTm (ty-tgt′ (lift-ty (truncate′ m (lift-ty (lift-ty (dyck-pre-type dy))))))
    ≡⟨ cong (ewf (ewf (drop (dyck-bd-supp d dy true))) ∪_) l2 ⟩
  ewf (ewf (drop (dyck-bd-supp d dy true) ∪ FVTm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy))))))
    ≡⟨ cong (ewf ∘ ewf) (dyck-bd-drop (suc m) dy) ⟩
  ewf (ewf (dyck-bd-supp d dy true)) ∎
  where
    l1 : ty-tgt′ (lift-ty (truncate′ m (lift-ty (lift-ty (dyck-pre-type dy)))))
         ≃tm
         lift-tm (lift-tm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy)))))
    l1 = begin
      < ty-tgt′ (lift-ty (truncate′ m (lift-ty (lift-ty (dyck-pre-type dy))))) >tm
        ≈⟨ ty-tgt′-≃ (lift-ty-≃ (lem m dy)) ⟩
      < ty-tgt′ (lift-ty (lift-ty (lift-ty (truncate′ m (dyck-pre-type dy))))) >tm
        ≈⟨ ty-tgt′-lift (lift-ty (lift-ty (truncate′ m (dyck-pre-type dy)))) ⦃ NonZero-subst (sym (lift-ty-dim _)) nz1 ⦄ ⟩
      < lift-tm (ty-tgt′ (lift-ty (lift-ty (truncate′ m (dyck-pre-type dy))))) >tm
        ≈⟨ lift-tm-≃ (ty-tgt′-lift (lift-ty (truncate′ m (dyck-pre-type dy))) ⦃ nz1 ⦄) ⟩
      < lift-tm (lift-tm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy))))) >tm ∎
       where
         dim-lem : ty-dim (lift-ty (truncate′ m (dyck-pre-type dy))) ≡ suc d
         dim-lem = begin
           ty-dim (lift-ty (truncate′ m (dyck-pre-type dy)))
             ≡⟨ lift-ty-dim (truncate′ m (dyck-pre-type dy)) ⟩
           ty-dim (truncate′ m (dyck-pre-type dy))
             ≡⟨ truncate′-dim m (dyck-pre-type dy) ⟩
           ty-dim (dyck-pre-type dy) ∸ m
             ≡⟨ cong (_∸ m) (dyck-pre-type-dim dy) ⟩
           suc (m + d) ∸ m
             ≡˘⟨ cong (_∸ m) (+-suc m d) ⟩
           m + suc d ∸ m
             ≡⟨ cong (_∸ m) (+-comm m (suc d)) ⟩
           suc d + m ∸ m
             ≡⟨ m+n∸n≡m (suc d) m ⟩
           suc d ∎
           where
             open ≡-Reasoning
         open Reasoning tm-setoid


         nz1 : NonZero (ty-dim (lift-ty (truncate′ m (dyck-pre-type dy))))
         nz1 = NonZero-subst (sym dim-lem) it

    open ≡-Reasoning

    l2 : FVTm (ty-tgt′ (lift-ty (truncate′ m (lift-ty (lift-ty (dyck-pre-type dy))))))
         ≡
         ewf (ewf (FVTm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy))))))
    l2 = begin
      FVTm (ty-tgt′ (lift-ty (truncate′ m (lift-ty (lift-ty (dyck-pre-type dy))))))
        ≡⟨ FVTm-≃ l1 ⟩
      FVTm (lift-tm (lift-tm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy))))))
        ≡⟨ supp-lift-tm (lift-tm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy))))) ⟩
      ewf (FVTm (lift-tm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy))))))
        ≡⟨ cong ewf (supp-lift-tm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy))))) ⟩
      ewf (ewf (FVTm (ty-tgt′ (lift-ty (truncate′ m (dyck-pre-type dy)))))) ∎


... | tri≈ ¬a b ¬c = ⊥-elim (¬a (≤-trans (+-monoˡ-≤ d (s≤s z≤n)) (≤-reflexive (sym (dyck-type-dim dy)))))
... | tri> ¬a ¬b c = ⊥-elim (¬a (≤-trans (+-monoˡ-≤ d (s≤s z≤n)) (≤-reflexive (sym (dyck-type-dim dy)))))

dyck-bd-drop-≡ : (d : ℕ) → (dy : Dyck n m) → d ≡ m
               → drop (dyck-bd-supp d dy true) ∪ FVTm (dyck-term dy)
                 ≡
                 dyck-bd-supp d dy true
dyck-bd-drop-≡ d dy refl = dyck-bd-drop 0 dy

dyck-bd-contains-ty : (x d : ℕ) → (dy : Dyck n m) → (b : Bool) → m ≤ x + d
                    → FVTy (lift-ty (truncate′ x (dyck-pre-type dy))) ⊆ drop (dyck-bd-supp d dy b)
dyck-bd-contains-ty′ : (x d : ℕ) → (dy : Dyck n m) → (b : Bool) → m ≤ x + d
                     → FVTy (lift-ty (truncate′ x (dyck-pre-type dy))) ⊆ dyck-bd-supp d dy b
dyck-bd-contains-tm : (d : ℕ) → (dy : Dyck n m) → (b : Bool) → m < d
                    → FVTm (dyck-term dy) ⊆ dyck-bd-supp d dy b

dyck-bd-contains-ty zero d End b p = ⊆-bot (drop (dyck-bd-supp d End b))
dyck-bd-contains-ty zero d (⇑ dy) b p = begin
  FVTy (lift-ty (lift-ty (dyck-type dy))) ∪ FVTm (lift-tm (lift-tm (dyck-term dy))) ∪ ewf (ewt empty)
    ≈⟨ cong₂ (λ a b → a ∪ b ∪ ewf (ewt empty))
             (trans (supp-lift-ty (lift-ty (dyck-type dy)))
                    (cong ewf (supp-lift-ty (dyck-type dy))))
             (trans (supp-lift-tm (lift-tm (dyck-term dy)))
                    (cong ewf (supp-lift-tm (dyck-term dy)))) ⟩
  ewf (ewt (FVTy (dyck-type dy) ∪ FVTm (dyck-term dy) ∪ empty))
    ≈⟨ cong (ewf ∘ ewt) (∪-right-unit (FVTy (lift-ty (dyck-pre-type dy)) ∪ FVTm (dyck-term dy))) ⟩
  ewf (ewt (FVTy (dyck-type dy) ∪ FVTm (dyck-term dy)))
    ≤⟨ ⊆-cong {xs = ewt (FVTy (dyck-type dy) ∪ FVTm (dyck-term dy))}
              false
              (⊆-cong true (∪-⊆ (⊆-trans (dyck-bd-contains-ty zero d dy b (≤-trans (n≤1+n _) p)) (⊆-drop (dyck-bd-supp d dy b)))
                                (dyck-bd-contains-tm d dy b p))) ⟩
  ewf (ewt (dyck-bd-supp d dy b))
    ≈˘⟨ cong drop (tri-case> (≤-trans (s≤s (≤-reflexive (dyck-type-dim dy))) p) (<-cmp d (ty-dim (dyck-type dy))) _ _ _) ⟩
  drop (dyck-bd-supp d (⇑ dy) b) ∎
  where
    open PReasoning (⊆-poset _)
dyck-bd-contains-ty zero d (⇓ dy) b p = dyck-bd-contains-ty 1 d dy b (s≤s p)
dyck-bd-contains-ty (suc x) d End b p = begin
  FVTy (lift-ty (truncate′ x ⋆))
    ≈⟨ l1 x ⟩
  empty
    ≤⟨ ⊆-bot (drop (dyck-bd-supp d End b)) ⟩
  drop (dyck-bd-supp d End b) ∎
  where
    l1 : (y : ℕ) → FVTy (lift-ty (truncate′ y (⋆ {n = n}))) ≡ empty
    l1 zero = refl
    l1 (suc y) = l1 y
    open PReasoning (⊆-poset _)

dyck-bd-contains-ty (suc x) d (⇑ dy) b p with <-cmp d (ty-dim (lift-ty (dyck-pre-type dy)))
... | tri< a ¬b ¬c = begin
  FVTy (lift-ty (truncate′ x (lift-ty (lift-ty (dyck-pre-type dy)))))
    ≈⟨ FVTy-≃ (lift-ty-≃ (lem x dy)) ⟩
  FVTy (lift-ty (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≈⟨ supp-lift-ty (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))) ⟩
  ewf (FVTy (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≈⟨ cong ewf (supp-lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))) ⟩
  ewf (ewf (FVTy (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≤⟨ cong (ewf ∘ ewf) (dyck-bd-contains-ty x d dy b (≤-pred p)) ⟩
  ewf (ewf (drop (dyck-bd-supp d dy b))) ∎
  where
    open PReasoning (⊆-poset _)
... | tri> ¬a ¬b c = begin
  FVTy (lift-ty (truncate′ x (lift-ty (lift-ty (dyck-pre-type dy)))))
    ≈⟨ FVTy-≃ (lift-ty-≃ (lem x dy)) ⟩
  FVTy (lift-ty (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≈⟨ supp-lift-ty (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))) ⟩
  ewf (FVTy (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≈⟨ cong ewf (supp-lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))) ⟩
  ewf (ewf (FVTy (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≤⟨ cong (ewf ∘ ewf) (dyck-bd-contains-ty′ x d dy b (≤-pred p)) ⟩
  ewf (ewf (dyck-bd-supp d dy b))
    ≤⟨ ⊆-cong {xs = ewf (dyck-bd-supp d dy b)} false (⊆-step (dyck-bd-supp d dy b)) ⟩
  ewf (ewt (dyck-bd-supp d dy b)) ∎
  where
    open PReasoning (⊆-poset _)
... | tri≈ ¬a b₁ ¬c = begin
  FVTy (lift-ty (truncate′ x (lift-ty (lift-ty (dyck-pre-type dy)))))
    ≈⟨ FVTy-≃ (lift-ty-≃ (lem x dy)) ⟩
  FVTy (lift-ty (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≈⟨ supp-lift-ty (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))) ⟩
  ewf (FVTy (lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≈⟨ cong ewf (supp-lift-ty (lift-ty (truncate′ x (dyck-pre-type dy)))) ⟩
  ewf (ewf (FVTy (lift-ty (truncate′ x (dyck-pre-type dy)))))
    ≤⟨ cong (ewf ∘ ewf) (dyck-bd-contains-ty x d dy b (≤-pred p)) ⟩
  ewf (ewf (drop (dyck-bd-supp d dy b)))
    ≈⟨ l1 b ⟩
  ewf (drop (b ∷ cdrop b (dyck-bd-supp d dy b))) ∎
  where
    open PReasoning (⊆-poset _)

    l1 : (b : Bool) → ewf (ewf (drop (dyck-bd-supp d dy b)))
                      ≡
                      ewf (drop (b ∷ cdrop b (dyck-bd-supp d dy b)))
    l1 false = refl
    l1 true = refl
dyck-bd-contains-ty (suc x) d (⇓ dy) b p = dyck-bd-contains-ty (2+ x) d dy b (s≤s p)

dyck-bd-contains-ty′ x d dy b p = begin
  FVTy (lift-ty (truncate′ x (dyck-pre-type dy)))
    ≤⟨ dyck-bd-contains-ty x d dy b p ⟩
  drop (dyck-bd-supp d dy b)
    ≤⟨ ⊆-drop (dyck-bd-supp d dy b) ⟩
  dyck-bd-supp d dy b ∎
  where
    open PReasoning (⊆-poset _)

dyck-bd-contains-tm d End b p = refl
dyck-bd-contains-tm d (⇑ dy) b p = begin
  ewt empty
    ≤⟨ ⊆-cong {xs = empty} true (⊆-bot (ewt (dyck-bd-supp d dy b))) ⟩
  ewt (ewt (dyck-bd-supp d dy b))
    ≈˘⟨ tri-case> (≤-trans (s≤s (≤-trans (≤-reflexive (dyck-type-dim dy)) (n≤1+n _))) p) (<-cmp d (ty-dim (dyck-type dy))) _ _ _ ⟩
  dyck-bd-supp d (⇑ dy) b ∎
  where
    open PReasoning (⊆-poset _)
dyck-bd-contains-tm d (⇓ dy) b p = begin
  FVTm (ty-tgt′ (dyck-type dy))
    ≤⟨ ty-tgt′-⊆ (dyck-type dy) ⦃ NonZero-subst (sym (dyck-type-dim dy)) it ⦄ ⟩
  FVTy (dyck-type dy)
    ≤⟨ dyck-bd-contains-ty 0 d dy b p ⟩
  drop (dyck-bd-supp d dy b)
    ≤⟨ ⊆-drop (dyck-bd-supp d dy b) ⟩
  dyck-bd-supp d dy b ∎
  where
    open PReasoning (⊆-poset _)
