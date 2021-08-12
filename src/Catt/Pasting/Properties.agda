{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Properties where

open import Catt.Syntax
open import Catt.Syntax.Patterns
open import Catt.Pasting
open import Relation.Binary.PropositionalEquality
open import Data.Nat

extend-pd-eq : (pdb : Γ ⊢pd[ submax ][ d ])
             → A ≡ getFocusType pdb
             → B ≡ liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V
             → Γ , A , B ⊢pd[ pred submax ][ suc d ]
extend-pd-eq pdb refl refl = Extend pdb

extend-pd-eq-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ])
                    → (p : A ≡ getFocusType pdb)
                    → (q : B ≡ liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                    → 0V ≡ getFocusTerm (extend-pd-eq pdb p q)
extend-pd-eq-foc-tm pdb refl refl = refl

extend-pd-eq-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ])
                    → (p : A ≡ getFocusType pdb)
                    → (q : B ≡ liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ 0V)
                    → liftTerm (liftTerm (getFocusTerm pdb)) ─⟨ liftType (liftType (getFocusType pdb)) ⟩⟶ 1V ≡ getFocusType (extend-pd-eq pdb p q)
extend-pd-eq-foc-ty pdb refl refl = refl

submax-irrelevant : (pdb : Γ ⊢pd[ submax ][ d ]) (pdb2 : Γ ⊢pd[ submax′ ][ d ]) → submax ≡ submax′
submax-irrelevant Base Base = refl
submax-irrelevant Base (Restr pdb2) = {!!}
submax-irrelevant (Extend {submax = zero} pdb) pdb2 = {!!}
submax-irrelevant (Extend {submax = suc submax} pdb) pdb2 = {!!}
submax-irrelevant (Restr pdb) pdb2 = {!!}

pdb-irrelevant : (pdb : Γ ⊢pd[ submax ][ d ]) (pdb2 : Γ ⊢pd[ submax ][ d ]) → pdb ≡ pdb2
pdb-irrelevant Base Base = {!!}
pdb-irrelevant (Extend pdb) pdb2 = {!!}
pdb-irrelevant (Restr pdb) pdb2 = {!!}
