{-# OPTIONS --safe --without-K --exact-split #-}

module Catt.Pasting.Properties where

open import Catt.Syntax
open import Catt.Pasting
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Patterns
open import Data.Nat

extend-pd-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ])
                 → Var 0F ≡ getFocusTerm (extend-pd pdb)
extend-pd-foc-tm {submax = zero} pdb = refl
extend-pd-foc-tm {submax = suc submax} pdb = refl

extend-pd-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ])
                 → liftTerm (liftTerm (getFocusTerm pdb)) ─⟨ liftType (liftType (getFocusType pdb)) ⟩⟶ Var 1F ≡ getFocusType (extend-pd pdb)
extend-pd-foc-ty {submax = zero} pdb = refl
extend-pd-foc-ty {submax = suc submax} pdb = refl

extend-pd-eq : (pdb : Γ ⊢pd[ submax ][ d ])
             → A ≡ getFocusType pdb
             → B ≡ liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F
             → Γ , A , B ⊢pd[ pred submax ][ suc d ]
extend-pd-eq pdb refl refl = extend-pd pdb

extend-pd-eq-foc-tm : (pdb : Γ ⊢pd[ submax ][ d ])
                    → (p : A ≡ getFocusType pdb)
                    → (q : B ≡ liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F)
                    → Var 0F ≡ getFocusTerm (extend-pd-eq pdb p q)
extend-pd-eq-foc-tm pdb refl refl = extend-pd-foc-tm pdb

extend-pd-eq-foc-ty : (pdb : Γ ⊢pd[ submax ][ d ])
                    → (p : A ≡ getFocusType pdb)
                    → (q : B ≡ liftTerm (getFocusTerm pdb) ─⟨ liftType (getFocusType pdb) ⟩⟶ Var 0F)
                    → liftTerm (liftTerm (getFocusTerm pdb)) ─⟨ liftType (liftType (getFocusType pdb)) ⟩⟶ Var 1F ≡ getFocusType (extend-pd-eq pdb p q)
extend-pd-eq-foc-ty pdb refl refl = extend-pd-foc-ty pdb
