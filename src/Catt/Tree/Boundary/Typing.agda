open import Catt.Typing.Rule

module Catt.Tree.Boundary.Typing (rules : RuleSet)
                                 (tame : Tame rules) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties

open import Catt.Tree.Structured.Typing rules
open import Catt.Tree.Structured.Typing.Properties rules tame

tree-inc-Ty : (d : ℕ) → (T : Tree n) → (b : Bool) → Typing-Label ⌊ T ⌋ (tree-inc-label d T b)
tree-inc-Ty zero T false = TySing (TySPath PHere)
tree-inc-Ty zero T true = TySing (last-path-Ty T)
tree-inc-Ty (suc d) Sing b = TySing (TySPath PHere)
tree-inc-Ty (suc d) (Join S T) b
  = TyJoin (TySPath PHere)
           (transport-label-typing (map-ext-Ty (tree-inc-Ty d S b)) [ (λ P → compute-≃ refl≃stm) ] (SArr≃ refl≃stm refl≃sty (compute-≃ (SShift≃ refl≃ (SPath≃ (sym≃p (tree-inc-label-phere d T b)))))))
           (transport-label-typing (map-shift-Ty (tree-inc-Ty (suc d) T b)) [ (λ P → compute-≃ refl≃stm) ] refl≃sty)
