open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Boundary.Typing {index : Set}
                                 (rule : index → Rule)
                                 (lift-rule : ∀ i → P.LiftRule rule i)
                                 (susp-rule : ∀ i → P.SuspRule rule i)
                                 (sub-rule : ∀ i → P.SubRule rule i) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Typing rule
open import Catt.Typing.Properties rule lift-rule susp-rule sub-rule
open import Catt.Connection.Typing rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing rule lift-rule
open import Catt.Suspension.Typing rule lift-rule susp-rule
open import Catt.Suspension
open import Catt.Suspension.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Typing rule lift-rule susp-rule sub-rule
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing rule
open import Catt.Tree.Label.Typing.Properties rule lift-rule susp-rule sub-rule

tree-inc-Ty : (d : ℕ) → (T : Tree n) → (b : Bool) → Typing-Label (tree-to-ctx T) (tree-inc-label d T b)
tree-inc-Ty zero T false = TySing (TySPath PHere)
tree-inc-Ty zero T true = TySing (last-path-Ty T)
tree-inc-Ty (suc d) Sing b = TySing (TySPath PHere)
tree-inc-Ty (suc d) (Join S T) b
  = TyJoin (TySPath PHere)
           (transport-label-typing (map-pext-Ty (tree-inc-Ty d S b)) [ (λ P → compute-≃ refl≃stm) ] (≃SArr refl≃stm refl≃sty (compute-≃ (≃SShift refl≃ (≃SPath (sym≃p (tree-inc-label-phere d T b)))))))
           (transport-label-typing (map-pshift-Ty (tree-inc-Ty (suc d) T b)) [ (λ P → compute-≃ refl≃stm) ] refl≃sty)
