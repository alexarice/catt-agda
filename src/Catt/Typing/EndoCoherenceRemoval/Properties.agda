open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P
import Catt.Typing.EndoCoherenceRemoval as ECR

module Catt.Typing.EndoCoherenceRemoval.Properties (index : ℕ)
                                          (rule : Fin index → Rule)
                                          (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                                          (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                                          (sub-rule : ∀ i a → P.SubRule index rule {i} a)
                                          (ecr : ECR.HasEndoCoherenceRemoval index rule) where

open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing index rule
open import Catt.Tree
open import Catt.Tree.Label
open import Catt.Tree.Label.Properties
open import Catt.Tree.Label.Typing index rule
open import Catt.Tree.Label.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Tree.Unbiased
open import Catt.Tree.Unbiased.Properties
open import Catt.Tree.Unbiased.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Tree.Path
open import Catt.Typing.Properties.Base index rule
open import Catt.Tree.Boundary
open import Catt.Tree.Boundary.Properties
