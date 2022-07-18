open import Catt.Prelude
open import Catt.Typing.Base
open import Catt.Strict.ECR.Base as E

module Catt.Strict.ECR (index : ℕ)
                       (rule : Fin index → Rule)
                       (hasECR : E.HasECR index rule) where


open import Catt.Strict.ECR.Base index rule public
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Unbiased

stm-ecr : tree-dim T ≤ n → unbiased-comp′ (suc n) T ≈[ incTree T ]stm identity-stm n >>= label-from-linear-tree-unbiased (n-disc n) ⦃ ? ⦄ T 0 ,, S⋆
stm-ecr p = ?
