open import Catt.Prelude
open import Catt.Typing.Base
import Catt.Typing.Properties.Base as P

module Catt.Tree.Path.Typing (index : ℕ)
                             (rule : Fin index → Rule)
                             (lift-rule : ∀ i a → P.LiftRule index rule {i} a)
                             (susp-rule : ∀ i a → P.SuspRule index rule {i} a)
                             (sub-rule : ∀ i a → P.SubRule index rule {i} a) where

open import Catt.Prelude.Properties
open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Properties
open import Catt.Tree.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Suspension
open import Catt.Suspension.Typing index rule lift-rule susp-rule
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Connection.Typing index rule lift-rule susp-rule sub-rule
open import Catt.Syntax.Bundles
open import Catt.Syntax.SyntacticEquality
open import Catt.Typing.Properties index rule lift-rule susp-rule sub-rule
open import Catt.Globular.Typing index rule lift-rule

data Typing-Path : (Γ : CtxOrTree n) → Path (COT-to-MT Γ) → (A : Ty n) → Set where
  TyPConv : Typing-Path ΓS P A → A ≈[ COT-to-Ctx ΓS ]ty B → Typing-Path ΓS P B
  TyHere : Typing-Path (incTree S) PHere ⋆
  TyExt : Typing-Path (incTree S) P A → Typing-Path (incTree (Join S T)) (PExt P) (suspTy A [ connect-susp-inc-left (tree-size S) (tree-size T) ]ty)
  TyShift : Typing-Path (incTree T) P A → Typing-Path (incTree (Join S T)) (PShift P) (A [ connect-susp-inc-right (tree-size S) (tree-size T) ]ty)
  TyOther : Typing-Tm (COT-to-Ctx ΓS) t A → Typing-Path ΓS (POther t) A

path-to-term-Ty : Typing-Path ΓS P A → Typing-Tm (COT-to-Ctx ΓS) (path-to-term P) A
path-to-term-Ty (TyPConv Pty p) = TyConv (path-to-term-Ty Pty) p
path-to-term-Ty {ΓS = incTree S} TyHere = fst-var-Ty (tree-to-ctx S)
path-to-term-Ty {ΓS = incTree (Join S T)} (TyExt p) = apply-sub-tm-typing (suspTmTy (path-to-term-Ty p)) (connect-susp-inc-left-Ty (tree-to-ctx T))
path-to-term-Ty {ΓS = incTree (Join S T)} (TyShift p) = apply-sub-tm-typing (path-to-term-Ty p) (connect-susp-inc-right-Ty (tree-to-ctx S))
path-to-term-Ty (TyOther x) = x
