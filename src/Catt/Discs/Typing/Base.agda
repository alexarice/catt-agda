open import Catt.Typing.Rule

module Catt.Discs.Typing.Base (ops : Op)
                              (rules : RuleSet)
                              (wk-cond : WkCond rules) where

open import Catt.Prelude
open import Catt.Discs

open import Catt.Typing ops rules
open import Catt.Typing.Properties.Weakening ops rules wk-cond

sphere-type-Ty : (d : ℕ) → Typing-Ty (Sphere d) (sphere-type d)
sphere-type-Ty zero = TyStar
sphere-type-Ty (suc d) = TyArr (TyVar (suc zero)) (wk-ty-typing (wk-ty-typing (sphere-type-Ty d))) (TyVar zero)

sphere-Ty : (d : ℕ) → Typing-Ctx (Sphere d)
disc-Ty : (d : ℕ) → Typing-Ctx (Disc d)

sphere-Ty zero = TyEmp
sphere-Ty (suc d) = TyAdd (disc-Ty d) (wk-ty-typing (sphere-type-Ty d))

disc-Ty d = TyAdd (sphere-Ty d) (sphere-type-Ty d)
