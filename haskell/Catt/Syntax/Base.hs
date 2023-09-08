module Catt.Syntax.Base where

import Numeric.Natural (Natural)

data Ctx = C1
         | C2 Ctx Ty

data Ty = Ty1
        | Ty2 Tm Ty Tm

data Tm = Var Natural
        | Coh Ctx Ty Sub

data Sub = S1
         | S2 Sub Tm

