module Catt.Ops.All where

open import Catt.Prelude
open import Catt.Typing.Rule
open import Catt.Ops.Pruning
open import Catt.Ops.Insertion

All : Op
All Γ xs ys = ⊤

all-standard-op : StandardOp All
all-standard-op Γ d p = tt

all-susp-op : SuspOp All
all-susp-op Γ xs ys x = tt

all-tame : TameOp All
all-tame .TameOp.susp-op = all-susp-op
all-tame .TameOp.standard-op = all-standard-op

all-pruning-op : PruningOp All
all-pruning-op dy pk xs ys x = tt

all-insertion-op : InsertionSOp All
all-insertion-op S P T x xs ys y = tt
