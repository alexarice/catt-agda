module Catt.Tree.Structured.Support2.Properties where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Support
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Path.Properties
open import Catt.Tree.Structured
open import Catt.Tree.Structured.ToTerm
open import Catt.Tree.Structured.Support2

ContainingPosRefl : (ΓS : CtxOrTree n) → (P : Position (COT-to-MT ΓS)) → ContainingPos ΓS P P
ContainingPosRefl (incTree x) P = ConPRefl P
ContainingPosRefl (incCtx x) P = ConRefl P

ContainingPathTrans : (T : Tree n) → {P Q R : Path T} → ContainingPath T P Q → ContainingPath T Q R → ContainingPath T P R
ContainingPathTrans T (ConPRefl _) q = q
ContainingPathTrans .(Join _ _) (ConPFirst P) (ConPRefl .PHere) = ConPFirst P
ContainingPathTrans .(Join _ _) (ConPSecond P) (ConPRefl .(PShift PHere)) = ConPSecond P

ContainingPosTrans : (ΓS : CtxOrTree n) → {P Q R : Position (COT-to-MT ΓS)} → ContainingPos ΓS P Q → ContainingPos ΓS Q R → ContainingPos ΓS P R
ContainingPosTrans (incTree x) p q = ContainingPathTrans x p q
ContainingPosTrans (incCtx x) p q = ConTrans p q

CloseTMul : (ΓS : CtxOrTree n) → (xs : VarSetTF (COT-to-MT ΓS)) → CloseT ΓS (CloseT ΓS xs) ≃vst CloseT ΓS xs
CloseTMul ΓS xs ._≃vst_.forward i (j ,, con ,, k ,, con2 ,, p) = k ,, ContainingPosTrans ΓS con2 con ,, p
CloseTMul ΓS xs ._≃vst_.backward i p = i ,, ContainingPosRefl ΓS i ,, p

-- ∋stm-to-term : {Pos : Position {n = n} (COT-to-MT ΓS)} → ΓS ∶ a ∋stm Pos → (COT-to-Ctx ΓS) ∶ stm-to-term a ∋tm Pos-to-fin Pos
-- ∋sty-to-type : {Pos : Position {n = n} (COT-to-MT ΓS)} → ΓS ∶ As ∋sty Pos → (COT-to-Ctx ΓS) ∶ sty-to-type As ∋ty Pos-to-fin Pos
-- ∋lt-to-sub : {Pos : Position {n = n} (COT-to-MT ΓS)} → {L : Label-WT (COT-to-MT ΓS) S } → ΓS ∶ L ∋lt Pos → (COT-to-Ctx ΓS) ∶ label-to-sub L ∋s Pos-to-fin Pos

-- ∋stm-to-term (∋SExt p) = {!!}
-- ∋stm-to-term (∋SExt1 p) = {!!}
-- ∋stm-to-term (∋SExt2 p) = {!!}
-- ∋stm-to-term (∋SShift p) = {!!}
-- ∋stm-to-term ∋SPath = {!!}
-- ∋stm-to-term (∋SCoh x) = {!!}
-- ∋stm-to-term (∋SOther x) = {!!}

-- ∋sty-to-type (∋SSrc p) = ∋Src (∋stm-to-term p)
-- ∋sty-to-type (∋SBase p) = ∋Base (∋sty-to-type p)
-- ∋sty-to-type (∋STgt p) = ∋Tgt (∋stm-to-term p)

-- ∋lt-to-sub (∋SType p) = ∋Type (∋sty-to-type p)
-- ∋lt-to-sub {ΓS = ΓS} {Pos = Pos} (∋SLabel {L = L} (∋SPos P x)) = ∋Sub {!!}
--   where
--     p : COT-to-Ctx ΓS ∶ stm-to-term (ap L P) ∋tm Pos-to-fin Pos
--     p = ∋stm-to-term x
