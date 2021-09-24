{-# OPTIONS --without-K --safe --exact-split --postfix-projections #-}

open import Catt.Typing.Base
import Catt.Typing.Properties.Base
open import Data.Fin using (Fin; zero; suc; inject₁; toℕ)
open import Data.Nat

module Catt.Typing.Properties (index : ℕ) (rule : Fin index → Rule) (props : (i : Fin index) → Catt.Typing.Properties.Base.Props index rule i) where

open import Catt.Typing.Properties.Base index rule public

open import Catt.Typing index rule
open import Catt.Syntax
open import Catt.Syntax.SyntacticEquality
open import Relation.Binary.PropositionalEquality
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Catt.Syntax.Bundles
open import Catt.Suspension
open import Catt.Support
open import Catt.Suspension.Support
open import Data.Bool using (Bool; true; false)
open import Data.Product renaming (_,_ to _,,_)
open import Catt.Tree.Support
open import Catt.Tree
open import Catt.Tree.Properties
open import Data.Empty

term-conversion : Typing-Tm Γ t A → A ≈[ Γ ]ty B → Typing-Tm Γ t B
-- term-conversion (TyVar i x) eq = TyVar i (trans≈ty x eq)
term-conversion (TyVarZ x) eq = TyVarZ (trans≈ty x eq)
term-conversion (TyVarS i tvi x) eq = TyVarS i tvi (trans≈ty x eq)
term-conversion (TyCoh Aty σty b sc p) eq = TyCoh Aty σty b sc (trans≈ty p eq)

-- type-conversion : Typing-Ty Γ A → A ≈[ Γ ]ty B → Typing-Ty Γ B
-- type-conversion TyStar Star≈ = TyStar
-- type-conversion (TyArr sty Aty tty) (Arr≈ p q r) = TyArr {!!} {!!} {!!}

lift-ty-typing : Typing-Ty Γ A → Typing-Ty (Γ , B) (liftType A)
lift-tm-typing : Typing-Tm Γ t A → Typing-Tm (Γ , B) (liftTerm t) (liftType A)
lift-sub-typing : Typing-Sub Γ Δ σ → Typing-Sub Γ (Δ , B) (liftSub σ)

lift-ty-equality : B ≈[ Γ ]ty C → (liftType B) ≈[ Γ , A ]ty (liftType C)
lift-tm-equality : s ≈[ Γ ]tm t → (liftTerm s) ≈[ Γ , A ]tm (liftTerm t)
lift-sub-equality : σ ≈[ Γ ]s τ → (liftSub σ) ≈[ Γ , A ]s (liftSub τ)

lift-ty-typing TyStar = TyStar
lift-ty-typing (TyArr p q r) = TyArr (lift-tm-typing p) (lift-ty-typing q) (lift-tm-typing r)

lift-tm-typing (TyVarZ x) = TyVarS zero (TyVarZ x) refl≈ty
lift-tm-typing (TyVarS i tvi x) = TyVarS (suc i) (TyVarS i tvi x) refl≈ty
lift-tm-typing (TyCoh {A = A} Aty σty b sc p) = TyCoh Aty (lift-sub-typing σty) b sc (trans≈ty (reflexive≈ty (apply-lifted-sub-ty-≃ A _)) (lift-ty-equality p))

lift-sub-typing (TyNull x) = TyNull (lift-ty-typing x)
lift-sub-typing (TyExt {A = A} p r) = TyExt (lift-sub-typing p) (term-conversion (lift-tm-typing r) (reflexive≈ty (sym≃ty (apply-lifted-sub-ty-≃ A _))))

lift-ty-equality Star≈ = Star≈
lift-ty-equality (Arr≈ q r s) = Arr≈ (lift-tm-equality q) (lift-ty-equality r) (lift-tm-equality s)

lift-tm-equality (Var≈ x) = Var≈ (cong suc x)
lift-tm-equality (Sym≈ eq) = Sym≈ (lift-tm-equality eq)
lift-tm-equality (Trans≈ eq eq′) = Trans≈ (lift-tm-equality eq) (lift-tm-equality eq′)

lift-tm-equality (Coh≈ r s) = Coh≈ r (lift-sub-equality s)
lift-tm-equality {A = A} (Rule≈ i a tc) = props i .lift-rule a (lift-tm-typing tc)

lift-sub-equality (Null≈ x) = Null≈ (lift-ty-equality x)
lift-sub-equality (Ext≈ eq x) = Ext≈ (lift-sub-equality eq) (lift-tm-equality x)

-- Suspension

suspCtxTy : Typing-Ctx Γ → Typing-Ctx (suspCtx Γ)
suspTyTy : Typing-Ty Γ A → Typing-Ty (suspCtx Γ) (suspTy A)
suspTmTy : Typing-Tm Γ t A → Typing-Tm (suspCtx Γ) (suspTm t) (suspTy A)
suspSubTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) (suspCtx Δ) (suspSub σ)
getFstTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getFst) ⋆
getSndTy : {Γ : Ctx n} → Typing-Tm (suspCtx Γ) (getSnd) ⋆

suspTyEq : A ≈[ Γ ]ty B → suspTy A ≈[ suspCtx Γ ]ty suspTy B
suspTmEq : s ≈[ Γ ]tm t → suspTm s ≈[ suspCtx Γ ]tm suspTm t
suspSubEq : σ ≈[ Γ ]s τ → suspSub σ ≈[ suspCtx Γ ]s suspSub τ

suspSuppCondition : {b : Bool} → {A : Ty (suc n)} → {T : Tree n} → supp-condition b A T → supp-condition b (suspTy A) (suspTree T)
suspSuppCondition {b = false} {A} {T} sc = begin
  FVTy (suspTy A) ≡⟨ suspSuppTy A ⟩
  suspSupp (FVTy A) ≡⟨ cong suspSupp sc ⟩
  suspSupp full ≡⟨ suspSuppFull ⟩
  full ∎
  where
    open ≡-Reasoning
suspSuppCondition {b = true} {s ─⟨ A ⟩⟶ t} {T@(Join S₁ S₂)} (sc1 ,, sc2) = l1 ,, l2
  where
    open ≡-Reasoning
    suc-pred : (n : ℕ) → zero ≢ n → suc (pred n) ≡ n
    suc-pred zero p = ⊥-elim (p refl)
    suc-pred (suc n) p = refl

    l1 : FVTy (suspTy A) ∪ FVTm (suspTm s) ≡ supp-bd (tree-dim T) (suspTree T) false
    l1 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm s) ≡⟨ suspSuppTyTm A s ⟩
      suspSupp (FVTy A ∪ FVTm s) ≡⟨ cong suspSupp sc1 ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T false) ≡⟨ suspSuppBd (pred (tree-dim T)) T false ⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) false ≡⟨ cong (λ - → supp-bd - (suspTree T) false) (suc-pred (tree-dim T) (join-tree-has-non-zero-dim S₁ S₂)) ⟩
      supp-bd (tree-dim T) (suspTree T) false ∎

    l2 : FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ supp-bd (tree-dim T) (suspTree T) true
    l2 = begin
      FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ suspSuppTyTm A t ⟩
      suspSupp (FVTy A ∪ FVTm t) ≡⟨ cong suspSupp sc2 ⟩
      suspSupp (supp-bd (pred (tree-dim T)) T true) ≡⟨ suspSuppBd (pred (tree-dim T)) T true ⟩
      supp-bd (suc (pred (tree-dim T))) (suspTree T) true ≡⟨ cong (λ - → supp-bd - (suspTree T) true) (suc-pred (tree-dim T) (join-tree-has-non-zero-dim S₁ S₂)) ⟩
      supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true ∎

suspCtxTy TyEmp = TyAdd (TyAdd TyEmp TyStar) TyStar
suspCtxTy (TyAdd ty x) = TyAdd (suspCtxTy ty) (suspTyTy x)

suspTyTy TyStar = TyArr getFstTy TyStar getSndTy
suspTyTy (TyArr p q r) = TyArr (suspTmTy p) (suspTyTy q) (suspTmTy r)

suspTmTy {Γ = Γ , A} (TyVarZ {Γ = .(Γ , A)} x) = TyVarZ (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift A))) (suspTyEq x))
suspTmTy (TyVarS i tvi x) = TyVarS (inject₁ (inject₁ i)) (suspTmTy tvi) (trans≈ty (reflexive≈ty (sym≃ty (susp-ty-lift _))) (suspTyEq x))
suspTmTy (TyCoh Aty σty b sc p) = TyCoh (suspTyTy Aty) (suspSubTy σty) b (suspSuppCondition sc) (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty _ _))) (suspTyEq p))


-- suspTmTy (TyComp {T = T} {s = s} {A = A} {t = t} {σ = σ} p q r x y) = TyComp (suspTyTy p) (suspSubTy q) lem1 lem2 (trans≈ty (reflexive≈ty (sym≃ty (susp-functorial-ty σ (s ─⟨ A ⟩⟶ t)))) (suspTyEq y))
--   where
--     open ≡-Reasoning
--

--     lem1 : FVTy (suspTy A) ∪ FVTm (suspTm s) ≡ supp-bd (pred (tree-dim (suspTree T))) (suspTree T) false
--     lem1 = begin
--       FVTy (suspTy A) ∪ FVTm (suspTm s) ≡⟨ suspSuppTyTm A s ⟩
--       suspSupp (FVTy A ∪ FVTm s) ≡⟨ cong suspSupp r ⟩
--       suspSupp (supp-bd (pred (tree-dim T)) T false) ≡⟨ suspSuppBd (pred (tree-dim T)) T false ⟩
--       supp-bd (suc (pred (tree-dim T))) (suspTree T) false ≡⟨ cong (λ - → supp-bd - (suspTree T) false) (suc-pred (tree-dim T)) ⟩
--       supp-bd (pred (tree-dim (suspTree T))) (suspTree T) false ∎

--     lem2 : FVTy (suspTy A) ∪ FVTm (suspTm t) ≡ supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true
--     lem2 = begin
--       FVTy (suspTy A) ∪ FVTm (suspTm t) ≡⟨ suspSuppTyTm A t ⟩
--       suspSupp (FVTy A ∪ FVTm t) ≡⟨ cong suspSupp x ⟩
--       suspSupp (supp-bd (pred (tree-dim T)) T true) ≡⟨ suspSuppBd (pred (tree-dim T)) T true ⟩
--       supp-bd (suc (pred (tree-dim T))) (suspTree T) true ≡⟨ cong (λ - → supp-bd - (suspTree T) true) (suc-pred (tree-dim T)) ⟩
--       supp-bd (pred (tree-dim (suspTree T))) (suspTree T) true ∎

suspSubTy (TyNull x) = TyExt (TyExt (TyNull TyStar) getFstTy) getSndTy
suspSubTy (TyExt p r) = TyExt (suspSubTy p) (term-conversion (suspTmTy r) (reflexive≈ty (susp-functorial-ty _ _)))

getFstTy {Γ = ∅} = TyVarS zero (TyVarZ Star≈) Star≈
getFstTy {Γ = Γ , A} = lift-tm-typing getFstTy

getSndTy {Γ = ∅} = TyVarZ Star≈
getSndTy {Γ = Γ , A} = lift-tm-typing getSndTy

-- suspCtxEq Emp≈ = refl≈c
-- suspCtxEq (Add≈ eq x) = Add≈ (suspCtxEq eq) (suspTyEq x)

suspTyEq Star≈ = refl≈ty

suspTyEq (Arr≈ q r s) = Arr≈ (suspTmEq q) (suspTyEq r) (suspTmEq s)

suspTmEq (Var≈ x) = Var≈ (begin
  toℕ (inject₁ (inject₁ _)) ≡⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ _) ≡⟨ toℕ-inject₁ _ ⟩
  toℕ _ ≡⟨ x ⟩
  toℕ _ ≡˘⟨ toℕ-inject₁ _ ⟩
  toℕ (inject₁ _) ≡˘⟨ toℕ-inject₁ (inject₁ _) ⟩
  toℕ (inject₁ (inject₁ _)) ∎)
  where
    open ≡-Reasoning
suspTmEq (Sym≈ eq) = Sym≈ (suspTmEq eq)
suspTmEq (Trans≈ eq eq′) = Trans≈ (suspTmEq eq) (suspTmEq eq′)
suspTmEq (Coh≈ q r) = Coh≈ (suspTyEq q) (suspSubEq r)
suspTmEq (Rule≈ i a tc) = props i .susp-rule a (suspTmTy tc)

suspSubEq (Null≈ x) = refl≈s
suspSubEq (Ext≈ p x) = Ext≈ (suspSubEq p) (suspTmEq x)

unrestrictTy : Typing-Sub Γ Δ σ → Typing-Sub (suspCtx Γ) Δ (unrestrict σ)
unrestrictTy (TyNull (TyArr p q r)) = TyExt (TyExt (TyNull q) p) r
unrestrictTy (TyExt σty x) = TyExt (unrestrictTy σty) (term-conversion x (reflexive≈ty (unrestrict-comp-ty _ _)))

unrestrictEq : σ ≈[ Δ ]s τ → unrestrict σ ≈[ Δ ]s unrestrict τ
unrestrictEq (Null≈ (Arr≈ p q r)) = Ext≈ (Ext≈ (Null≈ q) p) r
unrestrictEq (Ext≈ eq x) = Ext≈ (unrestrictEq eq) x

sub-typing-implies-ty-typing : {σ : Sub n m A} → Typing-Sub Γ Δ σ → Typing-Ty Δ A
sub-typing-implies-ty-typing (TyNull x) = x
sub-typing-implies-ty-typing (TyExt σty x) = sub-typing-implies-ty-typing σty

sub-eq-implies-ty-eq : {σ : Sub n m A} → {τ : Sub n m B} → σ ≈[ Δ ]s τ → A ≈[ Δ ]ty B
sub-eq-implies-ty-eq (Null≈ x) = x
sub-eq-implies-ty-eq (Ext≈ eq x) = sub-eq-implies-ty-eq eq

apply-sub-ty-typing : Typing-Ty Γ A → Typing-Sub Γ Δ σ → Typing-Ty Δ (A [ σ ]ty)
apply-sub-tm-typing : {σ : Sub n m B} → Typing-Tm Γ t A → Typing-Sub Γ Δ σ → Typing-Tm Δ (t [ σ ]tm) (A [ σ ]ty)
apply-sub-sub-typing : Typing-Sub Υ Γ τ → Typing-Sub Γ Δ σ → Typing-Sub Υ Δ (σ ∘ τ)
apply-sub-ty-eq : Typing-Sub Γ Δ σ → A ≈[ Γ ]ty B → A [ σ ]ty ≈[ Δ ]ty B [ σ ]ty
apply-sub-tm-eq : {σ : Sub n m A} → Typing-Sub Γ Δ σ → s ≈[ Γ ]tm t → s [ σ ]tm ≈[ Δ ]tm t [ σ ]tm
apply-sub-sub-eq : Typing-Sub Γ Δ σ → τ ≈[ Γ ]s μ → σ ∘ τ ≈[ Δ ]s σ ∘ μ

apply-sub-ty-typing TyStar σty = sub-typing-implies-ty-typing σty
apply-sub-ty-typing (TyArr sty Aty tty) σty = TyArr (apply-sub-tm-typing sty σty) (apply-sub-ty-typing Aty σty) (apply-sub-tm-typing tty σty)

apply-sub-tm-typing (TyVarZ x) (TyExt {t = t} {A = A} σty tty) = term-conversion tty (trans≈ty (sym≈ty (reflexive≈ty (lift-sub-comp-lem-ty {t = t} _ A))) (apply-sub-ty-eq (TyExt σty tty) x))
apply-sub-tm-typing (TyVarS {A = A} i tvi x) (TyExt {t = t} σty tty) = term-conversion (apply-sub-tm-typing tvi σty) (trans≈ty (sym≈ty (reflexive≈ty (lift-sub-comp-lem-ty {t = t} _ A))) (apply-sub-ty-eq (TyExt σty tty) x))
apply-sub-tm-typing {B = ⋆} (TyCoh {A = A} Aty τty b sc p) σty = TyCoh Aty (apply-sub-sub-typing τty σty) b sc (trans≈ty (reflexive≈ty (assoc-ty _ _ A)) (apply-sub-ty-eq σty p))
apply-sub-tm-typing {B = s ─⟨ B ⟩⟶ t} (TyCoh Aty τty b sc p) σty = term-conversion (apply-sub-tm-typing (suspTmTy (TyCoh Aty τty b sc p)) (unrestrictTy σty)) (reflexive≈ty (sym≃ty (unrestrict-comp-ty _ _)))

apply-sub-sub-typing (TyNull x) σty = TyNull (apply-sub-ty-typing x σty)
apply-sub-sub-typing (TyExt {A = A} τty tty) σty = TyExt (apply-sub-sub-typing τty σty) (term-conversion (apply-sub-tm-typing tty σty) (sym≈ty (reflexive≈ty (assoc-ty _ _ A))))

apply-sub-ty-eq σty Star≈ = refl≈ty
apply-sub-ty-eq σty (Arr≈ p q r) = Arr≈ (apply-sub-tm-eq σty p) (apply-sub-ty-eq σty q) (apply-sub-tm-eq σty r)

apply-sub-tm-eq σty (Var≈ x) with toℕ-injective x
... | refl = refl≈tm
apply-sub-tm-eq σty (Sym≈ p) = Sym≈ (apply-sub-tm-eq σty p)
apply-sub-tm-eq σty (Trans≈ p q) = Trans≈ (apply-sub-tm-eq σty p) (apply-sub-tm-eq σty q)
apply-sub-tm-eq {A = ⋆} σty (Coh≈ q r) = Coh≈ q (apply-sub-sub-eq σty r)
apply-sub-tm-eq {A = s ─⟨ A ⟩⟶ t} σty (Coh≈ q r) = apply-sub-tm-eq (unrestrictTy σty) (Coh≈ (suspTyEq q) (suspSubEq r))
apply-sub-tm-eq σty (Rule≈ i args tc) = props i .sub-rule args σty (apply-sub-tm-typing tc σty)

apply-sub-sub-eq σty (Null≈ x) = Null≈ (apply-sub-ty-eq σty x)
apply-sub-sub-eq σty (Ext≈ p x) = Ext≈ (apply-sub-sub-eq σty p) (apply-sub-tm-eq σty x)

apply-sub-eq-ty : (A : Ty n) → σ ≈[ Γ ]s τ → A [ σ ]ty ≈[ Γ ]ty A [ τ ]ty
apply-sub-eq-tm : {σ : Sub n m A} → {τ : Sub n m B} → (t : Tm n) → σ ≈[ Γ ]s τ → t [ σ ]tm ≈[ Γ ]tm t [ τ ]tm
apply-sub-eq-sub : (μ : Sub n m ⋆) → σ ≈[ Γ ]s τ → σ ∘ μ ≈[ Γ ]s τ ∘ μ

apply-sub-eq-ty ⋆ eq = sub-eq-implies-ty-eq eq
apply-sub-eq-ty (s ─⟨ A ⟩⟶ t) eq = Arr≈ (apply-sub-eq-tm s eq) (apply-sub-eq-ty A eq) (apply-sub-eq-tm t eq)

apply-sub-eq-tm (Var zero) (Ext≈ eq x) = x
apply-sub-eq-tm (Var (suc i)) (Ext≈ eq x) = apply-sub-eq-tm (Var i) eq
apply-sub-eq-tm {A = ⋆} {B = ⋆} (Coh T C τ) eq = Coh≈ refl≈ty (apply-sub-eq-sub τ eq)
apply-sub-eq-tm {A = ⋆} {B = s ─⟨ B ⟩⟶ t} (Coh T C τ) eq with sub-eq-implies-ty-eq eq
... | ()
apply-sub-eq-tm {A = s ─⟨ A ⟩⟶ t} {B = ⋆} (Coh T C τ) eq with sub-eq-implies-ty-eq eq
... | ()
apply-sub-eq-tm {A = s ─⟨ A ⟩⟶ t} {B = s₁ ─⟨ B ⟩⟶ t₁} (Coh T C τ) eq = apply-sub-eq-tm (Coh (suspTree T) (suspTy C) (suspSub τ)) (unrestrictEq eq)

apply-sub-eq-sub ⟨⟩ eq = Null≈ (sub-eq-implies-ty-eq eq)
apply-sub-eq-sub ⟨ μ , t ⟩ eq = Ext≈ (apply-sub-eq-sub μ eq) (apply-sub-eq-tm t eq)

id-Ty : {Γ : Ctx n} → Typing-Sub Γ Γ (idSub n)
id-Ty {Γ = ∅} = TyNull TyStar
id-Ty {Γ = Γ , A} = TyExt (lift-sub-typing id-Ty) (TyVarZ (reflexive≈ty (trans≃ty (sym≃ty (id-on-ty (liftType _))) (lift-sub-comp-lem-ty (liftSub (idSub _)) _))))

idSub≃-Ty : (p : Γ ≃c Δ) → Typing-Sub Γ Δ (idSub≃ p)
idSub≃-Ty Emp≃ = TyNull TyStar
idSub≃-Ty (Add≃ {A = A} {A′ = A′} p x) = TyExt (lift-sub-typing (idSub≃-Ty p)) (TyVarZ (reflexive≈ty lem))
  where
    open Reasoning ty-setoid

    lem : liftType A′ ≃ty (A [ liftSub (idSub≃ p) ]ty)
    lem = begin
      < liftType A′ >ty ≈˘⟨ lift-ty-≃ x ⟩
      < liftType A >ty ≈˘⟨ lift-ty-≃ (idSub≃-on-ty p A) ⟩
      < liftType (A [ idSub≃ p ]ty) >ty ≈˘⟨ apply-lifted-sub-ty-≃ A (idSub≃ p) ⟩
      < A [ liftSub (idSub≃ p) ]ty >ty ∎

-- ty-base-Ty : Typing-Ty Γ A → Typing-Ty Γ (ty-base A)
-- ty-base-Ty (TyArr sty Aty tty) = Aty

-- ty-src-Ty : Typing-Ty Γ A → Typing-Tm Γ (ty-src A) (ty-base A)
-- ty-src-Ty (TyArr sty Aty tty) = sty

-- ty-tgt-Ty : Typing-Ty Γ A → Typing-Tm Γ (ty-tgt A) (ty-base A)
-- ty-tgt-Ty (TyArr sty Aty tty) = tty
