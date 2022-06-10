module Catt.Test where

data Tree : Set where
  Sing : Tree
  Join : Tree → Tree → Tree

Σ : Tree → Tree
Σ T = Join T Sing

variable
  S T U : Tree

data Path : Tree → Set where
  Cns : (T : Tree) → Path T
  InL : {S : Tree} → (T : Tree) → Path S → Path (Join S T)
  InR : (S : Tree) → {T : Tree} → Path T → Path (Join S T)

data Ty (S : Tree) : Set
data Tm (S : Tree) : Set
data Sub (S : Tree)  : Tree → Set

variable
  A B : Ty S
  s t x : Tm S
  σ τ : Sub T S

data Ty S where
  Star : Ty S
  Arr : (A : Ty S) → (s t : Tm S) → Ty S

infix 5 _[_]ty _[_]tm _；_
_[_]ty : Ty S → Sub T S → Ty T
_[_]tm : Tm S → (σ : Sub T S) → Tm T
_；_ : Sub T S → (σ : Sub U T) → Sub U S

Star [ σ ]ty = Star
Arr A s t [ σ ]ty = Arr (A [ σ ]ty) (s [ σ ]tm) (t [ σ ]tm)

data Sub S where
  LSing : (s : Tm S) → Sub S Sing
  LJoin : (s : Tm S) → Sub S T → Sub S U → Sub S (Join T U)

LSing x ； τ = LSing (x [ τ ]tm)
LJoin t σ μ ； τ = LJoin (t [ τ ]tm) (σ ； τ) (μ ； τ)

data Tm S where
  Var : (P : Path S) → Tm S
  Coh : (T : Tree) → (σ : Sub S T) → (A : Ty T) → Tm S

first-label : Sub T S → Tm T
first-label (LSing s) = s
first-label (LJoin s σ τ) = s

Var (Cns _) [ σ ]tm = first-label σ
Var (InL T P) [ LJoin s σ τ ]tm = Var P [ σ ]tm
Var (InR S P) [ LJoin s σ τ ]tm = Var P [ τ ]tm
Coh T τ A [ σ ]tm = Coh T (τ ； σ) A

mapInLTy : Ty S → Ty (Join S T)
mapInLTm : Tm S → Tm (Join S T)
mapInLSub : Sub S U → Sub (Join S T) U

mapInLTy Star = Arr Star (Var (Cns (Join _ _))) (Var (InR _ (Cns _)))
mapInLTy (Arr A s t) = Arr (mapInLTy A) (mapInLTm s) (mapInLTm t)

mapInLTm (Var P) = Var (InL _ P)
mapInLTm (Coh T σ A) = Coh (Σ T) (LJoin (Var (Cns (Join _ _))) (mapInLSub σ) (LSing (Var (InR _ (Cns _))))) (mapInLTy A)

mapInLSub (LSing s) = LSing (mapInLTm s)
mapInLSub (LJoin s σ τ) = LJoin (mapInLTm s) (mapInLSub σ) (mapInLSub τ)

mapInRTy : Ty T → Ty (Join S T)
mapInRTm : Tm T → Tm (Join S T)
mapInRSub : Sub T U → Sub (Join S T) U

mapInRTy Star = Star
mapInRTy (Arr A s t) = Arr (mapInRTy A) (mapInRTm s) (mapInRTm t)

mapInRTm (Var P) = Var (InR _ P)
mapInRTm (Coh T σ A) = Coh T (mapInRSub σ) A

mapInRSub (LSing s) = LSing (mapInRTm s)
mapInRSub (LJoin s σ τ) = LJoin (mapInRTm s) (mapInRSub σ) (mapInRSub τ)

path-to-type : Path S → Ty S
path-to-type (Cns _) = Star
path-to-type (InL T P) = mapInLTy (path-to-type P)
path-to-type (InR S P) = mapInRTy (path-to-type P)

data Typ-Ty : Ty S → Set
data Typ-Tm : Tm S → Ty S → Set
data Typ-Sub : Sub T S → Ty T → Set

data Typ-Ty where
  TyStar : Typ-Ty (Star {S = S})
  TyArr : Typ-Ty A → Typ-Tm s A → Typ-Tm t A → Typ-Ty (Arr A s t)

data Typ-Tm where
  TyVar : (P : Path S) → Typ-Tm (Var P) (path-to-type P)
  TyCoh : Typ-Sub σ Star → Typ-Ty A → Typ-Tm (Coh T σ A) (A [ σ ]ty)

data Typ-Sub where
  TySing : Typ-Tm s A → Typ-Sub (LSing s) A
  TyJoin : Typ-Tm s A → Typ-Sub σ (Arr A s (first-label τ)) → Typ-Sub τ A → Typ-Sub (LJoin s σ τ) A

-- map properties

mapInLTy-Typ : Typ-Ty A → Typ-Ty (mapInLTy {T = T} A)
mapInLTm-Typ : Typ-Tm s A → Typ-Tm (mapInLTm {T = T} s) (mapInLTy A)
mapInLSub-Typ : Typ-Sub σ A → Typ-Sub (mapInLSub {T = T} σ) (mapInLTy A)

mapInLTy-Typ TyStar = TyArr TyStar (TyVar (Cns (Join _ _))) (TyVar (InR _ (Cns _)))
mapInLTy-Typ (TyArr Aty sty tty) = TyArr (mapInLTy-Typ Aty) (mapInLTm-Typ sty) (mapInLTm-Typ tty)

mapInLTm-Typ (TyVar P) = TyVar (InL _ P)
mapInLTm-Typ (TyCoh σty Aty) = {!!}

mapInLSub-Typ (TySing x) = TySing (mapInLTm-Typ x)
mapInLSub-Typ (TyJoin x σty τty) = TyJoin (mapInLTm-Typ x) {!mapInLSub-Typ σty!} {!!}

-- categorical properties

idSub : (S : Tree) → Sub S S
idSub Sing = LSing (Var (Cns Sing))
idSub (Join S T) = LJoin (Var (Cns (Join S T))) (mapInLSub (idSub S)) (mapInRSub (idSub T))

idSub-Typ : (S : Tree) → Typ-Sub (idSub S) Star
idSub-Typ Sing = TySing (TyVar (Cns Sing))
idSub-Typ (Join S T) = TyJoin (TyVar (Cns (Join S T))) {!!} {!!}
