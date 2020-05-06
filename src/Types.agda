{-# OPTIONS --without-K #-}

module Types where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Product hiding (_,_)
open import Data.Empty
open import Data.Unit
open import Induction.WellFounded

open ≡-Reasoning

transport : {A B : Set} → A ≡ B → A → B
transport refl a = a

data Ctx : Set

data Ty : Ctx → ℕ → Set

private
  variable
    n m submax l dim : ℕ
    Γ Δ Υ : Ctx

infixl 4 _,_
data Ctx where
  ∅ : Ctx
  _,_ : (Γ : Ctx) → (A : Ty Γ n) → Ctx

data Term : (Γ : Ctx) → Ty Γ n → Set

data Substitution : (Γ : Ctx) → (Δ : Ctx) → Set

data PD : Ctx → ℕ → Set

data Ty where
  ⋆ : Ty Γ 0
  _⟶_ : {A : Ty Γ n} → (t u : Term Γ A) → Ty Γ (suc n)

trans-term : {A B : Ty Γ n} → (A ≡ B) → Term Γ A → Term Γ B
trans-term p = transport (cong (Term _) p)

trans-over-type : {A B : Ty Γ n} → {x y : Term Γ A} → {a b : Term Γ B} → (p : A ≡ B) → (p₁ : trans-term p x ≡ a) → (p₂ : trans-term p y ≡ b) → (x ⟶ y ≡ a ⟶ b)
trans-over-type refl refl refl = refl

trans₃ : {X : Set} → {A B C D : X} → (q : A ≡ B) → (p : B ≡ C) → (u : C ≡ D) → A ≡ D
trans₃ refl refl refl = refl

trans-term-trans₃ : {A B C D : Ty Γ n} → (q : A ≡ B) → (p : B ≡ C) → (u : C ≡ D) → {x : Term Γ A} → trans-term u (trans-term p (trans-term q x)) ≡ trans-term (trans₃ q p u) x
trans-term-trans₃ refl refl refl = refl

trans-term-over-type : {A B : Ty Γ n} → (p : A ≡ B) → (x y : Term Γ A) → (x ⟶ y ≡ trans-term p x ⟶ trans-term p y)
trans-term-over-type refl x y = refl

_[_]ty : Ty Δ n → Substitution Γ Δ → Ty Γ n
_[_]tm : {A : Ty Δ n} → Term Δ A → (σ : Substitution Γ Δ) → Term Γ (A [ σ ]ty)

⋆ [ σ ]ty = ⋆
(t ⟶ u) [ σ ]ty = (t [ σ ]tm) ⟶ (u [ σ ]tm)

data Substitution where
  ⟨⟩ : Substitution Γ ∅
  ⟨_,_⟩ : (σ : Substitution Γ Δ) → {A : Ty Δ n} → Term Γ (A [ σ ]ty) → Substitution Γ (Δ , A)

liftType : (A : Ty Γ n) → (B : Ty Γ m) → Ty (Γ , B) n

data Variable : Ctx → Set where
  V : {A : Ty Γ n} → Variable (Γ , A)
  G : {A : Ty Γ n} → Variable Γ → Variable (Γ , A)

FVSet : Ctx → Set
FVSet Γ = Variable Γ → Bool

Bool≡ : Bool → Bool → Bool
Bool≡ false b = not b
Bool≡ true b = b

isEqual : FVSet Γ → FVSet Γ → Bool
isEqual {∅} f g = true
isEqual {Γ , A} f g = (Bool≡ (f V) (g V)) ∧ (isEqual (λ x → f (G x)) (λ x → f (G x)))

FVCtx : (Γ : Ctx) → FVSet Γ
FVTerm : {A : Ty Γ n} → Term Γ A → FVSet Γ
FVType : Ty Γ n → FVSet Γ
FVSub : Substitution Δ Γ → FVSet Δ

FVSrc : (Γ : Ctx) → (pd : PD Γ n) → FVSet Γ
FVTgt : (Γ : Ctx) → (pd : PD Γ n) → FVSet Γ

data Term where
  Var : (A : Ty Γ n) → Term (Γ , A) (liftType A A)
  Gen : {B : Ty Γ n} → (t : Term Γ B) → (A : Ty Γ m) → Term (Γ , A) (liftType B A)
  Coh : (pd : PD Γ n) →
        (A : Ty Γ m) →
        (cA : T (isEqual (FVCtx Γ) (FVType A))) →
        (σ : Substitution Δ Γ) →
        Term Δ (A [ σ ]ty)
  Comp : (pd : PD Γ n) →
         (A : Ty Γ n) →
         (t : Term Γ A) →
         (u : Term Γ A) →
         (ct : T (isEqual (FVSrc Γ pd) (FVTerm t))) →
         (cu : T (isEqual (FVTgt Γ pd) (FVTerm u))) →
         (σ : Substitution Δ Γ) →
         Term Δ ((t ⟶ u) [ σ ]ty)

infixl 3 _∪_
_∪_ : FVSet Γ → FVSet Γ → FVSet Γ
(f ∪ g) v = f v ∨ g v

allt : FVSet Γ
allt v = true

allf : FVSet Γ
allf v = false

FVCtx Γ = allt
FVTerm (Var A) V = true
FVTerm (Var A) (G v) = false
FVTerm (Gen x A) V = false
FVTerm (Gen x A) (G v) = FVTerm x v
FVTerm (Coh pd A cA σ) = FVSub σ
FVTerm (Comp pd A x x₁ ct cu σ) = FVSub σ
FVType ⋆ = allf
FVType (_⟶_ {A = A} t u) = FVType A ∪ FVTerm t ∪ FVTerm u
FVSub ⟨⟩ = allf
FVSub ⟨ σ , x ⟩ = FVSub σ ∪ FVTerm x

liftType ⋆ A = ⋆
liftType (t ⟶ u) A = Gen t A ⟶ Gen u A

ty-base : Ty Γ (suc n) → Ty Γ n
ty-base (_⟶_ {A = A} _ _) = A

ty-src : (ty : Ty Γ (suc n)) → Term Γ (ty-base ty)
ty-src (t ⟶ u) = t

ty-tgt : (ty : Ty Γ (suc n)) → Term Γ (ty-base ty)
ty-tgt (t ⟶ u) = u

-- TermHasSubs : {A : Ty Γ n} → Term Γ A → Set
-- TermHasSubs (Var A) = ⊥
-- TermHasSubs (Gen x A) = ⊥
-- TermHasSubs (Coh pd A cA σ) = ⊤
-- TermHasSubs (Comp pd A t u ct cu σ) = ⊤

-- SigSub : Ctx → Set
-- SigSub Γ = Σ[ Δ ∈ Ctx ] Substitution Γ Δ

-- getSub : {A : Ty Γ n} → (x : Term Γ A) → TermHasSubs x → SigSub Γ
-- getSub (Coh pd A cA σ) sub = -, σ
-- getSub (Comp pd A t u ct cu σ) sub = -, σ



-- infix 3 _<s_
-- data _<s_ {Γ : Ctx} : SigSub Γ → SigSub Γ → Set where
--   SubSub : (σ : Substitution Γ Δ) → {A : Ty Δ n} → (x : Term Γ (A [ σ ]ty)) → -, σ <s -, ⟨ σ , x ⟩
--   TermSub : (σ : Substitution Γ Δ) → {A : Ty Δ n} → (x : Term Γ (A [ σ ]ty)) → (sub : TermHasSubs x) → getSub x sub <s -, ⟨ σ , x ⟩

-- wf : (Γ : Ctx) → WellFounded (_<s_ {Γ})
-- wf Γ = {!!}

{-# TERMINATING #-}
_∘_ : {Γ Δ Υ : Ctx} → Substitution Υ Δ → Substitution Δ Γ → Substitution Υ Γ
comp-lemma : (σ : Substitution Δ Γ) → (τ : Substitution Υ Δ) → {A : Ty Γ n} → (A [ τ ∘ σ ]ty) ≡ (A [ σ ]ty [ τ ]ty)
lifting-lemma : (σ : Substitution Δ Γ) → {A : Ty Γ n} → {B : Ty Γ m} → {x : Term Δ (A [ σ ]ty)} → B [ σ ]ty ≡ liftType B A [ ⟨ σ , x ⟩ ]ty

Var A [ ⟨ σ , tm ⟩ ]tm = trans-term (lifting-lemma σ) tm
Gen {B = B} x A [ ⟨ σ , tm ⟩ ]tm = trans-term (lifting-lemma σ) (x [ σ ]tm)
Coh pd A cA σ [ τ ]tm = trans-term (comp-lemma σ τ) (Coh pd A cA (τ ∘ σ))
Comp pd A t u ct cu σ [ τ ]tm = trans-term (comp-lemma σ τ) (Comp pd A t u ct cu (τ ∘ σ))

τ ∘ ⟨⟩ = ⟨⟩
τ ∘ ⟨ σ , x ⟩ = ⟨ τ ∘ σ , trans-term (sym (comp-lemma σ τ)) (x [ τ ]tm) ⟩


-- si : {A : Ty Γ n} → Substitution Γ Δ → Substitution (Γ , A) Δ
-- si-lemma : (σ : Substitution Γ Δ) → (A : Ty Γ n) → (B : Ty Δ m) → B [ si σ ]ty ≡ liftType (B [ σ ]ty) A
-- si ⟨⟩ = ⟨⟩
-- si {A = A} (⟨_,_⟩ σ {B} x) = ⟨ (si σ) , γ ⟩
--   where
--     γ : Term (_ , A) (B [ si σ ]ty)
--     γ rewrite si-lemma σ A B = Gen x A

-- id : (Γ : Ctx) → Substitution Γ Γ
-- id-lemma : (A : Ty Γ n) → A [ si (id Γ) ]ty ≡ liftType A A

-- id ∅ = ⟨⟩
-- id (Γ , A) = ⟨ si (id Γ) , γ ⟩
--   where
--     γ : Term (Γ , A) (A [ si (id Γ) ]ty)
--     γ rewrite id-lemma A = Var A

data PDB : (Γ : Ctx) → (submax : ℕ) → {A : Ty Γ n} → Term Γ A → Set where
  Base : PDB (∅ , ⋆) 0 (Var ⋆)
  ExtendMax : {A : Ty Γ n} → {x : Term Γ A} → PDB Γ 0 x → PDB (Γ , A , Gen x A ⟶ Var A) 0 (Var (Gen x A ⟶ Var A))
  ExtendNM : {A : Ty Γ n} → {x : Term Γ A} → PDB Γ (suc submax) x → PDB (Γ , A , Gen x A ⟶ Var A) submax (Var (Gen x A ⟶ Var A))
  Restr : {A : Ty Γ (suc n)} → {x : Term Γ A} → PDB Γ submax x → PDB Γ (suc submax) (ty-tgt A)

data PD where
  Finish : {x : Term Γ ⋆} → PDB Γ n x → PD Γ n

ew : Bool → FVSet Γ → {A : Ty Γ n} → FVSet (Γ , A)
ew b f V = b
ew b f (G v) = f v

FVSrc-b : {A : Ty Γ n} → {x : Term Γ A} → (pdb : PDB Γ submax x) → FVSet Γ
FVSrc-b Base = allf
FVSrc-b (ExtendMax pdb) = ew false (ew false allt)
FVSrc-b {submax = zero} (ExtendNM pdb) = ew false (ew false (FVSrc-b pdb))
FVSrc-b {submax = suc n} (ExtendNM pdb) = ew true (ew true (FVSrc-b pdb))
FVSrc-b (Restr pdb) = FVSrc-b pdb

drop′ : {A : Ty Γ n} → FVSet (Γ , A) → FVSet (Γ , A)
drop′ f V = false
drop′ f (G v) = f (G v)

drop : {A : Ty Γ n} → {x : Term Γ A} → (PDB Γ submax x) → FVSet Γ → FVSet Γ
drop Base f = drop′ f
drop (ExtendMax pdb) f = drop′ f
drop (ExtendNM pdb) f = drop′ f
drop (Restr pdb) f = drop pdb f

FVTgt-b : {A : Ty Γ n} → {x : Term Γ A} → (pdb : PDB Γ submax x) → FVSet Γ
FVTgt-b Base = allf
FVTgt-b (ExtendMax pdb) = ew false (ew true (drop pdb allt))
FVTgt-b {submax = zero} (ExtendNM pdb) = ew false (ew true (drop pdb (FVTgt-b pdb)))
FVTgt-b {submax = suc n} (ExtendNM pdb) = ew true (ew true (FVTgt-b pdb))
FVTgt-b (Restr pdb) = FVTgt-b pdb

FVSrc Γ (Finish pdb) = FVSrc-b pdb
FVTgt Γ (Finish pdb) = FVTgt-b pdb

comp-term-lemma : {A : Ty Γ n} → (x : Term Γ A) → (σ : Substitution Δ Γ) → (τ : Substitution Υ Δ) → trans-term (comp-lemma σ τ) (x [ τ ∘ σ ]tm) ≡ ((x [ σ ]tm) [ τ ]tm)


comp-term-lemma (Var A) ⟨ σ , x ⟩ τ = {!!}
comp-term-lemma (Gen x A) σ τ = {!!}
comp-term-lemma (Coh pd A cA σ₁) σ τ = {!!}
comp-term-lemma (Comp pd A x x₁ ct cu σ₁) σ τ = {!!}

comp-lemma σ τ {⋆} = refl
comp-lemma σ τ {t ⟶ u} = trans-over-type (comp-lemma σ τ) (comp-term-lemma t σ τ) (comp-term-lemma u σ τ)

lifting-lemma σ {A} {⋆} = refl
lifting-lemma σ {A} {_⟶_ {A = C} t u} = trans-term-over-type (lifting-lemma σ) (t [ σ ]tm) (u [ σ ]tm)
