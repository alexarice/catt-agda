module Catt.Tree.Structured.ToTerm where

open import Catt.Prelude
open import Catt.Syntax
open import Catt.Suspension
open import Catt.Connection
open import Catt.Tree
open import Catt.Tree.Path
open import Catt.Tree.Structured

stm-to-term : {X : MaybeTree n} → STm X → Tm n
sty-to-type : {X : MaybeTree n} → STy X → Ty n
label-to-sub : {X : MaybeTree n} → (L : Label-WT X S) → Sub (suc (tree-size S)) n (sty-to-type (proj₂ L))

apt : {X : MaybeTree m} → Label-WT X S → Path S → Tm m
apt L P = stm-to-term (ap L P)

stm-to-term (SExt s) = susp-tm (stm-to-term s) [ connect-susp-inc-left _ _ ]tm
stm-to-term (SShift s) = stm-to-term s [ connect-susp-inc-right _ _ ]tm
stm-to-term (SPath P) = path-to-term P
stm-to-term (SCoh S A L) = Coh (tree-to-ctx S) (sty-to-type A) idSub [ label-to-sub L ]tm
stm-to-term (SOther t) = t

sty-to-type S⋆ = ⋆
sty-to-type (SArr s A t) = (stm-to-term s) ─⟨ (sty-to-type A) ⟩⟶ (stm-to-term t)

label-to-sub′ : ((P : Path S) → Tm n) → (A : Ty n) → Sub (suc (tree-size S)) n A
label-to-sub′ {S = Sing} f A = ⟨ ⟨⟩ , f PHere ⟩
label-to-sub′ {S = Join S₁ S₂} f A = sub-from-connect (unrestrict (label-to-sub′ (λ P → f (PExt P)) (f PHere ─⟨ A ⟩⟶ f (PShift PHere)))) (label-to-sub′ (λ P → f (PShift P)) A)

label-to-sub (L ,, A) = label-to-sub′ (λ P → stm-to-term (L P)) (sty-to-type A)

stm-to-other : STm X → STm (Other (maybeTreeSize X))
sty-to-other : STy X → STy (Other (maybeTreeSize X))
label-to-other : Label X S → Label (Other (maybeTreeSize X)) S
label-wt-to-other : Label-WT X S → Label-WT (Other (maybeTreeSize X)) S

stm-to-other s@(SExt _) = SOther (stm-to-term s)
stm-to-other s@(SShift _) = SOther (stm-to-term s)
stm-to-other s@(SPath _) = SOther (stm-to-term s)
stm-to-other (SCoh S A L) = SCoh S A (label-wt-to-other L)
stm-to-other (SOther t) = SOther t

sty-to-other S⋆ = S⋆
sty-to-other (SArr s As t) = SArr (stm-to-other s) (sty-to-other As) (stm-to-other t)

label-to-other L P = stm-to-other (L P)

label-wt-to-other (L ,, As) = (label-to-other L) ,, (sty-to-other As)

to-sty : Ty n → STy (Other n)
to-sty ⋆ = S⋆
to-sty (s ─⟨ A ⟩⟶ t) = SArr (SOther s) (to-sty A) (SOther t)

stm-sub : {X : MaybeTree n} → STm X → (σ : Sub n m B) → STm (Other m)
stm-sub a σ = SOther (stm-to-term a [ σ ]tm)

sty-sub : {X : MaybeTree n} → STy X → (σ : Sub n m B) → STy (Other m)
sty-sub {B = B} S⋆ σ = to-sty B
sty-sub (SArr s A t) σ = SArr (stm-sub s σ) (sty-sub A σ) (stm-sub t σ)

label-sub : {X : MaybeTree n} → Label-WT X S → (σ : Sub n m B) → Label-WT (Other m) S
label-sub L σ = (λ a → stm-sub a σ) ∘ ap L ,, sty-sub (lty L) σ

to-label-wt : (S : Tree n) → (σ : Sub (suc n) m A) → Label-WT (Other m) S
to-label-wt {A = A} S σ = label-sub (id-label-wt S) σ

to-label : (S : Tree n) → (σ : Sub (suc n) m A) → Label (Other m) S
to-label S σ = ap (to-label-wt S σ)
