open import Catt.Typing.Rule

module Catt.Tree.Structured.Typing {index : Set}
                                   (rule : index → Rule) where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Bundles
open import Catt.Syntax.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Properties
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Structured.ToTerm

open import Catt.Typing rule
open import Catt.Typing.Properties.Base rule


stm-eq : {X : MaybeTree n} → (Γ : Ctx n) → STm X → STm X → Set
stm-eq Γ = Wrap (λ a b → stm-to-term a ≈[ Γ ]tm stm-to-term b)

sty-eq : {X : MaybeTree n} → (Γ : Ctx n) → STy X → STy X → Set
sty-eq Γ = Wrap (λ A B → sty-to-type A ≈[ Γ ]ty sty-to-type B)

syntax stm-eq ΓS a b = a ≈[ ΓS ]stm b
syntax sty-eq ΓS A B = A ≈[ ΓS ]sty B

refl≈stm : a ≈[ Γ ]stm a
refl≈stm = [ refl≈tm ]

sym≈stm : a ≈[ Γ ]stm b → b ≈[ Γ ]stm a
sym≈stm [ p ] = [ sym≈tm p ]

trans≈stm : a ≈[ Γ ]stm b → b ≈[ Γ ]stm c → a ≈[ Γ ]stm c
trans≈stm [ p ] [ q ] = [ trans≈tm p q ]

reflexive≈stm : a ≃stm b → a ≈[ Γ ]stm b
reflexive≈stm [ p ] = [ reflexive≈tm p ]

stm-setoid-≈ : {Γ : Ctx n} → {X : MaybeTree n} → Setoid _ _
stm-setoid-≈ {Γ = Γ} {X = X} = record { Carrier = STm X
                         ; _≈_ = λ x y → x ≈[ Γ ]stm y
                         ; isEquivalence = record { refl = refl≈stm
                                                  ; sym = sym≈stm
                                                  ; trans = trans≈stm
                                                  }
                         }

refl≈sty : As ≈[ Γ ]sty As
refl≈sty = [ refl≈ty ]

sym≈sty : As ≈[ Γ ]sty Bs → Bs ≈[ Γ ]sty As
sym≈sty [ p ] = [ sym≈ty p ]

trans≈sty : As ≈[ Γ ]sty Bs → Bs ≈[ Γ ]sty Cs → As ≈[ Γ ]sty Cs
trans≈sty [ p ] [ q ] = [ trans≈ty p q ]

reflexive≈sty : As ≃sty Bs → As ≈[ Γ ]sty Bs
reflexive≈sty [ p ] = [ reflexive≈ty p ]

sty-setoid-≈ : {Γ : Ctx n} → {X : MaybeTree n} → Setoid _ _
sty-setoid-≈ {Γ = Γ} {X = X} = record { Carrier = STy X
                         ; _≈_ = λ x y → x ≈[ Γ ]sty y
                         ; isEquivalence = record { refl = refl≈sty
                                                  ; sym = sym≈sty
                                                  ; trans = trans≈sty
                                                  }
                         }

≈SArr : a ≈[ Γ ]stm a′ → As ≈[ Γ ]sty Bs → b ≈[ Γ ]stm b′ → SArr a As b ≈[ Γ ]sty SArr a′ Bs b′
≈SArr [ p ] [ q ] [ r ] = [ Arr≈ p q r ]

≈SArr-proj₁ : SArr a As b ≈[ Γ ]sty SArr a′ Bs b′ → a ≈[ Γ ]stm a′
≈SArr-proj₁ [ Arr≈ p _ _ ] = [ p ]

≈SArr-proj₃ : SArr a As b ≈[ Γ ]sty SArr a′ Bs b′ → b ≈[ Γ ]stm b′
≈SArr-proj₃ [ Arr≈ _ _ p ] = [ p ]

label-max-equality : {X : MaybeTree n} → (ΓS : Ctx n) → (L M : Label X S) → Set
label-max-equality {S = S} Γ L M = Wrap (λ L M → ∀ (Q : Path S) → .⦃ is-Maximal Q ⦄ → L Q ≈[ Γ ]stm M Q) L M

syntax label-max-equality Γ L M = L ≈[ Γ ]lm M

refl≈lm : L ≈[ Γ ]lm L
refl≈lm .get Z = refl≈stm

label-equality : {X : MaybeTree n} → (Γ : Ctx n) → (L M : Label X S) → Set
label-equality {S = S} Γ L M = Wrap (λ L M → ∀ (Q : Path S) → L Q ≈[ Γ ]stm M Q) L M

syntax label-equality Γ L M = L ≈[ Γ ]l M

refl≈l : L ≈[ Γ ]l L
refl≈l .get Z = refl≈stm

reflexive≈l : L ≃l M → L ≈[ Γ ]l M
reflexive≈l [ p ] .get Z = reflexive≈stm (p Z)

compute-≈ : {a b : STm (someTree S)} → compute-stm a ≈[ tree-to-ctx S ]stm compute-stm b → a ≈[ tree-to-ctx S ]stm b
compute-≈ {a = a} {b = b} p = begin
  a
    ≈˘⟨ reflexive≈stm (compute-to-term a) ⟩
  compute-stm a
    ≈⟨ p ⟩
  compute-stm b
    ≈⟨ reflexive≈stm (compute-to-term b) ⟩
  b ∎
  where
    open Reasoning stm-setoid-≈

fixup-reflexive≈stm : {a : STm (someTree S)} → {b : STm (someTree T)} → a ≃stm b → (p : S ≃′ T) → a ≈[ tree-to-ctx S ]stm stm-≃ (sym≃′ p) b
fixup-reflexive≈stm {a = a} {b} q p = reflexive≈stm (begin
  < a >stm
    ≈⟨ q ⟩
  < b >stm
    ≈⟨ stm-≃-≃stm (sym≃′ p) b ⟩
  < stm-≃ (sym≃′ p) b >stm ∎)
  where
    open Reasoning stm-setoid

stm-≃-≈ : (p : S ≃′ T) → a ≈[ tree-to-ctx S ]stm b → stm-≃ p a ≈[ tree-to-ctx T ]stm stm-≃ p b
stm-≃-≈ {a = a} {b = b} p q with ≃-to-same-n (≃′-to-≃ p)
... | refl with ≃-to-≡ (≃′-to-≃ p)
... | refl = begin
  stm-≃ p a
    ≈˘⟨ reflexive≈stm (stm-≃-≃stm p a) ⟩
  a
    ≈⟨ q ⟩
  b
    ≈⟨ reflexive≈stm (stm-≃-≃stm p b) ⟩
  stm-≃ p b ∎
  where
    open Reasoning stm-setoid-≈

sty-dim-≈ : As ≈[ Γ ]sty Bs → sty-dim As ≡ sty-dim Bs
sty-dim-≈ {As = S⋆} {Bs = S⋆} [ p ] = refl
sty-dim-≈ {As = SArr _ As _} {Bs = SArr _ Bs _} [ Arr≈ _ p _ ] = cong suc (sty-dim-≈ [ p ])

sty-base-≈ : As ≈[ Γ ]sty Bs → sty-base As ≈[ Γ ]sty sty-base Bs
sty-base-≈ {As = S⋆} {Bs = S⋆} [ p ] = [ Star≈ ]
sty-base-≈ {As = SArr _ As _} {Bs = SArr _ Bs _} [ Arr≈ _ p _ ] = [ p ]

sty-src-≈ : {As Bs : STy X} → (p : As ≈[ Γ ]sty Bs) → .⦃ _ : NonZero (sty-dim As) ⦄ → sty-src As ≈[ Γ ]stm sty-src Bs ⦃ NonZero-subst (sty-dim-≈ p) it ⦄
sty-src-≈ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≈ p _ _ ] = [ p ]

sty-tgt-≈ : {As Bs : STy X} → (p : As ≈[ Γ ]sty Bs) → .⦃ _ : NonZero (sty-dim As) ⦄ → sty-tgt As ≈[ Γ ]stm sty-tgt Bs ⦃ NonZero-subst (sty-dim-≈ p) it ⦄
sty-tgt-≈ {As = SArr _ _ _} {Bs = SArr _ _ _} [ Arr≈ _ _ p ] = [ p ]

Typing-STm : {X : MaybeTree m} → (Γ : Ctx m) → STm X → STy X → Set
Typing-STy : {X : MaybeTree m} → (Γ : Ctx m) → STy X → Set
Typing-Label′ : {X : MaybeTree m} → (Γ : Ctx m) → Label-WT X S → Set
data Typing-Label : {X : MaybeTree m} → (Γ : Ctx m) → Label-WT X S → Set

Typing-STm Γ = Wrap (λ a As → Typing-Tm Γ (stm-to-term a) (sty-to-type As))

Typing-STy Γ = Wrap (λ As → Typing-Ty Γ (sty-to-type As))

Typing-Label′ {S = S} Γ = Wrap (λ L → Typing-Sub (tree-to-ctx S) Γ (label-to-sub L))

data Typing-Label where
  TySing : {L : Label-WT X Sing} → Typing-STm Γ (ap L PHere) (lty L) → Typing-Label Γ L
  TyJoin : {L : Label-WT X (Join S T)}
         → Typing-STm Γ (ap L PHere) (lty L)
         → Typing-Label Γ (label₁ L)
         → Typing-Label Γ (label₂ L)
         → Typing-Label Γ L

TySStar : Typing-STy Γ (S⋆ {X = X})
TySStar .get = TyStar

TySConv : Typing-STm Γ a As → As ≈[ Γ ]sty Bs → Typing-STm Γ a Bs
TySConv [ aty ] [ p ] = [ TyConv aty p ]

TySArr : Typing-STm Γ a As → Typing-STy Γ As → Typing-STm Γ b As → Typing-STy Γ (SArr a As b)
TySArr [ aty ] [ Asty ] [ bty ] .get = TyArr aty Asty bty

TySArr-proj₁ : Typing-STy Γ (SArr a As b) → Typing-STm Γ a As
TySArr-proj₁ [ TyArr x _ _ ] = [ x ]

TySArr-proj₂ : Typing-STy Γ As → Typing-STy Γ (sty-base As)
TySArr-proj₂ {As = S⋆} [ TyStar ] = TySStar
TySArr-proj₂ {As = SArr _ _ _} [ TyArr _ x _ ] = [ x ]

TySArr-proj₃ : Typing-STy Γ (SArr a As b) → Typing-STm Γ b As
TySArr-proj₃ [ TyArr _ _ x ] = [ x ]

ap-phere-Ty : {L : Label-WT X S} → Typing-Label Γ L → Typing-STm Γ (ap L PHere) (lty L)
ap-phere-Ty (TySing x) = x
ap-phere-Ty (TyJoin x Lty Mty) = x

transport-stm-typing : Typing-STm Γ a As → a ≃stm b → As ≃sty Bs → Typing-STm Γ b Bs
transport-stm-typing [ aty ] [ p ] [ q ] = [ transport-typing-full aty p q ]

transport-label-typing : {L : Label-WT X S} → {M : Label-WT Y S} → Typing-Label Γ L → proj₁ L ≃l proj₁ M → proj₂ L ≃sty proj₂ M → Typing-Label Γ M
transport-label-typing (TySing x) [ p ] q = TySing (transport-stm-typing x (p PHere) q)
transport-label-typing (TyJoin x Lty Lty′) [ p ] q
  = TyJoin (transport-stm-typing x (p PHere) q)
           (transport-label-typing Lty [ p ∘ PExt ] (SArr≃ (p PHere) q (p (PShift PHere))))
           (transport-label-typing Lty′ [ p ∘ PShift ] q)

label-typing-conv : Typing-Label Γ (L ,, As) → As ≈[ Γ ]sty Bs → Typing-Label Γ (L ,, Bs)
label-typing-conv (TySing x) p = TySing (TySConv x p)
label-typing-conv (TyJoin x LTy LTy′) p = TyJoin (TySConv x p) (label-typing-conv LTy (≈SArr refl≈stm p refl≈stm)) (label-typing-conv LTy′ p)

unrestrict-label-Ty : {L : Label-WT X S } → Typing-Label Γ L → Typing-STy Γ (lty L) → .⦃ _ : NonZero (sty-dim (lty L)) ⦄ → Typing-Label Γ (unrestrict-label L ,, sty-base (lty L))
unrestrict-label-Ty {L = L ,, SArr s As t} LTy AsTy = TyJoin (TySArr-proj₁ AsTy) LTy (TySing (TySArr-proj₃ AsTy))

extend-disc-label-Ty : {L : Label X (n-disc n)}
                     → Typing-Label Γ (L ,, As)
                     → Typing-STm Γ b (disc-type n >>=′ (L ,, As))
                     → Typing-STm Γ a (SArr (L (disc-path n))
                                            (disc-type n >>=′ (L ,, As))
                                            b)
                     → Typing-Label Γ (extend-disc-label L b a ,, As)
extend-disc-label-Ty {n = zero} (TySing x) bTy aTy = TyJoin x (TySing aTy) (TySing bTy)
extend-disc-label-Ty {n = suc n} (TyJoin x LTy (TySing y)) bTy aTy
  = TyJoin x
           (extend-disc-label-Ty
             LTy
             (transport-stm-typing bTy refl≃stm (map-sty-ext-label (disc-type n) (_ ,, _)))
             (transport-stm-typing aTy refl≃stm (SArr≃ refl≃stm
                                                       (map-sty-ext-label (disc-type n) (_ ,, _))
                                                       refl≃stm)))
           (TySing y)

term-to-label-Ty : Typing-STm Γ a As → Typing-STy Γ As → Typing-Label Γ (term-to-label a As ,, S⋆)
term-to-label-Ty {As = S⋆} aTy AsTy = TySing aTy
term-to-label-Ty {As = SArr s As t} aTy AsTy
  = extend-disc-label-Ty (term-to-label-Ty (TySArr-proj₁ AsTy) (TySArr-proj₂ AsTy))
                         (transport-stm-typing (TySArr-proj₃ AsTy) refl≃stm (sym≃sty (term-to-label-disc-type s As)))
                         (transport-stm-typing aTy refl≃stm (sym≃sty (SArr≃ (term-to-label-max s As)
                                                                            (term-to-label-disc-type s As)
                                                                            refl≃stm)))
