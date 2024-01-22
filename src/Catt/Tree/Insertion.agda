module Catt.Tree.Insertion where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Syntax.Properties
open import Catt.Variables
open import Catt.Variables.Properties
open import Catt.Suspension
open import Catt.Connection
open import Catt.Connection.Properties
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Standard
open import Catt.Tree.Path
open import Catt.Tree.Structured
open import Catt.Tree.Structured.Globular
open import Catt.Tree.Structured.Construct
open import Catt.Tree.Structured.Construct.Properties
open import Catt.Tree.Structured.ToTerm

data Branch : Tree n → ℕ → Set where
  BHere : .⦃ is-linear S ⦄ → Branch (Join S T) 0
  BExt : Branch S n → Branch (Join S T) (suc n)
  BShift : Branch T n → Branch (Join S T) n

bh : Branch S d → ℕ
bh {d = d} p = d

lh′ : {T : Tree n} → (p : Branch T d) → ℕ
lh′ {T = Join S T} BHere = tree-dim S
lh′ (BExt P) = suc (lh′ P)
lh′ (BShift P) = lh′ P

lh : {T : Tree n} → (p : Branch T d) → ℕ
lh p = suc (lh′ p)

⌊_⌋p : (p : Branch T d) → Path T
⌊_⌋p {T = Join S T} BHere = PExt (is-linear-max-path S)
⌊_⌋p {T = Join S T} (BExt p) = PExt ⌊ p ⌋p
⌊_⌋p {T = Join S T} (BShift p) = PShift ⌊ p ⌋p

branch-type : (T : Tree n) → (P : Branch T d) → STy (someTree T)
branch-type (Join S T) BHere = map-sty-ext (disc-sty S)
branch-type (Join S T) (BExt P) = map-sty-ext (branch-type S P)
branch-type (Join S T) (BShift P) = map-sty-shift (branch-type T P)

infix 5 _>>[_]_
insertion-size :  (S : Tree n) → (p : Branch S d) → (T : Tree m) → .⦃ has-trunk-height d T ⦄ → ℕ
_>>[_]_ : (S : Tree n) → (p : Branch S d) → (T : Tree m) → .⦃ _ : has-trunk-height d T ⦄ → Tree (insertion-size S p T)

insertion-size {m = m} (Join S₁ S₂) BHere T = ++t-length T S₂
insertion-size (Join {m = m} S₁ S₂) (BExt P) (Susp T) = m + suc (suc (insertion-size S₁ P T))
insertion-size (Join {n = n} S₁ S₂) (BShift P) T = insertion-size S₂ P T + suc (suc n)

Join S₁ S₂ >>[ BHere ] T = T ++t S₂
Join S₁ S₂ >>[ BExt P ] (Susp T) = Join (S₁ >>[ P ] T) S₂
Join S₁ S₂ >>[ BShift P ] T = Join S₁ (S₂ >>[ P ] T)

ι : (S : Tree n)
  → (P : Branch S d)
  → (T : Tree m)
  → .⦃ _ : has-trunk-height d T ⦄
  → Label (someTree (S >>[ P ] T)) T
ι (Join S₁ S₂) BHere T = ap (++t-inc-left T S₂)
ι (Join S₁ S₂) (BExt P) (Susp T) = unrestrict-label (map-ext (ι S₁ P T ,, S⋆))
ι (Join S₁ S₂) (BShift P) T Z = SShift (ι S₂ P T Z)

κ′ : (S : Tree n)
   → (P : Branch S d)
   → (T : Tree m)
   → .⦃ _ : has-trunk-height d T ⦄
   → (As : STy (someTree (chop-trunk d T)))
   → .⦃ has-dim (lh P ∸ d) As ⦄
   → Label (someTree (S >>[ P ] T)) S
κ′ (Join S₁ S₂) BHere T As
  = label-between-++t (replace-label (stm-to-label (Susp S₁) (sty-to-coh As) As) SHere) SPath
κ′ (Join S₁ S₂) (BExt P) (Susp T) As
  = label-between-joins (κ′ S₁ P T As) SPath
κ′ (Join S₁ S₂) (BShift P) T A
  = label-between-joins SPath (κ′ S₂ P T A)

κ : (S : Tree n)
  → (P : Branch S d)
  → (T : Tree m)
  → .⦃ _ : has-trunk-height d T ⦄
  → Label (someTree (S >>[ P ] T)) S
κ (Join S₁ S₂) BHere T
  = label-between-++t (replace-label (standard-label (Susp S₁) T) SHere) SPath
κ (Join S₁ S₂) (BExt P) (Susp T)
  = label-between-joins (κ S₁ P T) SPath
κ (Join S₁ S₂) (BShift P) T
  = label-between-joins SPath (κ S₂ P T)

infix 5 _>>l[_]_ _>>l′[_]_
_>>l[_]_ : (L : Label X S)
         → (p : Branch S d)
         → (M : Label X T)
         → .⦃ _ : has-trunk-height d T ⦄
         → Label X (S >>[ p ] T)
_>>l[_]_ L BHere M = M ++l (L ∘ PShift)
_>>l[_]_ {T = Susp T} L (BExt P) M PHere = M PHere
_>>l[_]_ {T = Susp T} L (BExt P) M (PExt Z) = (L ∘ PExt >>l[ P ] M ∘ PExt) Z
_>>l[_]_ {T = Susp T} L (BExt P) M (PShift Z) = replace-label (L ∘ PShift) (M (PShift PHere)) Z
_>>l[_]_ L (BShift P) M PHere = L PHere
_>>l[_]_ L (BShift P) M (PExt Z) = L (PExt Z)
_>>l[_]_ L (BShift P) M (PShift Z) = (L ∘ PShift >>l[ P ] M) Z

_>>l′[_]_ : (L : Label X S)
          → (P : Branch S d)
          → (M : Label X T)
          → .⦃ _ : has-trunk-height d T ⦄
          → Label X (S >>[ P ] T)
_>>l′[_]_ L BHere M = replace-label (M ++l′ (L ∘ PShift)) (L PHere)
_>>l′[_]_ {T = Susp T} L (BExt P) M PHere = L PHere
_>>l′[_]_ {T = Susp T} L (BExt P) M (PExt Z) = (L ∘ PExt >>l′[ P ] M ∘ PExt) Z
_>>l′[_]_ {T = Susp T} L (BExt P) M (PShift Z) = L (PShift Z)
_>>l′[_]_ L (BShift P) M PHere = L PHere
_>>l′[_]_ L (BShift P) M (PExt Z) = L (PExt Z)
_>>l′[_]_ L (BShift P) M (PShift Z) = (L ∘ PShift >>l′[ P ] M) Z

bh-<-lh : (p : Branch S d) → d < lh p
bh-<-lh BHere = s≤s z≤n
bh-<-lh (BExt p) = s≤s (bh-<-lh p)
bh-<-lh (BShift p) = bh-<-lh p

prune-lem : (P : Branch S d)
          → has-trunk-height d (n-disc (pred (lh P)))
prune-lem P = has-trunk-height-n-disc (≤-pred (bh-<-lh P))

infix 5 _//t_
_//t_ : (S : Tree n)
      → (P : Branch S d)
      → Tree (insertion-size S P (n-disc (pred (lh P))) ⦃ prune-lem P ⦄)
S //t p = (S >>[ p ] (n-disc (pred (lh p)))) ⦃ prune-lem p ⦄

infix 5 _>>p[_]_
_>>p[_]_ : (L : Label X S)
         → (P : Branch S d)
         → (M : Label X (n-disc (pred (lh P))))
         → Label X (S //t P)
L >>p[ P ] M = (L >>l[ P ] M) ⦃ prune-lem P ⦄

πt : (P : Branch S d)
   → Label (someTree (S //t P)) S
πt P = let
  instance _ = prune-lem P
  in κ _ P (n-disc (pred (lh P)))
