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
open import Catt.Tree.Canonical
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

ih′ : {T : Tree n} → (p : Branch T d) → ℕ
ih′ {T = Join S T} (BHere) = tree-dim S
ih′ (BExt P) = suc (ih′ P)
ih′ (BShift P) = ih′ P

ih : {T : Tree n} → (p : Branch T d) → ℕ
ih p = suc (ih′ p)

⌊_⌋p : (p : Branch T d) → Path T
⌊_⌋p {T = Join S T} BHere = PExt (is-linear-max-path S)
⌊_⌋p {T = Join S T} (BExt p) = PExt ⌊ p ⌋p
⌊_⌋p {T = Join S T} (BShift p) = PShift ⌊ p ⌋p

branch-type : (T : Tree n) → (P : Branch T d) → STy (someTree T)
branch-type (Join S T) (BHere) = map-sty-ext (disc-sty S)
branch-type (Join S T) (BExt P) = map-sty-ext (branch-type S P)
branch-type (Join S T) (BShift P) = map-sty-shift (branch-type T P)

insertion-tree-size :  (S : Tree n) → (p : Branch S d) → (T : Tree m) → .⦃ has-trunk-height d T ⦄ → ℕ
insertion-tree : (S : Tree n) → (p : Branch S d) → (T : Tree m) → .⦃ _ : has-trunk-height d T ⦄ → Tree (insertion-tree-size S p T)

insertion-tree-size {m = m} (Join S₁ S₂) (BHere) T = ++t-length T S₂
insertion-tree-size (Join {m = m} S₁ S₂) (BExt P) (Susp T) = m + suc (suc (insertion-tree-size S₁ P T))
insertion-tree-size (Join {n = n} S₁ S₂) (BShift P) T = insertion-tree-size S₂ P T + suc (suc n)

insertion-tree (Join S₁ S₂) (BHere) T = T ++t S₂
insertion-tree (Join S₁ S₂) (BExt P) (Susp T) = Join (insertion-tree S₁ P T) S₂
insertion-tree (Join S₁ S₂) (BShift P) T = Join S₁ (insertion-tree S₂ P T)

ι : (S : Tree n)
               → (p : Branch S d)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height d T ⦄
               → Label (someTree (insertion-tree S p T)) T
ι (Join S₁ S₂) BHere T = ap (++t-inc-left T S₂)
ι (Join S₁ S₂) (BExt p) (Susp T) = unrestrict-label (map-ext (ι S₁ p T ,, S⋆))
ι (Join S₁ S₂) (BShift p) T P = SShift (ι S₂ p T P)

κ′ : (S : Tree n)
                → (p : Branch S d)
                → (T : Tree m)
                → .⦃ _ : has-trunk-height d T ⦄
                → (As : STy (someTree (chop-trunk d T)))
                → .⦃ has-dim (ih p ∸ d) As ⦄
                → Label (someTree (insertion-tree S p T)) S
κ′ (Join S₁ S₂) BHere T As
  = label-between-++t (replace-label (stm-to-label (Susp S₁) (sty-to-coh As) As) SHere) SPath
κ′ (Join S₁ S₂) (BExt p) (Susp T) As
  = label-between-joins (κ′ S₁ p T As) SPath
κ′ (Join S₁ S₂) (BShift p) T A
  = label-between-joins SPath (κ′ S₂ p T A)

κ : (S : Tree n)
               → (p : Branch S d)
               → (T : Tree m)
               → .⦃ _ : has-trunk-height d T ⦄
               → Label (someTree (insertion-tree S p T)) S
κ (Join S₁ S₂) BHere T
  = label-between-++t (replace-label (canonical-label (Susp S₁) T) SHere) SPath
κ (Join S₁ S₂) (BExt p) (Susp T)
  = label-between-joins (κ S₁ p T) SPath
κ (Join S₁ S₂) (BShift p) T
  = label-between-joins SPath (κ S₂ p T)

label-from-insertion : (S : Tree n)
                     → (p : Branch S d)
                     → (T : Tree m)
                     → .⦃ _ : has-trunk-height d T ⦄
                     → (L : Label X S)
                     → (M : Label X T)
                     → Label X (insertion-tree S p T)
label-from-insertion (Join S₁ S₂) BHere T L M = M ++l (L ∘ PShift)
label-from-insertion (Join S₁ S₂) (BExt p) (Susp T) L M PHere = M PHere
label-from-insertion (Join S₁ S₂) (BExt p) (Susp T) L M (PExt Z) = label-from-insertion S₁ p T (L ∘ PExt) (M ∘ PExt) Z
label-from-insertion (Join S₁ S₂) (BExt p) (Susp T) L M (PShift Z) = replace-label (L ∘ PShift) (M (PShift PHere)) Z
label-from-insertion (Join S₁ S₂) (BShift p) T L M PHere = L PHere
label-from-insertion (Join S₁ S₂) (BShift p) T L M (PExt Z) = L (PExt Z)
label-from-insertion (Join S₁ S₂) (BShift p) T L M (PShift Z) = label-from-insertion S₂ p T (L ∘ PShift) M Z

label-from-insertion′ : (S : Tree n)
                      → (p : Branch S d)
                      → (T : Tree m)
                      → .⦃ _ : has-trunk-height d T ⦄
                      → (L : Label X S)
                      → (M : Label X T)
                      → Label X (insertion-tree S p T)
label-from-insertion′ (Join S₁ S₂) BHere T L M = replace-label (M ++l′ (L ∘ PShift)) (L PHere)
label-from-insertion′ (Join S₁ S₂) (BExt p) (Susp T) L M PHere = L PHere
label-from-insertion′ (Join S₁ S₂) (BExt p) (Susp T) L M (PExt Z) = label-from-insertion′ S₁ p T (L ∘ PExt) (M ∘ PExt) Z
label-from-insertion′ (Join S₁ S₂) (BExt p) (Susp T) L M (PShift Z) = L (PShift Z)
label-from-insertion′ (Join S₁ S₂) (BShift p) T L M PHere = L PHere
label-from-insertion′ (Join S₁ S₂) (BShift p) T L M (PExt Z) = L (PExt Z)
label-from-insertion′ (Join S₁ S₂) (BShift p) T L M (PShift Z) = label-from-insertion′ S₂ p T (L ∘ PShift) M Z

bh-<-ih : (p : Branch S d) → d < ih p
bh-<-ih BHere = s≤s z≤n
bh-<-ih (BExt p) = s≤s (bh-<-ih p)
bh-<-ih (BShift p) = bh-<-ih p

prune-tree-lem : (S : Tree n)
               → (p : Branch S d)
               → has-trunk-height d (n-disc (pred (ih p)))
prune-tree-lem S p = has-trunk-height-n-disc (≤-pred (bh-<-ih p))

prune-tree : (S : Tree n)
           → (p : Branch S d)
           → Tree (insertion-tree-size S p (n-disc (pred (ih p))) ⦃ prune-tree-lem S p ⦄)
prune-tree S p = insertion-tree S p (n-disc (pred (ih p))) ⦃ prune-tree-lem S p ⦄

label-from-prune : (S : Tree n)
                 → (p : Branch S d)
                 → (L : Label X S)
                 → (M : Label X (n-disc (pred (ih p))))
                 → Label X (prune-tree S p)
label-from-prune S p L M = label-from-insertion S p (n-disc (pred (ih p))) ⦃ prune-tree-lem S p ⦄ L M

module _ where
  open ≡-Reasoning
  κ-prune : (S : Tree n)
              → (p : Branch S d)
              → Label (someTree (prune-tree S p)) S
  κ-prune {d = d} S p = let
    instance _ = prune-tree-lem S p
    in κ S p (n-disc (pred (ih p)))
