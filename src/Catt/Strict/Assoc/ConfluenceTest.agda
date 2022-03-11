module Catt.Strict.Assoc.ConfluenceTest where

open import Catt.Prelude
open import Catt.Prelude.Properties
open import Catt.Syntax
open import Catt.Tree
open import Catt.Tree.Properties
open import Catt.Tree.Insertion

path-seperate : (S : Tree n) → Path S → Path S → Set
path-seperate (Join S T) PHere PHere = ⊥
path-seperate (Join S T) PHere (PExt Q) = ⊥
path-seperate (Join S T) PHere (PShift Q) = ⊤
path-seperate (Join S T) (PExt P) PHere = ⊥
path-seperate (Join S T) (PExt P) (PExt Q) = path-seperate S P Q
path-seperate (Join S T) (PExt P) (PShift Q) = ⊤
path-seperate (Join S T) (PShift P) PHere = ⊤
path-seperate (Join S T) (PShift P) (PExt Q) = ⊤
path-seperate (Join S T) (PShift P) (PShift Q) = path-seperate T P Q

path-seperate-sym : (S : Tree n) → (P Q : Path S) → path-seperate S P Q → path-seperate S Q P
path-seperate-sym (Join S T) PHere (PShift Q) p = tt
path-seperate-sym (Join S T) (PExt P) (PExt Q) p = path-seperate-sym S P Q p
path-seperate-sym (Join S T) (PExt P) (PShift Q) p = tt
path-seperate-sym (Join S T) (PShift P) PHere p = tt
path-seperate-sym (Join S T) (PShift P) (PExt Q) p = tt
path-seperate-sym (Join S T) (PShift P) (PShift Q) p = path-seperate-sym T P Q p

path-connect-tree-2 : (S : Tree n) → (T : Tree m) → Path T → Path (connect-tree S T)
path-connect-tree-2 Sing T P = P
path-connect-tree-2 (Join S₁ S₂) T P = PShift (path-connect-tree-2 S₂ T P)

path-connect-tree-2-length : (S : Tree n) → (T : Tree m) → (P : Path T) → path-length (path-connect-tree-2 S T P) ≡ path-length P
path-connect-tree-2-length Sing T P = refl
path-connect-tree-2-length (Join S₁ S₂) T P = path-connect-tree-2-length S₂ T P

path-in-insertion : (S : Tree n) → (P : Path S) → (T : Tree m) → .⦃ _ : has-linear-height (path-length P) T ⦄ → (Q : Path S) → (path-seperate S P Q) → Path (insertion-tree S P T)
path-in-insertion (Join S₁ S₂) PHere T (PShift Q) p = path-connect-tree-2 T S₂ Q
path-in-insertion (Join S₁ S₂) (PExt P) (Join T Sing) (PExt Q) p = PExt (path-in-insertion S₁ P T Q p)
path-in-insertion (Join S₁ S₂) (PExt P) (Join T Sing) (PShift Q) p = PShift Q
path-in-insertion (Join S₁ S₂) (PShift P) T PHere p = PHere
path-in-insertion (Join S₁ S₂) (PShift P) T (PExt Q) p = PExt Q
path-in-insertion (Join S₁ S₂) (PShift P) T (PShift Q) p = PShift (path-in-insertion S₂ P T Q p)

path-in-insertion-length : (S : Tree n)
                         → (P : Path S)
                         → (T : Tree m)
                         → .⦃ _ : has-linear-height (path-length P) T ⦄
                         → (Q : Path S)
                         → (p : path-seperate S P Q)
                         → path-length (path-in-insertion S P T Q p) ≡ path-length Q
path-in-insertion-length (Join S₁ S₂) PHere T (PShift Q) p = path-connect-tree-2-length T S₂ Q
path-in-insertion-length (Join S₁ S₂) (PExt P) (Join T Sing) (PExt Q) p = cong suc (path-in-insertion-length S₁ P T Q p)
path-in-insertion-length (Join S₁ S₂) (PExt P) (Join T Sing) (PShift Q) p = refl
path-in-insertion-length (Join S₁ S₂) (PShift P) T PHere p = refl
path-in-insertion-length (Join S₁ S₂) (PShift P) T (PExt Q) p = refl
path-in-insertion-length (Join S₁ S₂) (PShift P) T (PShift Q) p = path-in-insertion-length S₂ P T Q p

has-linear-height-≡ : (S : Tree n) → (l ≡ m) → has-linear-height l S → has-linear-height m S
has-linear-height-≡ S refl hlh = hlh

insertion-tree-connect-lem : (T : Tree n) → (S : Tree m) → (P : Path S) → (U : Tree l)
                           → .⦃ _ : has-linear-height (path-length P) U ⦄
                           → insertion-tree (connect-tree T S) (path-connect-tree-2 T S P) U ⦃ has-linear-height-≡ U (sym (path-connect-tree-2-length T S P)) it ⦄
                           ≃ connect-tree T (insertion-tree S P U)
insertion-tree-connect-lem Sing S P U = refl≃
insertion-tree-connect-lem (Join T₁ T₂) S P U = Join≃ refl≃ (insertion-tree-connect-lem T₂ S P U)

insertion-tree-comm : (S : Tree n)
                    → (P : Path S)
                    → (T : Tree m) → .⦃ _ : has-linear-height (path-length P) T ⦄
                    → (Q : Path S)
                    → (U : Tree l) → .⦃ _ : has-linear-height (path-length Q) U ⦄
                    → (p : path-seperate S P Q)
                    → insertion-tree (insertion-tree S P T) (path-in-insertion S P T Q p) U ⦃ has-linear-height-≡ U (sym (path-in-insertion-length S P T Q p)) it ⦄
                    ≃ insertion-tree (insertion-tree S Q U) (path-in-insertion S Q U P (path-seperate-sym S P Q p)) T ⦃ has-linear-height-≡ T (sym (path-in-insertion-length S Q U P (path-seperate-sym S P Q p))) it ⦄
insertion-tree-comm (Join S₁ S₂) PHere T (PShift Q) U p = insertion-tree-connect-lem T S₂ Q U
insertion-tree-comm (Join S₁ S₂) (PExt P) (Join T Sing) (PExt Q) (Join U Sing) p = Join≃ (insertion-tree-comm S₁ P T Q U p) refl≃
insertion-tree-comm (Join S₁ S₂) (PExt P) (Join T Sing) (PShift Q) U p = refl≃
insertion-tree-comm (Join S₁ S₂) (PShift P) T PHere U p = sym≃ (insertion-tree-connect-lem U S₂ P T)
insertion-tree-comm (Join S₁ S₂) (PShift P) T (PExt Q) (Join U Sing) p = refl≃
insertion-tree-comm (Join S₁ S₂) (PShift P) T (PShift Q) U p = Join≃ refl≃ (insertion-tree-comm S₂ P T Q U p)
