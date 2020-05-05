-- pdb-src-i< : {n : ℕ} → {Γ : Ctx} → {A : Ty Γ} → {x : Term Γ A} → PDB (suc (suc n)) Γ x → PDB (suc n) Γ x
-- pdb-src-i≡ : {Γ : Ctx} → {A : Ty Γ} → {x : Term Γ A} → PDB 1 Γ x → PDB 0 Γ x

-- pdb-bd : (Γ : Ctx) → {A : Ty Γ n} → {x : Term Γ A} → PDB submax Γ x → Ctx
-- boundary-typing : {A : Ty Γ n} → {x : Term Γ A} → (pdb : PDB (suc submax) Γ x) → Ty (pdb-bd Γ pdb) n
-- boundary-term : {A : Ty Γ n} → {x : Term Γ A} → (pdb : PDB (suc submax) Γ x) → Term (pdb-bd Γ pdb) (boundary-typing pdb)

-- pdb-bd Γ Base = Γ
-- pdb-bd (Γ , _ , (Gen _ _ ⟶ Var _)) (ExtendMax pdb) = Γ
-- pdb-bd {submax = zero} (Γ , _ , (Gen _ _ ⟶ Var _)) (ExtendNM pdb) = pdb-bd Γ pdb
-- pdb-bd {submax = suc n} (Γ , _ , _) (ExtendNM pdb) = pdb-bd Γ pdb , boundary-typing pdb , ((Gen (boundary-term pdb) (boundary-typing pdb)) ⟶ Var (boundary-typing pdb))
-- pdb-bd Γ (Restr pdb) = pdb-bd Γ pdb


-- boundary-typing (ExtendNM pdb) = let A = (Gen (boundary-term pdb) (boundary-typing pdb)) ⟶ (Var (boundary-typing pdb))
--   in liftType A A
-- boundary-typing {submax = zero} (Restr (ExtendMax {A = A} pdb)) = A
-- boundary-typing {submax = zero} (Restr (ExtendNM pdb)) = boundary-typing pdb
-- boundary-typing {submax = suc n} (Restr pdb) = ty-base (boundary-typing pdb)

-- boundary-term (ExtendNM pdb) = Var (Gen (boundary-term pdb) (boundary-typing pdb) ⟶
--                                      Var (boundary-typing pdb))
-- boundary-term {submax = zero} (Restr (ExtendMax {x = x} pdb)) = x
-- boundary-term {submax = zero} (Restr (ExtendNM pdb)) = boundary-term pdb
-- boundary-term {submax = suc n} (Restr pdb) = ty-tgt (boundary-typing pdb)

-- pd-bd Γ (Finish x) = pdb-bd Γ x

-- bd-is-pdb≤ : {A : Ty Γ n} → {x : Term Γ A} → (pdb : PDB (suc submax) Γ x) → PDB submax (pdb-bd Γ pdb) (boundary-term pdb)
-- bd-is-pdb> : {A : Ty Γ (suc n)} {x : Term Γ A} → (pdb : PDB 0 Γ x) → PDB 0 (pdb-bd Γ pdb) (boundary-term (Restr pdb))

-- bd-is-pdb≤ (ExtendNM pdb) = ExtendNM (bd-is-pdb≤ pdb)
-- bd-is-pdb≤ {submax = zero} (Restr pdb) = bd-is-pdb> pdb
-- bd-is-pdb≤ {submax = suc n} (Restr pdb) = Restr (bd-is-pdb≤ pdb)

-- bd-is-pdb> (ExtendMax pdb) = pdb
-- bd-is-pdb> (ExtendNM pdb) = bd-is-pdb≤ pdb

-- bd-is-pd : (pd : PD Γ (suc n)) → PD (pd-bd Γ pd) n
-- bd-is-pd {Γ} {n} (Finish pdb) with boundary-typing pdb | boundary-term pdb | bd-is-pdb≤ pdb
-- ... | ⋆ | x | pd = Finish pd

-- src-substitution-b : {A : Ty Γ n} → {x : Term Γ A} → (pdb : PDB submax Γ x) → Substitution Γ (pdb-bd Γ pdb)
-- boundary-typing-lemma-src : {A : Ty Γ n} → {x : Term Γ A} → (pdb : PDB (suc submax) Γ x) → boundary-typing pdb [ src-substitution-b pdb ]ty ≡ A
-- boundary-term-lemma-src : {A : Ty Γ n} → {x : Term Γ A} → (pdb : PDB (suc submax) Γ x) → transport (cong (Term _) (boundary-typing-lemma-src pdb)) (boundary-term pdb [ src-substitution-b pdb ]tm) ≡ x
-- src-substitution-b Base = ⟨ ⟨⟩ , (Var ⋆) ⟩
-- src-substitution-b (ExtendMax pdb) = si (si (id _))
-- src-substitution-b {submax = zero} (ExtendNM pdb) = si (si (src-substitution-b pdb))

-- src-substitution-b {submax = suc n} (ExtendNM {x = x} pdb) with pdb-bd _ pdb | src-substitution-b pdb | boundary-typing pdb | boundary-typing-lemma-src pdb | boundary-term pdb | boundary-term-lemma-src pdb
-- ... | pd | σ | B | refl | z | refl = ⟨ ⟨ si (si σ) , α ⟩ , β ⟩
--   where
--     α : Term (_ , (B [ σ ]ty) , (Gen x (B [ σ ]ty) ⟶ Var (B [ σ ]ty)))
--           (B [ si (si σ) ]ty)
--     α rewrite si-lemma (si σ) (Gen x (B [ σ ]ty) ⟶ Var (B [ σ ]ty)) B rewrite si-lemma σ (B [ σ ]ty) B = Gen (Gen x (B [ σ ]ty)) (Gen x (B [ σ ]ty) ⟶ Var (B [ σ ]ty))
--     β : Term (_ , (B [ σ ]ty) , (Gen x (B [ σ ]ty) ⟶ Var (B [ σ ]ty)))
--           ((Gen z B ⟶ Var B) [ ⟨ si (si σ) , α ⟩ ]ty)
--     β = {!!}
-- ⟨ ⟨ (si (si ω)) , (si-lemma _ (si-lemma _ x)) ⟩ , {!!} ⟩
--  ⟨ ⟨ si (si (src-substitution-b pdb)) , si-lemma (si (src-substitution-b pdb)) (si-lemma (src-substitution-b pdb) {!!}) ⟩ , {!!} ⟩
-- src-substitution-b (Restr pdb) = src-substitution-b pdb

-- boundary-typing-lemma-src pdb = {!!}
-- boundary-term-lemma-src = {!!}
