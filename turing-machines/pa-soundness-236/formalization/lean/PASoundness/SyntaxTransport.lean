import PASoundness.FOL

/-! Structural substitution identities for the canonical first-order syntax.
These are equalities of finite syntax trees, not semantic equivalences. -/
namespace PASoundness.SyntaxTransport
open FirstOrder FirstOrder.Language
variable {L : Language} {α β γ : Type}

@[simp] theorem term_subst_var (t : L.Term α) : t.subst Term.var = t := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.subst,ih]

theorem term_subst_comp (t : L.Term α) (σ : α → L.Term β) (τ : β → L.Term γ) :
    (t.subst σ).subst τ = t.subst (fun a => (σ a).subst τ) := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.subst,ih]

theorem term_relabel_subst (t : L.Term α) (r : α → β) (σ : β → L.Term γ) :
    (t.relabel r).subst σ = t.subst (σ ∘ r) := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.relabel,Term.subst,ih]

theorem term_subst_relabel (t : L.Term α) (σ : α → L.Term β) (r : β → γ) :
    (t.subst σ).relabel r = t.subst (fun a => (σ a).relabel r) := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.relabel,Term.subst,ih]

def liftSub (n : Nat) (σ : α → L.Term β) : α ⊕ Fin n → L.Term (β ⊕ Fin n) :=
  Sum.elim (Term.relabel Sum.inl ∘ σ) (Term.var ∘ Sum.inr)

theorem liftSub_comp (n : Nat) (σ : α → L.Term β) (τ : β → L.Term γ) (x : α ⊕ Fin n) :
    (liftSub n σ x).subst (liftSub n τ) = liftSub n (fun a => (σ a).subst τ) x := by
  cases x with
  | inl a =>
    simp only [liftSub,Sum.elim_inl,Function.comp_apply,term_relabel_subst,term_subst_relabel]
    rfl
  | inr a => rfl

@[simp] theorem formula_subst_var {n : Nat} (φ : L.BoundedFormula α n) :
    φ.subst Term.var = φ := by
  unfold BoundedFormula.subst
  have ht : (fun (n : Nat) (t : L.Term (α ⊕ Fin n)) =>
      t.subst (Sum.elim (Term.relabel Sum.inl ∘ Term.var) (Term.var ∘ Sum.inr))) =
      (fun _ => id) := by
    funext n t
    have he : (Sum.elim (Term.relabel Sum.inl ∘ Term.var) (Term.var ∘ Sum.inr) :
      α ⊕ Fin n → L.Term (α ⊕ Fin n)) = Term.var := by
      funext x; cases x <;> rfl
    rw [he,term_subst_var]
    rfl
  rw [ht,BoundedFormula.mapTermRel_id_id_id]

theorem formula_subst_comp {n : Nat} (φ : L.BoundedFormula α n)
    (σ : α → L.Term β) (τ : β → L.Term γ) :
    (φ.subst σ).subst τ = φ.subst (fun a => (σ a).subst τ) := by
  simp only [BoundedFormula.subst,BoundedFormula.mapTermRel_mapTermRel]
  congr 1
  funext n t
  change (t.subst (liftSub n σ)).subst (liftSub n τ) =
    t.subst (liftSub n (fun a => (σ a).subst τ))
  rw [term_subst_comp]
  congr 1
  funext x
  exact liftSub_comp n σ τ x

@[simp] theorem substAt_self (φ : FOL.Formula L) (x : Nat) :
    FOL.substAt φ x (.var x) = φ := by
  unfold FOL.substAt
  have h : (fun y => if y = x then (Term.var x : L.Term Nat) else .var y) = Term.var := by
    funext y
    split <;> simp_all
  rw [h,formula_subst_var]

theorem term_bind_freeVars {n : Nat} (t : L.Term (Nat ⊕ Fin n)) (x y : Nat) :
    y ∈ (t.relabel (BoundedFormula.relabelAux
      (fun z => if z = x then Sum.inr (0 : Fin 1) else Sum.inl z) n)).varFinsetLeft ↔
      y ≠ x ∧ y ∈ t.varFinsetLeft := by
  induction t with
  | var z =>
    cases z with
    | inl z =>
      by_cases hz : z = x <;>
        simp [Term.relabel,BoundedFormula.relabelAux,Term.varFinsetLeft,hz] <;> aesop
    | inr z => simp [Term.relabel,BoundedFormula.relabelAux,Term.varFinsetLeft]
  | func f ts ih =>
    simp only [Term.relabel,Term.varFinsetLeft,Finset.mem_biUnion,
      Finset.mem_univ,true_and,ih]
    constructor
    · rintro ⟨i,hy,hi⟩; exact ⟨hy,i,hi⟩
    · rintro ⟨hy,i,hi⟩; exact ⟨i,hy,hi⟩

theorem relabel_bind_freeVars {n : Nat} (φ : L.BoundedFormula Nat n) (x : Nat) :
    (φ.relabel (fun z => if z = x then Sum.inr (0 : Fin 1) else Sum.inl z)).freeVarFinset =
      φ.freeVarFinset.erase x := by
  induction φ with
  | falsum => simp
  | equal t u =>
    ext y
    simp only [BoundedFormula.relabel,BoundedFormula.mapTermRel,
      BoundedFormula.freeVarFinset,Finset.mem_union,term_bind_freeVars,Finset.mem_erase]
    tauto
  | rel r ts =>
    ext y
    simp only [BoundedFormula.relabel,BoundedFormula.mapTermRel,
      BoundedFormula.freeVarFinset,Finset.mem_biUnion,Finset.mem_univ,true_and,
      term_bind_freeVars,Finset.mem_erase]
    constructor
    · rintro ⟨i,hy,hi⟩; exact ⟨hy,i,hi⟩
    · rintro ⟨hy,i,hi⟩; exact ⟨i,hy,hi⟩
  | imp a b ia ib =>
    simp only [BoundedFormula.relabel_imp,BoundedFormula.freeVarFinset,ia,ib]
    ext y
    simp only [Finset.mem_union,Finset.mem_erase]
    tauto
  | all f ih => simpa only [BoundedFormula.relabel_all,BoundedFormula.freeVarFinset] using ih

@[simp] theorem allAt_freeVars (φ : FOL.Formula L) (x : Nat) :
    (FOL.allAt x φ).freeVarFinset = φ.freeVarFinset.erase x :=
  relabel_bind_freeVars φ x

@[simp] theorem term_relabel_inl_vars {n : Nat} (t : L.Term Nat) :
    (t.relabel (Sum.inl : Nat → Nat ⊕ Fin n)).varFinsetLeft = t.varFinset := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.relabel,Term.varFinsetLeft,Term.varFinset,ih]

theorem term_liftSub_freeVars {n : Nat} (t : L.Term (Nat ⊕ Fin n))
    (σ : Nat → L.Term Nat) (x : Nat) :
    x ∈ (t.subst (liftSub n σ)).varFinsetLeft ↔
      ∃ y ∈ t.varFinsetLeft, x ∈ (σ y).varFinset := by
  induction t with
  | var z =>
    cases z <;> simp [Term.subst,liftSub]
  | func f ts ih =>
    simp only [Term.subst,Term.varFinsetLeft,Finset.mem_biUnion,
      Finset.mem_univ,true_and,ih]
    constructor
    · rintro ⟨i,y,hy,hx⟩; exact ⟨y,⟨i,hy⟩,hx⟩
    · rintro ⟨y,⟨i,hy⟩,hx⟩; exact ⟨i,y,hy,hx⟩

theorem formula_subst_freeVars {n : Nat} (φ : L.BoundedFormula Nat n)
    (σ : Nat → L.Term Nat) (x : Nat) :
    x ∈ (φ.subst σ).freeVarFinset ↔
      ∃ y ∈ φ.freeVarFinset, x ∈ (σ y).varFinset := by
  induction φ with
  | falsum => simp [BoundedFormula.subst,BoundedFormula.mapTermRel]
  | equal t u =>
    change (x ∈ (t.subst (liftSub _ σ)).varFinsetLeft ∪
      (u.subst (liftSub _ σ)).varFinsetLeft) ↔ _
    simp only [Finset.mem_union,term_liftSub_freeVars,BoundedFormula.freeVarFinset]
    aesop
  | rel r ts =>
    change (x ∈ Finset.univ.biUnion (fun i => (ts i |>.subst (liftSub _ σ)).varFinsetLeft)) ↔ _
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,term_liftSub_freeVars,
      BoundedFormula.freeVarFinset]
    constructor
    · rintro ⟨i,y,hy,hx⟩; exact ⟨y,⟨i,hy⟩,hx⟩
    · rintro ⟨y,⟨i,hy⟩,hx⟩; exact ⟨i,y,hy,hx⟩
  | imp a b ia ib =>
    change (x ∈ (a.subst σ).freeVarFinset ∪ (b.subst σ).freeVarFinset) ↔ _
    simp only [Finset.mem_union,ia,ib,BoundedFormula.freeVarFinset]
    aesop
  | all f ih => exact ih

theorem term_liftSub_agree {n : Nat} (t : L.Term (Nat ⊕ Fin n))
    (σ τ : Nat → L.Term β) (h : ∀ x ∈ t.varFinsetLeft, σ x = τ x) :
    t.subst (liftSub n σ) = t.subst (liftSub n τ) := by
  induction t with
  | var z =>
    cases z with
    | inl x =>
      have hx := h x (by simp)
      simpa only [Term.subst,liftSub,Sum.elim_inl,Function.comp_apply,hx]
    | inr x => rfl
  | func f ts ih =>
    simp only [Term.subst]
    congr 1
    funext i
    apply ih i
    intro x hx
    exact h x (by simp only [Term.varFinsetLeft,Finset.mem_biUnion]; exact ⟨i,by simp,hx⟩)

theorem formula_subst_agree {n : Nat} (φ : L.BoundedFormula Nat n)
    (σ τ : Nat → L.Term β) (h : ∀ x ∈ φ.freeVarFinset, σ x = τ x) :
    φ.subst σ = φ.subst τ := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change BoundedFormula.equal (t.subst (liftSub _ σ)) (u.subst (liftSub _ σ)) =
      BoundedFormula.equal (t.subst (liftSub _ τ)) (u.subst (liftSub _ τ))
    congr 1
    · apply term_liftSub_agree
      intro x hx
      exact h x (Finset.mem_union_left _ hx)
    · apply term_liftSub_agree
      intro x hx
      exact h x (Finset.mem_union_right _ hx)
  | rel r ts =>
    change BoundedFormula.rel r (fun i => (ts i).subst (liftSub _ σ)) =
      BoundedFormula.rel r (fun i => (ts i).subst (liftSub _ τ))
    congr 1
    funext i
    apply term_liftSub_agree
    intro x hx
    exact h x (by simp only [BoundedFormula.freeVarFinset,Finset.mem_biUnion]; exact ⟨i,by simp,hx⟩)
  | imp a b ia ib =>
    change (a.subst σ).imp (b.subst σ) = (a.subst τ).imp (b.subst τ)
    congr 1
    · apply ia
      intro x hx
      exact h x (Finset.mem_union_left _ hx)
    · apply ib
      intro x hx
      exact h x (Finset.mem_union_right _ hx)
  | all f ih =>
    change (f.subst σ).all = (f.subst τ).all
    exact congrArg BoundedFormula.all (ih h)

theorem term_relabel_as_subst (t : L.Term α) (r : α → β) :
    t.relabel r = t.subst (Term.var ∘ r) := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.relabel,Term.subst,ih]

theorem term_relabel_zero_as_subst {n : Nat} (t : L.Term (α ⊕ Fin n))
    (r : α → β) (h : n ≤ 0 + n) :
    t.relabel (BoundedFormula.relabelAux (Sum.inl ∘ r) n) =
      (t.subst (liftSub n (Term.var ∘ r))).relabel (Sum.map id (Fin.castLE h)) := by
  rw [term_relabel_as_subst,term_subst_relabel]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr x =>
    change Term.var (Sum.inr (Fin.natAdd 0 x)) =
      Term.var (Sum.inr (Fin.castLE h x))
    congr 2
    apply Fin.ext
    simp

/-- At arbitrary binder depth, free renaming agrees with variable substitution.
The explicit cast records mathlib's `0 + n` result index for bounded relabeling. -/
theorem bounded_relabel_as_subst {n : Nat} (φ : L.BoundedFormula α n)
    (r : α → β) :
    φ.relabel (Sum.inl ∘ r) =
      (φ.subst (Term.var ∘ r)).castLE (by omega : n ≤ 0 + n) := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change BoundedFormula.equal
      (t.relabel (BoundedFormula.relabelAux (Sum.inl ∘ r) _))
      (u.relabel (BoundedFormula.relabelAux (Sum.inl ∘ r) _)) =
      BoundedFormula.equal
      ((t.subst (liftSub _ (Term.var ∘ r))).relabel (Sum.map id (Fin.castLE _)))
      ((u.subst (liftSub _ (Term.var ∘ r))).relabel (Sum.map id (Fin.castLE _)))
    rw [term_relabel_zero_as_subst,term_relabel_zero_as_subst]
  | rel rel ts =>
    change BoundedFormula.rel rel (fun i =>
      (ts i).relabel (BoundedFormula.relabelAux (Sum.inl ∘ r) _)) =
      BoundedFormula.rel rel (fun i =>
      ((ts i).subst (liftSub _ (Term.var ∘ r))).relabel (Sum.map id (Fin.castLE _)))
    congr 1
    funext i
    exact term_relabel_zero_as_subst _ _ _
  | imp a b ia ib =>
    simp only [BoundedFormula.relabel_imp,BoundedFormula.subst,
      BoundedFormula.mapTermRel,BoundedFormula.castLE] at *
    rw [ia,ib]
  | all f ih =>
    simpa only [BoundedFormula.relabel_all,BoundedFormula.subst,
      BoundedFormula.mapTermRel,BoundedFormula.castLE,id_eq] using congrArg BoundedFormula.all ih

theorem formula_relabel_as_subst (φ : L.Formula α) (r : α → β) :
    φ.relabel r = φ.subst (Term.var ∘ r) := by
  simpa only [FirstOrder.Language.Formula.relabel,BoundedFormula.castLE_rfl]
    using bounded_relabel_as_subst φ r

theorem formula_subst_relabel (φ : L.Formula α) (σ : α → L.Term β) (r : β → γ) :
    (FirstOrder.Language.Formula.relabel r (φ.subst σ)) =
      φ.subst (fun x => (σ x).relabel r) := by
  rw [formula_relabel_as_subst,formula_subst_comp]
  congr 1
  funext x
  exact (term_relabel_as_subst _ _).symm

end PASoundness.SyntaxTransport
