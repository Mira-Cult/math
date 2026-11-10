import PASoundness.PAtoCompactScopedBindSelf
import PASoundness.PAtoCompactDirectGeneralization

namespace PASoundness.PAtoCompactScopedBindVariable
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedUnusedLevel

def varMap {n : Nat} (x y : Nat) : Nat ⊕ Fin n → Nat ⊕ Fin n :=
  Sum.elim (fun a => .inl (rename x y a)) Sum.inr

theorem name_map {n : Nat} (x y : Nat) (bound : Fin n → Nat) (v : Nat ⊕ Fin n) :
    (Sum.elim id bound ∘ varMap x y) v =
    (Sum.elim id (Fin.append (fun _ : Fin 1 => y) bound) ∘
      BoundedFormula.relabelAux (bindName x) n) v := by
  cases v with
  | inl z =>
    by_cases h : z = x
    · subst z; simp [BoundedFormula.relabelAux, bindName, rename, varMap, Function.comp_def]
    · simp [BoundedFormula.relabelAux, bindName, rename, varMap, Function.comp_def, h]
  | inr i => simp [BoundedFormula.relabelAux, varMap, Function.comp_def]

theorem term_subst_varMap {n : Nat} (t : Peano.language.Term (Nat ⊕ Fin n)) (x y : Nat) :
    t.subst (PASoundness.SyntaxTransport.liftSub n (Term.var ∘ rename x y)) =
      t.relabel (varMap x y) := by
  rw [PASoundness.SyntaxTransport.term_relabel_as_subst]
  congr 1
  funext v
  cases v <;> simp [PASoundness.SyntaxTransport.liftSub, varMap, Function.comp_def]

theorem renamed_free {n : Nat} (φ : Peano.language.BoundedFormula Nat n) (x y : Nat) :
    (φ.subst (Term.var ∘ rename x y)).freeVarFinset = φ.freeVarFinset.image (rename x y) := by
  ext z
  simp only [PASoundness.SyntaxTransport.formula_subst_freeVars, Finset.mem_image,
    Function.comp_apply, Term.varFinset, Finset.mem_singleton]
  exact exists_congr fun a => and_congr_right fun _ => eq_comm

theorem subst_of_absent {n : Nat} (φ : Peano.language.BoundedFormula Nat n) (x y : Nat)
    (hx : x ∉ φ.freeVarFinset) : φ.subst (Term.var ∘ rename x y) = φ := by
  calc
    φ.subst (Term.var ∘ rename x y) = φ.subst Term.var := by
      apply PASoundness.SyntaxTransport.formula_subst_agree
      intro z hz
      have hne : z ≠ x := fun h => hx (h ▸ hz)
      simp [rename, hne]
    _ = φ := PASoundness.SyntaxTransport.formula_subst_var _

theorem bound_scopeBase_same {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (x y : Nat) (bound : Fin n → Nat) (hx : x ∈ φ.freeVarFinset) :
    scopeBase (φ.subst (Term.var ∘ rename x y)) bound =
      scopeBase (φ.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => y) bound) := by
  unfold scopeBase
  have hbind : (φ.relabel (bindName x)).freeVarFinset = φ.freeVarFinset.erase x := by
    exact PASoundness.SyntaxTransport.relabel_bind_freeVars φ x
  rw [renamed_free, hbind, extended_bound_image]
  have hset : φ.freeVarFinset.image (rename x y) = insert y (φ.freeVarFinset.erase x) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨a, ha, hz⟩
      by_cases he : a = x
      · subst a; left; simpa [rename] using hz.symm
      · right
        have haeq : rename x y a = a := by simp [rename, he]
        rw [haeq] at hz
        rw [← hz]
        exact ⟨he, ha⟩
    · rintro (rfl | ⟨hzx, hz⟩)
      · exact ⟨x, hx, by simp [rename]⟩
      · exact ⟨z, hz, by simp [rename, hzx]⟩
  rw [hset]
  simp only [Finset.insert_union, Finset.union_insert]


open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactScopedUnusedFull PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousQuantifierFree
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Capture-safe binding alignment for an arbitrary replacement variable.
The target may already occur freely or alias an active name. -/
noncomputable def scoped_bind_variable {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ∀ (x y : Nat) (bound : Fin n → Nat),
      KBoth (scopedFormula n (φ.subst (Term.var ∘ rename x y)) bound)
        (scopedFormula (1+n) (φ.relabel (bindName x))
          (Fin.append (fun _ : Fin 1 => y) bound)) := by
  induction φ with
  | falsum => intro x y bound; exact ⟨identity 1, identity 1⟩
  | @equal n t u =>
      intro x y bound
      by_cases hx : x ∈ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset
      · let r := BoundedFormula.relabelAux (bindName x) n
        let ext := Fin.append (fun _ : Fin 1 => y) bound
        let σ := PASoundness.SyntaxTransport.liftSub n ((Term.var : Nat → Peano.Term) ∘ rename x y)
        have ht : t.subst σ = t.relabel (varMap x y) := term_subst_varMap t x y
        have hu : u.subst σ = u.relabel (varMap x y) := term_subst_varMap u x y
        have hbase := bound_scopeBase_same (.equal t u) x y bound hx
        have hn (v : Nat ⊕ Fin n) :
            (Sum.elim id bound ∘ varMap x y) v = (Sum.elim id ext ∘ r) v :=
          name_map x y bound v
        change KBoth (scopedFormula n (.equal (t.subst σ) (u.subst σ)) bound)
          (scopedFormula (1+n) (.equal (t.relabel r) (u.relabel r)) ext)
        rw [ht, hu, scoped_equal_frame, scoped_equal_frame]
        have heqL := frame_relabel_name_agree t u (varMap x y) (Sum.elim id bound ∘ varMap x y)
          (Sum.elim id bound) (scopeBase (.equal (t.relabel r) (u.relabel r)) ext)
          (fun v hv => rfl) (fun v hv => rfl)
        have heqR := frame_relabel_name_agree t u r (Sum.elim id bound ∘ varMap x y)
          (Sum.elim id ext) (scopeBase (.equal (t.relabel r) (u.relabel r)) ext)
          (fun v hv => hn v) (fun v hv => hn v)
        have hb : scopeBase (.equal (t.relabel (varMap x y)) (u.relabel (varMap x y))) bound =
            scopeBase (.equal (t.relabel r) (u.relabel r)) ext := by
          change scopeBase (.equal (t.subst σ) (u.subst σ)) bound =
            scopeBase (.equal (t.relabel r) (u.relabel r)) ext at hbase
          rw [ht, hu] at hbase
          exact hbase
        rw [hb, heqL, heqR]
        exact ⟨identity _, identity _⟩
      · rw [subst_of_absent (.equal t u) x y hx]
        exact scoped_unused (.equal t u) x y bound hx
  | rel r ts => exact nomatch r
  | imp a b ia ib =>
      intro x y bound
      have ha := ia x y bound
      have hb := ib x y bound
      change KBoth (.imp (scopedFormula _ (a.subst (Term.var ∘ rename x y)) bound)
          (scopedFormula _ (b.subst (Term.var ∘ rename x y)) bound))
        (.imp (scopedFormula _ (a.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => y) bound))
          (scopedFormula _ (b.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => y) bound)))
      exact ⟨implicationCongr ha.2 hb.1, implicationCongr ha.1 hb.2⟩
  | @all n body ih =>
      intro x y bound
      by_cases hx : x ∈ (.all body : Peano.language.BoundedFormula Nat n).freeVarFinset
      · let ext := Fin.append (fun _ : Fin 1 => y) bound
        let lb := body.subst (Term.var ∘ rename x y)
        let rb : Peano.language.BoundedFormula Nat ((1+n)+1) := body.relabel (bindName x)
        let p := scopeBase (.all lb) bound
        have hbase : scopeBase (.all rb) ext = p := by
          simpa [p, lb, rb, ext, BoundedFormula.subst, BoundedFormula.relabel_all,
            BoundedFormula.mapTermRel] using (bound_scopeBase_same (.all body) x y bound hx).symm
        have hh := ih x y (Fin.snoc bound p)
        rw [Fin.append_snoc] at hh
        rw [show (.all body : Peano.language.BoundedFormula Nat n).subst (Term.var ∘ rename x y) =
          .all (body.subst (Term.var ∘ rename x y)) from rfl]
        rw [BoundedFormula.relabel_all]
        change KBoth (Formula.all p (.imp (domainAt (p+1) p)
            (scopedFormula (n+1) lb (Fin.snoc bound p))))
          (Formula.all (scopeBase (.all rb) ext)
            (.imp (domainAt (scopeBase (.all rb) ext + 1) (scopeBase (.all rb) ext))
              (scopedFormula ((1+n)+1) rb (Fin.snoc ext (scopeBase (.all rb) ext)))))
        rw [hbase]
        exact ⟨allCongr p (implicationCongr (identity _) hh.1),
          allCongr p (implicationCongr (identity _) hh.2)⟩
      · rw [subst_of_absent (.all body) x y hx]
        exact scoped_unused (.all body) x y bound hx

noncomputable def formula_bind_variable (φ : Peano.Formula) (x y : Nat) :
    KBoth (formula (FOL.substAt φ x (.var y)))
      (PASoundness.PAtoCompactDirectGeneralization.scopeAt φ x y) := by
  have h := scoped_bind_variable φ x y Fin.elim0
  have hs : (Term.var ∘ rename x y : Nat → Peano.Term) =
      (fun z => if z = x then .var y else .var z) := by
    funext z
    by_cases hz : z = x <;> simp [rename, hz]
  have he : (Fin.append (fun _ : Fin 1 => y) (Fin.elim0 : Fin 0 → Nat)) = Fin.snoc Fin.elim0 y := by
    funext i
    fin_cases i
    simp [Fin.append, Fin.addCases]
  rw [hs, he] at h
  exact h

end PASoundness.PAtoCompactScopedBindVariable

#print axioms PASoundness.PAtoCompactScopedBindVariable.scoped_bind_variable
#print axioms PASoundness.PAtoCompactScopedBindVariable.formula_bind_variable
