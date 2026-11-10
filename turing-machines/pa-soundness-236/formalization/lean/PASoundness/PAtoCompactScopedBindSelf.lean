import PASoundness.PAtoCompactScopedUnusedFull

/-! Binding a source name to a new bound level interpreted by that same name
preserves the generated scoped formula up to finite K proof, at any depth. No
claim of effective certificate extraction is made. -/
namespace PASoundness.PAtoCompactScopedBindSelf
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedUnusedLevel

theorem interpreted_name_same {n : Nat} (x : Nat) (bound : Fin n → Nat) (v : Nat ⊕ Fin n) :
    (Sum.elim id (Fin.append (fun _ : Fin 1 => x) bound) ∘
      BoundedFormula.relabelAux (bindName x) n) v = Sum.elim id bound v := by
  cases v with
  | inl y =>
      by_cases h : y = x
      · subst y; simp [BoundedFormula.relabelAux, bindName, Function.comp_def]
      · simp [BoundedFormula.relabelAux, bindName, Function.comp_def, h]
  | inr i => simp [BoundedFormula.relabelAux, Function.comp_def]

theorem same_base_of_free {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (x : Nat) (bound : Fin n → Nat) (hx : x ∈ φ.freeVarFinset) :
    scopeBase (φ.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => x) bound) =
      scopeBase φ bound := by
  unfold scopeBase
  rw [show (φ.relabel (bindName x)).freeVarFinset = φ.freeVarFinset.erase x from by
    change (φ.relabel (fun y => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y)).freeVarFinset = _
    exact PASoundness.SyntaxTransport.relabel_bind_freeVars φ x]
  rw [extended_bound_image]
  have hset : φ.freeVarFinset.erase x ∪ insert x (Finset.univ.image bound) =
      φ.freeVarFinset ∪ Finset.univ.image bound := by
    ext z
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro (⟨hneq, hz⟩ | rfl | hz)
      · exact Or.inl hz
      · exact Or.inl hx
      · exact Or.inr hz
    · rintro (hz | hz)
      · by_cases hzx : z = x
        · exact Or.inr (Or.inl hzx)
        · exact Or.inl ⟨hzx, hz⟩
      · exact Or.inr (Or.inr hz)

  rw [hset]

#print axioms PASoundness.PAtoCompactScopedBindSelf.interpreted_name_same
#print axioms PASoundness.PAtoCompactScopedBindSelf.same_base_of_free
end PASoundness.PAtoCompactScopedBindSelf

namespace PASoundness.PAtoCompactScopedBindSelf
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedUnusedLevel PASoundness.PAtoCompactScopedUnusedFull
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactScopedEqualityReplace

noncomputable def scoped_bind_self {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ∀ (x : Nat) (bound : Fin n → Nat),
      KBoth (scopedFormula n φ bound)
        (scopedFormula (1+n) (φ.relabel (bindName x))
          (Fin.append (fun _ : Fin 1 => x) bound)) := by
  induction φ with
  | falsum => intro x bound; exact ⟨identity 1, identity 1⟩
  | @equal n t u =>
      intro x bound
      by_cases hx : x ∈ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset
      · let r := BoundedFormula.relabelAux (bindName x) n
        let ext := Fin.append (fun _ : Fin 1 => x) bound
        have hbase := same_base_of_free (.equal t u) x bound hx
        have hn (v : Nat ⊕ Fin n) : Sum.elim id bound v = Sum.elim id ext (r v) :=
          (interpreted_name_same x bound v).symm
        change KBoth (scopedFormula n (.equal t u) bound)
          (scopedFormula (1+n) (.equal (t.relabel r) (u.relabel r)) ext)
        rw [scoped_equal_frame, scoped_equal_frame]
        have heq := frame_relabel_name_agree t u r (Sum.elim id bound) (Sum.elim id ext)
          (scopeBase (.equal (t.relabel r) (u.relabel r)) ext)
          (fun v hv => hn v) (fun v hv => hn v)
        rw [heq]
        have hb : scopeBase (.equal (t.relabel r) (u.relabel r)) ext = scopeBase (.equal t u) bound := by
          exact hbase
        rw [hb]
        exact ⟨identity _, identity _⟩
      · exact scoped_unused (.equal t u) x x bound hx
  | rel r ts => exact nomatch r
  | imp a b ia ib =>
      intro x bound
      have ha := ia x bound
      have hb := ib x bound
      change KBoth (.imp (scopedFormula _ a bound) (scopedFormula _ b bound))
        (.imp (scopedFormula _ (a.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => x) bound))
          (scopedFormula _ (b.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => x) bound)))
      exact ⟨implicationCongr ha.2 hb.1, implicationCongr ha.1 hb.2⟩
  | @all n body ih =>
      intro x bound
      by_cases hx : x ∈ (.all body : Peano.language.BoundedFormula Nat n).freeVarFinset
      · let ext := Fin.append (fun _ : Fin 1 => x) bound
        let rb : Peano.language.BoundedFormula Nat ((1+n)+1) := body.relabel (bindName x)
        let p := scopeBase (.all body) bound
        have hbase : scopeBase (.all rb) ext = p := by
          simpa only [BoundedFormula.relabel_all] using same_base_of_free (.all body) x bound hx
        have hh := ih x (Fin.snoc bound p)
        rw [Fin.append_snoc] at hh
        simp only [BoundedFormula.relabel_all]
        change KBoth (Formula.all p (.imp (domainAt (p+1) p)
            (scopedFormula (n+1) body (Fin.snoc bound p))))
          (Formula.all (scopeBase (.all rb) ext)
            (.imp (domainAt (scopeBase (.all rb) ext + 1) (scopeBase (.all rb) ext))
              (scopedFormula ((1+n)+1) rb (Fin.snoc ext (scopeBase (.all rb) ext)))))
        rw [hbase]
        exact ⟨allCongr p (implicationCongr (identity _) hh.1),
          allCongr p (implicationCongr (identity _) hh.2)⟩
      · exact scoped_unused (.all body) x x bound hx

theorem scoped_bind_self_forward_certificate {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) (x : Nat) (bound : Fin n → Nat) :
    theoremCode (certificate ((scoped_bind_self φ x bound).1)) =
      imp (scopedFormula n φ bound).encode
        (scopedFormula (1+n) (φ.relabel (bindName x))
          (Fin.append (fun _ : Fin 1 => x) bound)).encode := certificate_correct _

theorem scoped_bind_self_backward_certificate {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) (x : Nat) (bound : Fin n → Nat) :
    theoremCode (certificate ((scoped_bind_self φ x bound).2)) =
      imp (scopedFormula (1+n) (φ.relabel (bindName x))
          (Fin.append (fun _ : Fin 1 => x) bound)).encode
        (scopedFormula n φ bound).encode := certificate_correct _

#print axioms PASoundness.PAtoCompactScopedBindSelf.scoped_bind_self
#print axioms PASoundness.PAtoCompactScopedBindSelf.scoped_bind_self_forward_certificate
#print axioms PASoundness.PAtoCompactScopedBindSelf.scoped_bind_self_backward_certificate
end PASoundness.PAtoCompactScopedBindSelf
