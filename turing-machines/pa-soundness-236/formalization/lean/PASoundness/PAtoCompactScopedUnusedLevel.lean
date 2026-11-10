import PASoundness.PAtoCompactScopedAlphaInvariant
import PASoundness.PAtoCompactFormulaTranslation
import PASoundness.SyntaxTransport

/-! Local invariants for inserting an unused source bound level. The extra
active name can change the allocation base; these lemmas do not claim K
equivalence of the full scoped translations. -/
namespace PASoundness.PAtoCompactScopedUnusedLevel

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedAlphaInvariant

def bindName (x : Nat) (y : Nat) : Nat ⊕ Fin 1 :=
  if y = x then Sum.inr 0 else Sum.inl y

/-- An inserted level is not a new free source variable when its source name
was absent. -/
theorem inserted_free_names {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    (φ.relabel (bindName x)).freeVarFinset = φ.freeVarFinset := by
  change (φ.relabel (fun y => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y)).freeVarFinset = _
  rw [PASoundness.SyntaxTransport.relabel_bind_freeVars, Finset.erase_eq_of_notMem hx]

/-- The image of the extended environment is its old image plus the
inserted label, even if that label duplicates an old one. -/
theorem extended_bound_image {n : Nat} (bound : Fin n → Nat) (z : Nat) :
    Finset.univ.image (Fin.append (fun _ : Fin 1 => z) bound) =
      insert z (Finset.univ.image bound) := by
  ext w
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.addCases ?_ ?_ i
    · intro j hi
      simp only [Fin.append_left] at hi
      exact Or.inl hi.symm
    · intro j hi
      simp only [Fin.append_right] at hi
      exact Or.inr ⟨j, hi⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd n (0 : Fin 1), by simp⟩
    · exact ⟨Fin.natAdd 1 i, by simp⟩

/-- The allocator base changes exactly by adjoining the unused active name.
This is generally not equal to the original base when the new label is high. -/
theorem inserted_scopeBase {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (x z : Nat) (bound : Fin n → Nat) (hx : x ∉ φ.freeVarFinset) :
    scopeBase (φ.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => z) bound) =
      max (scopeBase φ bound) (z + 1) := by
  unfold scopeBase
  rw [inserted_free_names φ x hx, extended_bound_image]
  simp only [Finset.union_insert, Finset.sup_insert, id_eq]
  omega

/-- If the added label is already below the old allocator base, insertion
preserves that exact base. -/
theorem inserted_scopeBase_same {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (x z : Nat) (bound : Fin n → Nat) (hx : x ∉ φ.freeVarFinset)
    (hz : z < scopeBase φ bound) :
    scopeBase (φ.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => z) bound) =
      scopeBase φ bound := by
  rw [inserted_scopeBase φ x z bound hx]
  omega

/-- Mapping the extended bound environment back to each source term variable
preserves its name, provided the newly bound source variable does not occur. -/
theorem inserted_term_name_agree {n : Nat}
    (t : Peano.language.Term (Nat ⊕ Fin n)) (x z : Nat) (bound : Fin n → Nat)
    (hx : Sum.inl x ∉ t.varFinset) :
    ∀ v ∈ t.varFinset,
      (Sum.elim id (Fin.append (fun _ : Fin 1 => z) bound) ∘ BoundedFormula.relabelAux (bindName x) n) v =
        Sum.elim id bound v := by
  intro v hv
  cases v with
  | inl y =>
      have hy : y ≠ x := by
        intro h
        subst y
        exact hx hv
      simp [BoundedFormula.relabelAux, bindName, hy, Function.comp_def]
  | inr i =>
      simp [BoundedFormula.relabelAux, Function.comp_def]

/-- The generated term graph is literally unchanged when the inserted
source level is unused and the caller keeps its allocator base fixed. -/
theorem inserted_termGraph {n : Nat}
    (t : Peano.language.Term (Nat ⊕ Fin n)) (x z out base : Nat)
    (bound : Fin n → Nat) (hx : Sum.inl x ∉ t.varFinset) :
    termGraph (Sum.elim id (Fin.append (fun _ : Fin 1 => z) bound))
        (t.relabel (BoundedFormula.relabelAux (bindName x) n)) out base =
      termGraph (Sum.elim id bound) t out base := by
  rw [termGraph_relabel]
  exact termGraph_name_agree t _ _ (inserted_term_name_agree t x z bound hx) out base

end PASoundness.PAtoCompactScopedUnusedLevel

#print axioms PASoundness.PAtoCompactScopedUnusedLevel.inserted_free_names
#print axioms PASoundness.PAtoCompactScopedUnusedLevel.extended_bound_image
#print axioms PASoundness.PAtoCompactScopedUnusedLevel.inserted_scopeBase
#print axioms PASoundness.PAtoCompactScopedUnusedLevel.inserted_scopeBase_same
#print axioms PASoundness.PAtoCompactScopedUnusedLevel.inserted_term_name_agree
#print axioms PASoundness.PAtoCompactScopedUnusedLevel.inserted_termGraph
