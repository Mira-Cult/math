import PASoundness.PAtoCompactFreeVacuity

/-! Finite K vacuity proofs for generated term graphs and arbitrary scoped
formula translations, under explicit source-name freshness conditions. -/
namespace PASoundness.PAtoCompactScopedVacuity

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

/-- A name distinct from the output and all used source-variable names is
vacuous for a generated term graph, even if it is an internal bound name. -/
def termGraph_vacuity {α : Type} [DecidableEq α] (varName : α → Nat)
    (t : Peano.language.Term α) (out base x : Nat) (hout : x ≠ out)
    (hvars : ∀ a ∈ t.varFinset, x ≠ varName a) :
    KDerivation (imp (termGraph varName t out base).encode
      (allCode x (termGraph varName t out base).encode)) := by
  apply free_vacuity x (termGraph varName t out base)
  intro h
  rcases Finset.mem_union.mp (termGraph_free_subset varName t out base h) with hv | ho
  · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hv
    exact hvars a ha he.symm
  · exact hout (Finset.mem_singleton.mp ho)

/-- A name absent from source free variables and all active bound-name
assignments is vacuous for the generated scoped formula. -/
def scopedFormula_vacuity {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (bound : Fin n → Nat) (x : Nat) (hfree : x ∉ φ.freeVarFinset)
    (hbound : ∀ i, x ≠ bound i) :
    KDerivation (imp (scopedFormula n φ bound).encode
      (allCode x (scopedFormula n φ bound).encode)) := by
  apply free_vacuity x (scopedFormula n φ bound)
  intro h
  rcases Finset.mem_union.mp (scopedFormula_free_subset φ bound h) with hf | hb
  · exact hfree hf
  · obtain ⟨i, _, he⟩ := Finset.mem_image.mp hb
    exact hbound i he.symm

theorem termGraph_vacuity_certificate {α : Type} [DecidableEq α] (varName : α → Nat)
    (t : Peano.language.Term α) (out base x : Nat) (hout : x ≠ out)
    (hvars : ∀ a ∈ t.varFinset, x ≠ varName a) :
    theoremCode (certificate (termGraph_vacuity varName t out base x hout hvars)) =
      imp (termGraph varName t out base).encode (allCode x (termGraph varName t out base).encode) :=
  certificate_correct _

theorem scopedFormula_vacuity_certificate {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (bound : Fin n → Nat) (x : Nat) (hfree : x ∉ φ.freeVarFinset)
    (hbound : ∀ i, x ≠ bound i) :
    theoremCode (certificate (scopedFormula_vacuity φ bound x hfree hbound)) =
      imp (scopedFormula n φ bound).encode (allCode x (scopedFormula n φ bound).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactScopedVacuity

#print axioms PASoundness.PAtoCompactScopedVacuity.termGraph_vacuity
#print axioms PASoundness.PAtoCompactScopedVacuity.scopedFormula_vacuity
#print axioms PASoundness.PAtoCompactScopedVacuity.termGraph_vacuity_certificate
#print axioms PASoundness.PAtoCompactScopedVacuity.scopedFormula_vacuity_certificate
