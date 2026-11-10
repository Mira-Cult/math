import PASoundness.PAtoCompactGuardedAllElim
import PASoundness.PAtoCompactVacuousAllElim
import PASoundness.PAtoCompactUnaryGuardedCanonical

/-! Guarded universal elimination with a unary substitution term: the term
graph existence input is constructed, while the K substitution-compatibility
proof remains explicit. The absent-variable branch is unconditional. -/
namespace PASoundness.PAtoCompactAllElimVariable

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactGuardedVacuity PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity

/-- The chosen graph witness is above the axiom's entire free support. -/
theorem outputName_not_axiom_free (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    outputName (allElimFormula φ x t) ∉ (allElimFormula φ x t).freeVarFinset := by
  intro h
  have hle : outputName (allElimFormula φ x t) ≤
      (allElimFormula φ x t).freeVarFinset.sup id := Finset.le_sup (f := id) h
  unfold outputName guardBase at hle
  omega

theorem outputName_guard_fresh (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    outputName (allElimFormula φ x t) ∉ (guardFormula (allElimFormula φ x t)).free := by
  intro h
  exact outputName_not_axiom_free φ x t (guardFormula_free_subset _ h)

theorem outputName_all_fresh (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    outputName (allElimFormula φ x t) ∉ (formula (FOL.allAt x φ)).free := by
  intro h
  have hm := formula_free_subset (FOL.allAt x φ) h
  apply outputName_not_axiom_free φ x t
  change outputName (allElimFormula φ x t) ∈
    (FOL.allAt x φ).freeVarFinset ∪ (FOL.substAt φ x t).freeVarFinset
  exact Finset.mem_union.mpr (Or.inl hm)

theorem outputName_target_fresh (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    outputName (allElimFormula φ x t) ∉ (formula (FOL.substAt φ x t)).free := by
  intro h
  have hm := formula_free_subset (FOL.substAt φ x t) h
  apply outputName_not_axiom_free φ x t
  change outputName (allElimFormula φ x t) ∈
    (FOL.allAt x φ).freeVarFinset ∪ (FOL.substAt φ x t).freeVarFinset
  exact Finset.mem_union.mpr (Or.inr hm)

/-- When the substituted source variable occurs, unary term-graph totality is
constructed from the actual axiom guard. The remaining K input is precisely
the capture-safe substitution compatibility for the generated instance. -/
noncomputable def unary_allElim_of_substitution (φ : Peano.Formula) (x : Nat)
    (t : Peano.Term) (h : UnaryTerm t) (hx : x ∈ φ.freeVarFinset)
    (substitution : KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (outputName (allElimFormula φ x t))
        (allocatorBase (allElimFormula φ x t))).encode
        (imp (instanceBody φ x (outputName (allElimFormula φ x t))).encode
          (code (FOL.substAt φ x t)))))) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  let A := allElimFormula φ x t
  have hcover : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    exact termVars_in_axiom_of_occurs φ x t hx ha
  exact allElim_of_witness φ x t (outputName A)
    (termGraph id t (outputName A) (allocatorBase A))
    (outputName_guard_fresh φ x t) (outputName_all_fresh φ x t)
    (outputName_target_fresh φ x t)
    (PAtoCompactUnaryGuardedCanonical.unary_total id A h hcover) substitution

theorem unary_allElim_of_substitution_certificate (φ : Peano.Formula) (x : Nat)
    (t : Peano.Term) (h : UnaryTerm t) (hx : x ∈ φ.freeVarFinset)
    (substitution : KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (outputName (allElimFormula φ x t))
        (allocatorBase (allElimFormula φ x t))).encode
        (imp (instanceBody φ x (outputName (allElimFormula φ x t))).encode
          (code (FOL.substAt φ x t)))))) :
    theoremCode (certificate (unary_allElim_of_substitution φ x t h hx substitution)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

/-- Direct variable instantiation needs no existential term-graph witness.
The input is a finite K proof aligning the capture-safe instantiated scope
with the translation of the exact source-level substitution. -/
noncomputable def variable_allElim_of_alignment (φ : Peano.Formula) (x y : Nat)
    (hx : x ∈ φ.freeVarFinset)
    (alignment : KDerivation (imp
      (domainAt (guardBase (allElimFormula φ x (.var y))) y).encode
      (imp (instanceBody φ x y).encode (code (FOL.substAt φ x (.var y)))))) :
    KDerivation (guardedCode (allElimFormula φ x (.var y))) := by
  let G := (guardFormula (allElimFormula φ x (.var y))).encode
  let A := code (FOL.allAt x φ)
  let B := code (FOL.substAt φ x (.var y))
  change KDerivation (imp G (imp A B))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [A, G]
  have ha : Context Γ A := Context.head [G] A
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt (guardBase (allElimFormula φ x (.var y))) y).encode :=
    .mp hg (.closed (termVar_guard φ x (.var y) y hx (by simp [Term.varFinset])))
  have hi : Context Γ (instanceBody φ x y).encode :=
    .mp ha (.closed (universal_instance φ x y))
  exact .mp hi (.mp hd (.closed alignment))

/-- Only the occurring-variable branch requires an alignment proof. -/
noncomputable def variable_allElim (φ : Peano.Formula) (x y : Nat)
    (alignment : x ∈ φ.freeVarFinset → KDerivation (imp
      (domainAt (guardBase (allElimFormula φ x (.var y))) y).encode
      (imp (instanceBody φ x y).encode (code (FOL.substAt φ x (.var y)))))) :
    KDerivation (guardedCode (allElimFormula φ x (.var y))) := by
  by_cases hx : x ∈ φ.freeVarFinset
  · exact variable_allElim_of_alignment φ x y hx (alignment hx)
  · exact PAtoCompactVacuousAllElim.allElim_of_unused φ x (.var y) hx

theorem variable_allElim_certificate (φ : Peano.Formula) (x y : Nat)
    (alignment : x ∈ φ.freeVarFinset → KDerivation (imp
      (domainAt (guardBase (allElimFormula φ x (.var y))) y).encode
      (imp (instanceBody φ x y).encode (code (FOL.substAt φ x (.var y)))))) :
    theoremCode (certificate (variable_allElim φ x y alignment)) =
      guardedCode (allElimFormula φ x (.var y)) := certificate_correct _

end PASoundness.PAtoCompactAllElimVariable

#print axioms PASoundness.PAtoCompactAllElimVariable.outputName_not_axiom_free
#print axioms PASoundness.PAtoCompactAllElimVariable.outputName_guard_fresh
#print axioms PASoundness.PAtoCompactAllElimVariable.outputName_all_fresh
#print axioms PASoundness.PAtoCompactAllElimVariable.outputName_target_fresh
#print axioms PASoundness.PAtoCompactAllElimVariable.unary_allElim_of_substitution
#print axioms PASoundness.PAtoCompactAllElimVariable.unary_allElim_of_substitution_certificate
#print axioms PASoundness.PAtoCompactAllElimVariable.variable_allElim_of_alignment
#print axioms PASoundness.PAtoCompactAllElimVariable.variable_allElim
#print axioms PASoundness.PAtoCompactAllElimVariable.variable_allElim_certificate
