import PASoundness.PAtoCompactPAAddZeroNecessityFrame
import PASoundness.PAtoCompactPAAddZeroNecessityCanonical
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactUnaryGuardedCanonical

/-! The translated PA right-zero axiom entails existence of the argument's
term-graph witness. This is a finite K proof transformation, not a semantic
soundness argument. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PASoundness.PAtoCompactPAAddZeroNecessity

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactPAAddZeroNecessityFrame PASoundness.PAtoCompactPAAddZeroNecessityCanonical

/-- Any finite K proof of the actual guarded PA right-zero axiom supplies a
finite K proof of guarded graph existence for its argument, at the canonical
output and allocator for that very axiom's guard. -/
noncomputable def guarded_graph_of_add_zero (t : Peano.Term)
    (h : KDerivation (guardedCode ((Peano.add t Peano.zero).equal t))) :
    let A := (Peano.add t Peano.zero).equal t
    KDerivation (imp (guardFormula A).encode
      (existsCode (outputName A) (termGraph id t (outputName A) (allocatorBase A)).encode)) := by
  let A := (Peano.add t Peano.zero).equal t
  let b := guardBase A
  have hscope : b = scopeBase A Fin.elim0 := by simp [b, guardBase, scopeBase]
  have ht : ∀ a ∈ t.varFinset, a < b := by
    intro a ha
    have hfree : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inr ha
    have hh := free_lt_scopeBase A Fin.elim0 a hfree
    omega
  have hp := equality_frame_right_graph id (Peano.add t Peano.zero) t b
    (by intro a ha; simpa using ht a ha)
  have hc := right_to_canonical t b (b + 2 + termCost (Peano.add t Peano.zero))
    (by omega) ht
  have hg : KDerivation (imp (guardFormula A).encode
      (equalityFrame id (Peano.add t Peano.zero) t b).encode) := by
    have hh := h
    unfold guardedCode code at hh
    rw [original_shape] at hh
    rw [← hscope] at hh
    exact hh
  have hres := compose (compose hg hp) hc
  simpa [A, b, outputName, allocatorBase] using hres

theorem guarded_graph_of_add_zero_certificate (t : Peano.Term)
    (h : KDerivation (guardedCode ((Peano.add t Peano.zero).equal t))) :
    let A := (Peano.add t Peano.zero).equal t
    theoremCode (certificate (guarded_graph_of_add_zero t h)) =
      imp (guardFormula A).encode
        (existsCode (outputName A) (termGraph id t (outputName A) (allocatorBase A)).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactPAAddZeroNecessity

#print axioms PASoundness.PAtoCompactPAAddZeroNecessity.guarded_graph_of_add_zero
#print axioms PASoundness.PAtoCompactPAAddZeroNecessity.guarded_graph_of_add_zero_certificate
