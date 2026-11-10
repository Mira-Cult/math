import PASoundness.PAtoCompactGuardedEqualityReflexivityUnary
import PASoundness.PAtoCompactAddUnaryTotalityClosed

/-! Guarded equality reflexivity for the variable/zero/successor/addition
fragment of PA terms. The construction uses a shared graph witness for both
sides and does not assume graph functionality. Multiplication and the full PA
proof translation are not established here. -/
namespace PASoundness.PAtoCompactGuardedEqualityReflexivityAddition
open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactAddUnaryTotalityInduction
open PASoundness.PAtoCompactGuardedEqualityReflexivityUnary

/-- Every addition/unary PA term has a guarded reflexive equality proof in K.
The finite proof transformer is noncomputable and does not use soundness. -/
noncomputable def addition_reflexivity (t : Peano.Term) (h : AddUnaryTerm t) :
    KDerivation (guardedCode (t.equal t)) := by
  apply reflexivity_of_graph_total
  have hv := PASoundness.PAtoCompactAddUnaryTotalityClosed.canonical_total
    id (t.equal t) h (term_coverage t)
  simpa only [PASoundness.PAtoCompactUnaryGuardedCanonical.outputName,
    PASoundness.PAtoCompactUnaryGuardedCanonical.allocatorBase, guard_scope] using hv

theorem addition_reflexivity_certificate (t : Peano.Term) (h : AddUnaryTerm t) :
    theoremCode (certificate (addition_reflexivity t h)) = guardedCode (t.equal t) :=
  certificate_correct _
end PASoundness.PAtoCompactGuardedEqualityReflexivityAddition
#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivityAddition.addition_reflexivity
#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivityAddition.addition_reflexivity_certificate
