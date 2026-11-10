import PASoundness.PAtoCompactGuardedEqualityReflexivityUnary
import PASoundness.PAtoCompactAllTermsTotalityClosed

/-! Guarded equality reflexivity for every PA term, constructed as finite K
proof data. The two equality witnesses share one graph value; this result
requires no graph functionality. It does not establish equality substitution,
PA arithmetic-axiom translation, or the full PA soundness bridge. -/
namespace PASoundness.PAtoCompactGuardedEqualityReflexivityClosed

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedEqualityReflexivityUnary

/-- Construct the guarded equality-reflexivity axiom for any PA term. The
source guard covers all term variables; their generated graph has an output,
which supplies both equality operands. -/
noncomputable def reflexivity (t : Peano.Term) :
    KDerivation (guardedCode (t.equal t)) := by
  apply reflexivity_of_graph_total
  have hv := PAtoCompactAllTermsTotalityClosed.canonical_total id (t.equal t) t (term_coverage t)
  simpa only [PAtoCompactUnaryGuardedCanonical.outputName,
    PAtoCompactUnaryGuardedCanonical.allocatorBase, guard_scope] using hv

theorem reflexivity_certificate (t : Peano.Term) :
    theoremCode (certificate (reflexivity t)) = guardedCode (t.equal t) :=
  certificate_correct _
end PASoundness.PAtoCompactGuardedEqualityReflexivityClosed

#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivityClosed.reflexivity
#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivityClosed.reflexivity_certificate
