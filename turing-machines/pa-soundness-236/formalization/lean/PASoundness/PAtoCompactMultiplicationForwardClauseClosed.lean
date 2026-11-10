import PASoundness.PAtoCompactMultiplicationForwardOldShared
import PASoundness.PAtoCompactMultiplicationTopForwardCommonContext
import PASoundness.PAtoCompactMultiplicationForwardQuantGeneric

/-! The complete quantified forward clause of the proposed product graph,
under one explicit shared context retaining the old product, clean graph,
suffix map, row invariant, candidate guards, cut and successor. This does
not construct those witnesses, prove the reverse/lex clauses, multiplication
totality or the PA bridge. -/
namespace PASoundness.PAtoCompactMultiplicationForwardClauseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationForwardQuantGeneric
open PASoundness.PAtoCompactMultiplicationForwardOldShared
open PASoundness.PAtoCompactMultiplicationTopPointTransport
open PASoundness.PAtoCompactMultiplicationTopForwardCommonContext
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The same shared context supplies the actual top-major point proof. -/
def top_point_from_context : KDerivation (imp context.encode
    (imp (equal 3 30) (imp (member 31 4) witness.encode))) :=
  compose shared_to_top_base top_point_at4

/-- Under the literal shared conditions, all queried members of the new first
factor and old second factor have an extended product-graph output unique in
the new result. -/
def forward_clause : KDerivation (imp context.encode newForward.encode) :=
  forward_from_cases context.encode project_successor old_point top_point_from_context
    context_vacuity3 context_vacuity4

theorem forward_clause_certificate : theoremCode (certificate forward_clause) =
    imp context.encode newForward.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationForwardClauseClosed
#print axioms PASoundness.PAtoCompactMultiplicationForwardClauseClosed.top_point_from_context
#print axioms PASoundness.PAtoCompactMultiplicationForwardClauseClosed.forward_clause
#print axioms PASoundness.PAtoCompactMultiplicationForwardClauseClosed.forward_clause_certificate
