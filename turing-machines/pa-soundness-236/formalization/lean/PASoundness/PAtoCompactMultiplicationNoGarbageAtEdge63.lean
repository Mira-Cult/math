import PASoundness.PAtoCompactFixedFirstCoverageBase

/-! Capture-safe K specialization of the actual fixed-first no-garbage
invariant at edge name 63. This is an explicit invariant premise, not a
construction of the row graph or multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationNoGarbageAtEdge63
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstCoverageBase
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Graph 64's explicit no-garbage clause classifies its edge 63 into an
old-graph member or an actual row witness at that same edge. -/
def no_garbage_at_edge : KDerivation (imp (noGarbage 64).encode
    (imp (member 64 63) (either (member 10 63) (replace 9 63 rowWitness).encode))) := by
  let F : Formula := .imp (.member 64 9) (namedEither (.member 10 9) rowWitness)
  have hi := universalInstance 9 63 F (by decide) (by decide) (by decide)
  have hshape : replace 9 63 F = .imp (.member 64 63)
      (namedEither (.member 10 63) (replace 9 63 rowWitness)) := by decide
  rw [hshape] at hi
  simpa [noGarbage,F,namedEither,Formula.not,Formula.encode,neg,either] using hi

theorem no_garbage_at_edge_certificate : theoremCode (certificate no_garbage_at_edge) =
    imp (noGarbage 64).encode
      (imp (member 64 63) (either (member 10 63) (replace 9 63 rowWitness).encode)) :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationNoGarbageAtEdge63
#print axioms PASoundness.PAtoCompactMultiplicationNoGarbageAtEdge63.no_garbage_at_edge
#print axioms PASoundness.PAtoCompactMultiplicationNoGarbageAtEdge63.no_garbage_at_edge_certificate
