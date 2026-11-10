import PASoundness.PAtoCompactSuccOrderPointLift

/-! Exact named and numeric syntax of the pointwise successor-order target.
These are formula identities, not an order proof or a congruence claim. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccOrderPointShape
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccOrderPointLift

/-- The exact six graph/domain guards in the pointwise new-order clause. -/
def guards : Nat := both (member 7 2) (both (member 7 4)
  (both (member 8 3) (both (member 8 5)
    (both (graphFormula 9 2 3).encode (graphFormula 9 4 5).encode))))

/-- The exact two-way membership implication in the pointwise clause. -/
def comparison : Nat := both (imp (member 4 2) (member 5 3))
  (imp (member 5 3) (member 4 2))

/-- Named form of the six guards and order comparison. -/
def namedPoint : Formula :=
  .imp (namedBoth (.member 7 2) (namedBoth (.member 7 4)
    (namedBoth (.member 8 3) (namedBoth (.member 8 5)
      (namedBoth (graphFormula 9 2 3) (graphFormula 9 4 5))))))
    (namedBoth (.imp (.member 4 2) (.member 5 3))
      (.imp (.member 5 3) (.member 4 2)))

/-- All input/domain replacements and fixed graph occurrences agree exactly. -/
theorem point_named_shape : pointMatrix = namedPoint := by decide

/-- The exact literal K code has the advertised nested conjunction. -/
theorem point_encoded_shape : pointMatrix.encode = imp guards comparison := by
  rw [point_named_shape]
  rfl

end PASoundness.PAtoCompactSuccOrderPointShape

#print axioms PASoundness.PAtoCompactSuccOrderPointShape.point_named_shape
#print axioms PASoundness.PAtoCompactSuccOrderPointShape.point_encoded_shape
