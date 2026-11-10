import PASoundness.PAtoCompactMultiplicationCleanMapUniqueActual

/-! Capture-safe specialization of clean map uniqueness to competing output
name 70. This leaves name 9 available for a separate no-garbage binder; it
does not construct a graph or prove multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCleanMapUnique70
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationCleanMapUnique41
open PASoundness.PAtoCompactMultiplicationCleanMapUniqueActual
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def statement : Formula := .imp suffixClean (.imp mapBijection40
  (.imp (.member 31 3) (.imp (graphFormula 6 3 5)
    (.imp (graphFormula 6 3 9) (.equal 9 5)))))

/-- Under the supplied clean source-31/target-40 bijection, two edges at
source 3 have equal outputs; the competing output uses fresh label 70. -/
def clean_unique_70 : KDerivation (imp suffixClean.encode (imp mapBijection40.encode
    (imp (member 31 3) (imp (graphFormula 6 3 5).encode
      (imp (graphFormula 6 3 70).encode (equal 70 5)))))) := by
  have h : KDerivation statement.encode := by
    simpa [statement, Formula.encode] using clean_unique_actual
  have hi := universalInstance 9 70 statement (by decide) (by decide) (by decide)
  have hs : replace 9 70 statement = .imp suffixClean (.imp mapBijection40
      (.imp (.member 31 3) (.imp (graphFormula 6 3 5)
        (.imp (graphFormula 6 3 70) (.equal 70 5))))) := by decide
  rw [hs] at hi
  exact .mp (.generalize 9 h) hi

theorem clean_unique_70_certificate : theoremCode (certificate clean_unique_70) =
    imp suffixClean.encode (imp mapBijection40.encode (imp (member 31 3)
      (imp (graphFormula 6 3 5).encode (imp (graphFormula 6 3 70).encode (equal 70 5))))) :=
  certificate_correct clean_unique_70
end PASoundness.PAtoCompactMultiplicationCleanMapUnique70
#print axioms PASoundness.PAtoCompactMultiplicationCleanMapUnique70.clean_unique_70
#print axioms PASoundness.PAtoCompactMultiplicationCleanMapUnique70.clean_unique_70_certificate
