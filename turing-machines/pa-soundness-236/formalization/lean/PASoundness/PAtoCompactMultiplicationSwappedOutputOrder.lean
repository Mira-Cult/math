import PASoundness.PAtoCompactMultiplicationCandidateMixedOrder
import PASoundness.PAtoCompactFilterInstantiation

/-! Capture-safe reversal of the two output point labels in the candidate-
guarded cut/suffix comparison. This establishes no new graph, multiplication
totality, or PA soundness theorem. -/
namespace PASoundness.PAtoCompactMultiplicationSwappedOutputOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationCandidateMixedOrder
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def F : Formula := .imp (domainAt 100 45) (.imp (domainAt 100 32)
  (.imp (namedEither (.equal 32 45) (.member 45 32))
    (.imp (.all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not))
      (.imp (.member 32 5) (.imp (.member 40 9)
        (namedBoth (.member 9 5) (Formula.member 5 9).not))))))
private def F1 : Formula := replace 5 60 F
private def F2 : Formula := replace 9 5 F1
private def F3 : Formula := replace 60 9 F2

private def initial : KDerivation F.encode := by
  simpa [F,namedEither,namedFilterBody,namedBoth,Formula.encode,Formula.not,
    filterGraph,filterPredicate,either,both,neg] using candidate_old_before_new

private def at60 : KDerivation F1.encode := by
  have hi := universalInstance 5 60 F (by decide) (by decide) (by decide)
  exact .mp (.generalize 5 initial) hi

private def at5 : KDerivation F2.encode := by
  have hi := universalInstance 9 5 F1 (by decide) (by decide) (by decide)
  exact .mp (.generalize 9 at60) hi

private def at9 : KDerivation F3.encode := by
  have hi := universalInstance 60 9 F2 (by decide) (by decide) (by decide)
  exact .mp (.generalize 60 at5) hi

/-- For old output 9 in the cut and new output 5 in the filtered suffix,
the old output is below the new one. All candidate/cut hypotheses remain
literal antecedents. The output names are syntactic labels and their objects
may otherwise coincide. -/
def swapped_old_before_new : KDerivation
    (imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
      (imp (either (equal 32 45) (member 45 32))
        (imp (filterGraph 45 40 35 (neg (member 32 35)))
          (imp (member 32 9) (imp (member 40 5)
            (both (member 5 9) (neg (member 9 5))))))))) := by
  have h := at9
  have shape : F3 = .imp (domainAt 100 45) (.imp (domainAt 100 32)
    (.imp (namedEither (.equal 32 45) (.member 45 32))
      (.imp (.all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not))
        (.imp (.member 32 9) (.imp (.member 40 5)
          (namedBoth (.member 5 9) (Formula.member 9 5).not)))))) := by decide
  rw [shape] at h
  simpa [namedEither,namedFilterBody,namedBoth,Formula.encode,Formula.not,
    filterGraph,filterPredicate,either,both,neg] using h

theorem swapped_old_before_new_certificate : theoremCode (certificate swapped_old_before_new) =
    imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
      (imp (either (equal 32 45) (member 45 32))
        (imp (filterGraph 45 40 35 (neg (member 32 35)))
          (imp (member 32 9) (imp (member 40 5)
            (both (member 5 9) (neg (member 9 5)))))))) :=
  certificate_correct swapped_old_before_new
end PASoundness.PAtoCompactMultiplicationSwappedOutputOrder
#print axioms PASoundness.PAtoCompactMultiplicationSwappedOutputOrder.swapped_old_before_new
#print axioms PASoundness.PAtoCompactMultiplicationSwappedOutputOrder.swapped_old_before_new_certificate
