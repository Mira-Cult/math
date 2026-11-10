import PASoundness.PAtoCompactEquivalentAliasGuardLift
import PASoundness.CompactNamed

/-! Vacuity at the original graph label for the exact segment-output
formula. The K proof first uses the existing explicit alpha preparation,
which moves the graph binder to name 8, and then transports vacuity back.
This does not establish the segment-transport premise. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLessRightSegmentOutputVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactEquivalentAliasGuardLift
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def outputBody : Formula := namedBoth (.member 1 5) (guarded originalAliases)
def preparedOutputBody : Formula := namedBoth (.member 1 5) (guarded preparedAliases)
def output : Formula := .ex 5 outputBody
def preparedOutput : Formula := .ex 5 preparedOutputBody

private def body_congr {a b : Formula} (h : KDerivation (imp a.encode b.encode)) :
    KDerivation (imp (namedBoth (.member 1 5) a).encode
      (namedBoth (.member 1 5) b).encode) := by
  change KDerivation (imp (neg (imp (member 1 5) (neg a.encode)))
    (neg (imp (member 1 5) (neg b.encode))))
  exact contrapose (implicationCongr (CompactHilbertBasis.identity (member 1 5)) (contrapose h))

/-- Actual K implications in both directions between the exact output and
its alpha-prepared form. Both aliases and their guards are unchanged. -/
def output_to_prepared : KDerivation (imp output.encode preparedOutput.encode) :=
  existsCongr 5 (body_congr PAtoCompactEquivalentAliasGuardLift.forward)

def prepared_to_output : KDerivation (imp preparedOutput.encode output.encode) :=
  existsCongr 5 (body_congr PAtoCompactEquivalentAliasGuardLift.backward)

theorem prepared_avoids_graph_name : 6 ∉ preparedOutput.names := by decide

/-- The exact output is K-vacuous at 6 after explicit graph-binder
alpha preparation. No semantic independence assumption is used. -/
def output_vacuity6 : KDerivation (imp output.encode (allCode 6 output.encode)) :=
  compose output_to_prepared
    (compose (preparedOutput.vacuity 6 prepared_avoids_graph_name) (allCongr 6 prepared_to_output))

theorem output_vacuity6_certificate : theoremCode (certificate output_vacuity6) =
    imp output.encode (allCode 6 output.encode) := certificate_correct output_vacuity6

end PASoundness.PAtoCompactLessRightSegmentOutputVacuity

#print axioms PASoundness.PAtoCompactLessRightSegmentOutputVacuity.output_vacuity6
#print axioms PASoundness.PAtoCompactLessRightSegmentOutputVacuity.output_vacuity6_certificate
