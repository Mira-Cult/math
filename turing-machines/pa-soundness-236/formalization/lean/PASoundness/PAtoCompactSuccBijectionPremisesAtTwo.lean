import PASoundness.PAtoCompactSuccBijectionPremises
import PASoundness.PAtoCompactSuccOldMatrixVacuity
import PASoundness.PAtoCompactSuccPremiseVacuity

/-! Capture-safe K vacuity at name 2 of the exact eight supplied premises.
The old matrix's internal binder 2 is first alpha-freshened in the imported
proof. No premise or successor congruence is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBijectionPremisesAtTwo
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccBijectionPremises
open PASoundness.PAtoCompactSuccOldMatrixVacuity PASoundness.PAtoCompactSuccPremiseVacuity

/-- Vacuity of a conjunction follows by the literal conjunction encoding. -/
def conjunction_vacuity (x A B : Nat)
    (hA : KDerivation (imp A (allCode x A)))
    (hB : KDerivation (imp B (allCode x B))) :
    KDerivation (imp (both A B) (allCode x (both A B))) :=
  negationVacuity x (implicationVacuity x hA (negationVacuity x hB))

/-- The exact conjunction of eight premises is vacuous at pointwise name 2. -/
def premises_vacuity_2 : KDerivation (imp premisesCode (allCode 2 premisesCode)) := by
  unfold premisesCode
  exact conjunction_vacuity 2 _ _ old_matrix_vacuity
    (conjunction_vacuity 2 _ _ clean_vacuity
      (conjunction_vacuity 2 _ _ source_successor_vacuity
        (conjunction_vacuity 2 _ _ target_successor_vacuity
          (conjunction_vacuity 2 _ _ pair_vacuity
            (conjunction_vacuity 2 _ _ graph_vacuity
              (conjunction_vacuity 2 _ _ source_irreflexive_vacuity target_irreflexive_vacuity))))))

theorem premises_vacuity_2_certificate : theoremCode (certificate premises_vacuity_2) =
    imp premisesCode (allCode 2 premisesCode) := certificate_correct premises_vacuity_2

end PASoundness.PAtoCompactSuccBijectionPremisesAtTwo

#print axioms PASoundness.PAtoCompactSuccBijectionPremisesAtTwo.premises_vacuity_2
#print axioms PASoundness.PAtoCompactSuccBijectionPremisesAtTwo.premises_vacuity_2_certificate
