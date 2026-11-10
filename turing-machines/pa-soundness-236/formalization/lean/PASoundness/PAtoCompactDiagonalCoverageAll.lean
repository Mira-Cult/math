import PASoundness.PAtoCompactDiagonalExtension

/-! Quantified diagonal-coverage transfer in the literal K calculus. All
successor cases, old coverage/inclusion, and the new pair and membership
witnesses are supplied as hypotheses. This does not construct a diagonal
graph, prove no-garbage, or assert a collection principle. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalCoverageAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactDiagonalExtension

/-- The pointwise coverage argument lifts to all candidate arguments, retaining
every input hypothesis. Numeric labels are fixed and binders are literal. -/
def diagonal_coverage_all : KDerivation
    (imp (allCode 2 (imp (member 1 2) (either (equal 2 0) (member 0 2))))
      (imp (allCode 19 (imp (member 6 19) (member 7 19)))
        (imp (allCode 2 (imp (member 0 2) (graphFormula 6 2 2).encode))
          (imp (member 7 8) (imp (pairFormula 8 0 0).encode
            (allCode 2 (imp (member 1 2) (graphFormula 7 2 2).encode))))))) := by
  let C := allCode 2 (imp (member 1 2) (either (equal 2 0) (member 0 2)))
  let I := allCode 19 (imp (member 6 19) (member 7 19))
  let O := allCode 2 (imp (member 0 2) (graphFormula 6 2 2).encode)
  let M := member 7 8
  let P := (pairFormula 8 0 0).encode
  let Γ := [P,M,O,I,C]
  have hI : Context Γ I := .hypothesis (by simp [Γ])
  have hO : Context Γ O := .hypothesis (by simp [Γ])
  have hM : Context Γ M := .hypothesis (by simp [Γ])
  have hP : Context Γ P := .hypothesis (by simp [Γ])
  have hC : Context Γ C := .hypothesis (by simp [Γ])
  let fI : Formula := .all 19 (.imp (.member 6 19) (.member 7 19))
  have hIfresh : 2 ∉ fI.names := by decide
  have hIv : KDerivation (imp I (allCode 2 I)) := by
    have h := fI.vacuity 2 hIfresh
    simpa [fI,I, Formula.encode] using h
  have hMv : KDerivation (imp M (allCode 2 M)) := membershipVacuity 7 8 2 (by decide) (by decide)
  have hPfresh : 2 ∉ (pairFormula 8 0 0).names := by decide
  have hPv : KDerivation (imp P (allCode 2 P)) := (pairFormula 8 0 0).vacuity 2 hPfresh
  have hallI : Context Γ (allCode 2 I) := .mp hI (.closed hIv)
  have hallM : Context Γ (allCode 2 M) := .mp hM (.closed hMv)
  have hallP : Context Γ (allCode 2 P) := .mp hP (.closed hPv)
  have h1 := Context.allMP hC (.closed (.generalize 2 diagonal_coverage_step))
  have h2 := Context.allMP hallI h1
  have h3 := Context.allMP hO h2
  have h4 := Context.allMP hallM h3
  have h5 := Context.allMP hallP h4
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact h5

theorem diagonal_coverage_all_certificate :
    theoremCode (certificate diagonal_coverage_all) =
      imp (allCode 2 (imp (member 1 2) (either (equal 2 0) (member 0 2))))
        (imp (allCode 19 (imp (member 6 19) (member 7 19)))
          (imp (allCode 2 (imp (member 0 2) (graphFormula 6 2 2).encode))
            (imp (member 7 8) (imp (pairFormula 8 0 0).encode
              (allCode 2 (imp (member 1 2) (graphFormula 7 2 2).encode)))))) :=
  certificate_correct diagonal_coverage_all

end PASoundness.PAtoCompactDiagonalCoverageAll

#print axioms PASoundness.PAtoCompactDiagonalCoverageAll.diagonal_coverage_all
#print axioms PASoundness.PAtoCompactDiagonalCoverageAll.diagonal_coverage_all_certificate
