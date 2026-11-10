import PASoundness.PAtoCompactSuccInjectiveTransInstances
import PASoundness.PAtoCompactChainSymmetry

/-! Candidate-guarded equality chain for raw successor witnesses of two
quotient successors. All candidate and E hypotheses remain explicit; witness
existence, cancellation and PA proof transport are separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectiveEquivalenceChain
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccInjectiveTransInstances PASoundness.PAtoCompactChainSymmetry
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- From equivalence of the quotient outputs and both witness-to-output
relations, obtain equivalence of the two raw witnesses. -/
def witness_equivalence : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp (candidateCode 1 37 32 33 34 30 35 10 36)
        (imp E07.encode (imp E78.encode (imp E18.encode equivalentFormula.encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D0 := candidateCode 0 37 32 33 34 30 35 10 36
  let D1 := candidateCode 1 37 32 33 34 30 35 10 36
  let Γ := [E18.encode,E78.encode,E07.encode,D1,D0]
  have h18 : Context Γ E18.encode := .head _ _
  have h78 : Context Γ E78.encode := .hypothesis (by simp [Γ])
  have h07 : Context Γ E07.encode := .hypothesis (by simp [Γ])
  have hd1 : Context Γ D1 := .hypothesis (by simp [Γ])
  have hd0 : Context Γ D0 := .hypothesis (by simp [Γ])
  have h08 : Context Γ E08.encode := .mp h78 (.mp h07 (.mp hd0 (.closed trans_first)))
  have h81 : Context Γ PASoundness.PAtoCompactSuccInjectiveTransInstances.E81.encode := by
    exact .mp h18 (.mp hd1 (.closed symmetry_18))
  exact .mp h81 (.mp h08 (.mp hd0 (.closed trans_second)))

theorem witness_equivalence_certificate : theoremCode (certificate witness_equivalence) =
    imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp (candidateCode 1 37 32 33 34 30 35 10 36)
        (imp E07.encode (imp E78.encode (imp E18.encode equivalentFormula.encode)))) :=
  certificate_correct witness_equivalence

end PASoundness.PAtoCompactSuccInjectiveEquivalenceChain

#print axioms PASoundness.PAtoCompactSuccInjectiveEquivalenceChain.witness_equivalence
#print axioms PASoundness.PAtoCompactSuccInjectiveEquivalenceChain.witness_equivalence_certificate
