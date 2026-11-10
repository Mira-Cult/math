import PASoundness.PAtoCompactCleanSuffixRowClosed
import PASoundness.PAtoCompactFixedFirstRowGraph64

/-! Alpha-rebind the already constructed row graph for the product lexicographic
points while keeping the SAME clean suffix-map witness. No graph equality or
new choice of suffix graph is assumed. This is not a product matrix proof. -/
namespace PASoundness.PAtoCompactCleanSuffixRow64
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCleanSuffixRowPackage PASoundness.PAtoCompactCleanSuffixRowClosed
open PASoundness.PAtoCompactFixedFirstRowGraph64

def result64 : Formula := .ex 6 (namedBoth cleanMatrix (.ex 64 rowBody64))

/-- The clean F graph is retained and the SAME row witness is rebound from
label 7 to label 64, which is fresh for the literal row body. -/
def row_package_alpha : KDerivation (imp result.encode result64.encode) := by
  let A : Formula := namedBoth cleanMatrix rowResult
  let B : Formula := namedBoth cleanMatrix (.ex 64 rowBody64)
  have hpoint : KDerivation (imp A.encode B.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [A.encode]
    have hp : Context Γ A.encode := .head _ _
    have hh : Context Γ (both cleanMatrix.encode rowResult.encode) := by
      simpa [A,namedBoth,Formula.not,Formula.encode,both,neg] using hp
    have hr : Context Γ (existsCode 64 rowBody64.encode) := by
      apply Context.mp (Context.conjunctionRight hh)
      apply Context.closed
      simpa [rowResult] using row_graph_alpha
    have hc := Context.conjunctionIntro (Context.conjunctionLeft hh) hr
    simpa [B,namedBoth,Formula.not,Formula.encode,both,neg,existsCode] using hc
  have hh := existsCongr 6 hpoint
  simpa [result,result64,A,B,Formula.encode] using hh

/-- Candidate index and the source/suffix equivalence construct one clean
suffix graph and its associated row graph at the lexicographic label 64. -/
def clean_suffix_with_row64 : KDerivation
    (imp candidate (imp (equivAt 31 40).encode result64.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt 31 40).encode,candidate]
  have he : Context Γ (equivAt 31 40).encode := .head _ _
  have hc : Context Γ candidate := .hypothesis (by simp [Γ])
  exact .mp (.mp he (.mp hc (.closed clean_suffix_with_row))) (.closed row_package_alpha)

theorem clean_suffix_with_row64_certificate :
    theoremCode (certificate clean_suffix_with_row64) =
      imp candidate (imp (equivAt 31 40).encode result64.encode) := certificate_correct _
end PASoundness.PAtoCompactCleanSuffixRow64
#print axioms PASoundness.PAtoCompactCleanSuffixRow64.row_package_alpha
#print axioms PASoundness.PAtoCompactCleanSuffixRow64.clean_suffix_with_row64
#print axioms PASoundness.PAtoCompactCleanSuffixRow64.clean_suffix_with_row64_certificate
