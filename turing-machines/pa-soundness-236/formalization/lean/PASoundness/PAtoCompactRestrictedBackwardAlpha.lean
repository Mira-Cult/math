import PASoundness.PAtoCompactRestrictedBackwardWitness
import PASoundness.CompactQuantifiers

/-! Capture-safe alignment of the original reverse-bijection clause with
the restricted graph's displayed names. This is a syntax and finite-proof
interface, not a claim of restricted bijection or quotient cancellation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedBackwardAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactBijectionBackwardAtThree PASoundness.PAtoCompactRestrictedBackwardWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact original right-bijection clause: source 0, target 1, graph 6. -/
def originalClause : Formula :=
  .all 3 (.imp (.member 1 3) (.ex 2 (witness 2)))

/-- The same original clause with existential preimage binder 2 changed to
fresh 7, before replacing any free endpoint or graph names. -/
def alphaClause : Formula :=
  .all 3 (.imp (.member 1 3) (.ex 7 (witness 7)))

/-- The actual named formula established by the restricted backward proof. -/
def restrictedClause : Formula :=
  .all 3 (.imp (.member 5 3) (.ex 7 restrictedWitness))

/-- The original bijection formula has exactly the displayed right clause.
This identity is syntactic, before any replacement of free names. -/
theorem original_is_right_clause :
    (match bijectionFormula with
      | .imp (.imp _ (.imp right .bottom)) .bottom => right
      | _ => .truth) = originalClause := by decide

/-- Rename the existential preimage binder 2 to fresh 7 under the outer
target quantifier, using explicit K alpha conversion in both directions. -/
def original_alpha :
    KDerivation (imp originalClause.encode alphaClause.encode) ×
    KDerivation (imp alphaClause.encode originalClause.encode) := by
  have h := CompactNamed.existentialAlpha 2 7 (witness 2)
    (by decide) (by decide) (by decide)
  have hs : CompactNamed.replace 2 7 (witness 2) = witness 7 := by decide
  rw [hs] at h
  have hf : KDerivation (imp originalClause.encode alphaClause.encode) := by
    simpa only [originalClause, alphaClause, Formula.encode] using
      allCongr 3 (implicationCongr (CompactHilbertBasis.identity (member 1 3)) h.1)
  have hb : KDerivation (imp alphaClause.encode originalClause.encode) := by
    simpa only [originalClause, alphaClause, Formula.encode] using
      allCongr 3 (implicationCongr (CompactHilbertBasis.identity (member 1 3)) h.2)
  exact ⟨hf,hb⟩

/-- Only after the bound preimage 2 has been renamed to 7, replacing free
source 0→2, target 1→5 and graph 6→8 gives the actual restricted clause.
Naively replacing source 0→2 in the original clause would capture it. -/
theorem restricted_clause_alignment :
    CompactNamed.replace 6 8 (CompactNamed.replace 1 5
      (CompactNamed.replace 0 2 alphaClause)) = restrictedClause := by decide

/-- The quantified target used by the backward-bijection derivation is
exactly the encoded restricted clause after the alpha-safe alignment. -/
theorem restricted_clause_code : restrictedClause.encode =
    allCode 3 (imp (member 5 3) (existsCode 7 restrictedWitness.encode)) := rfl

/-- An independently named preimage binder for the same restricted clause. -/
def alternativeClause : Formula := .all 3 (.imp (.member 5 3)
  (.ex 9 (CompactNamed.replace 7 9 restrictedWitness)))

/-- At the actual restricted source/target/graph names, changing the bound
preimage 7 to fresh 9 preserves the clause by explicit K proof data in both
directions. This is binder alpha conversion, not a substitution of free
parameters or an assertion that a graph exists. -/
def restricted_alpha :
    KDerivation (imp restrictedClause.encode alternativeClause.encode) ×
    KDerivation (imp alternativeClause.encode restrictedClause.encode) := by
  have h := CompactNamed.existentialAlpha 7 9 restrictedWitness
    (by decide) (by decide) (by decide)
  have hf : KDerivation (imp restrictedClause.encode alternativeClause.encode) := by
    simpa only [restrictedClause, alternativeClause, Formula.encode] using
      allCongr 3 (implicationCongr (CompactHilbertBasis.identity (member 5 3)) h.1)
  have hb : KDerivation (imp alternativeClause.encode restrictedClause.encode) := by
    simpa only [restrictedClause, alternativeClause, Formula.encode] using
      allCongr 3 (implicationCongr (CompactHilbertBasis.identity (member 5 3)) h.2)
  exact ⟨hf,hb⟩

theorem original_alpha_forward_certificate : theoremCode (certificate original_alpha.1) =
    imp originalClause.encode alphaClause.encode := certificate_correct original_alpha.1

theorem original_alpha_backward_certificate : theoremCode (certificate original_alpha.2) =
    imp alphaClause.encode originalClause.encode := certificate_correct original_alpha.2

theorem restricted_alpha_forward_certificate : theoremCode (certificate restricted_alpha.1) =
    imp restrictedClause.encode alternativeClause.encode := certificate_correct restricted_alpha.1

theorem restricted_alpha_backward_certificate : theoremCode (certificate restricted_alpha.2) =
    imp alternativeClause.encode restrictedClause.encode := certificate_correct restricted_alpha.2

end PASoundness.PAtoCompactRestrictedBackwardAlpha

#print axioms PASoundness.PAtoCompactRestrictedBackwardAlpha.original_alpha
#print axioms PASoundness.PAtoCompactRestrictedBackwardAlpha.restricted_clause_alignment
#print axioms PASoundness.PAtoCompactRestrictedBackwardAlpha.original_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactRestrictedBackwardAlpha.original_alpha_backward_certificate
#print axioms PASoundness.PAtoCompactRestrictedBackwardAlpha.restricted_alpha
#print axioms PASoundness.PAtoCompactRestrictedBackwardAlpha.restricted_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactRestrictedBackwardAlpha.restricted_alpha_backward_certificate
