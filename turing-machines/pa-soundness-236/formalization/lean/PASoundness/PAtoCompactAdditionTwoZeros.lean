import PASoundness.PAtoCompactOrderIsoZero
import PASoundness.PAtoCompactOrdinalAddition

/-! Two explicitly empty objects are isomorphic, in the addition relation's
literal fixed-name syntax. The graph witness comes from the existing finite K
proof for the canonical pair of zero objects; no semantic premise is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionTwoZeros
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactOrderIsoZero PASoundness.PAtoCompactOrdinalAddition
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def zero0 : Formula := .all 36 (Formula.member 0 36).not
private def zero1 : Formula := .all 37 (Formula.member 1 37).not
private def source : Formula := zero0.imp (zero1.imp equivalentFormula)
private def moved : Formula := replace 0 31 source

private def zero0_alpha : KDerivation (imp (zeroCode 0 36) (zeroCode 0 7)) := by
  have h := universalAlpha 36 7 ((Formula.member 0 36).not) (by decide) (by decide) (by decide)
  simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1

private def zero1_alpha : KDerivation (imp (zeroCode 1 37) (zeroCode 1 7)) := by
  have h := universalAlpha 37 7 ((Formula.member 1 37).not) (by decide) (by decide) (by decide)
  simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1

private def source_proved : KDerivation source.encode := by
  let A := zeroCode 0 36
  let B := zeroCode 1 37
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [B,A]
  have ha : Context Γ A := Context.under (Context.head [] A) B
  have hb : Context Γ B := Context.head _ _
  have ha' : Context Γ (zeroCode 0 7) := .mp ha (.closed zero0_alpha)
  have hb' : Context Γ (zeroCode 1 7) := .mp hb (.closed zero1_alpha)
  exact .mp hb' (.mp ha' (.closed two_zeros_equivalent))

private def moved_proved : KDerivation moved.encode := by
  have hi := universalInstance 0 31 source (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 source_proved) hi

/-- The literal addition labels 31 and 34 may use distinct zero-test binders
36 and 37. This proves a K derivation, not a semantic equivalence or an
addition graph existence theorem. -/
def two_zeros_equivalent_addition : KDerivation
    (imp (zeroCode 31 36) (imp (zeroCode 34 37) (equivAt 31 34).encode)) := by
  have hi := universalInstance 1 34 moved (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 1 moved_proved) hi
  simpa [moved, source, zero0, zero1, equivAt, replace, rename, Formula.encode,
    Formula.not, zeroCode, neg] using h

theorem two_zeros_equivalent_addition_certificate :
    theoremCode (certificate two_zeros_equivalent_addition) =
      imp (zeroCode 31 36) (imp (zeroCode 34 37) (equivAt 31 34).encode) :=
  certificate_correct two_zeros_equivalent_addition

end PASoundness.PAtoCompactAdditionTwoZeros

#print axioms PASoundness.PAtoCompactAdditionTwoZeros.two_zeros_equivalent_addition
#print axioms PASoundness.PAtoCompactAdditionTwoZeros.two_zeros_equivalent_addition_certificate
