import PASoundness.PAtoCompactAdditionEmptySuffix
import PASoundness.PAtoCompactEquivalentZero
import PASoundness.PAtoCompactOrdinalAddition

/-! Fixed-label whole-cut branch: if a suffix is filtered from a result by
nonmembership in an equal cut, and the second summand is isomorphic to that
suffix, the second summand is zero. No addition output transport, quotient
transitivity or semantic soundness is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactWholeCutZeroTransfer
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionEmptySuffix PASoundness.PAtoCompactEquivalentZero
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def rightZero : Formula := .all 37 (Formula.member 1 37).not
private def leftZero : Formula := .all 36 (Formula.member 0 36).not
private def source : Formula := rightZero.imp (equivalentFormula.imp leftZero)
private def moved : Formula := replace 0 31 source

private def right_zero_alpha : KDerivation (imp (zeroCode 1 37) (zeroCode 1 7)) := by
  have h := universalAlpha 37 7 ((Formula.member 1 37).not) (by decide) (by decide) (by decide)
  simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1

private def left_zero_alpha : KDerivation (imp (zeroCode 0 8) (zeroCode 0 36)) := by
  have h := universalAlpha 8 36 ((Formula.member 0 8).not) (by decide) (by decide) (by decide)
  simpa [zeroCode, Formula.not, Formula.encode, replace, rename, neg] using h.1

private def source_proved : KDerivation source.encode := by
  let Z := zeroCode 1 37
  let E := equivalentFormula.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,Z]
  have he : Context Γ E := .head _ _
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hz' : Context Γ (zeroCode 1 7) := .mp hz (.closed right_zero_alpha)
  have hl : Context Γ (zeroCode 0 8) := .mp he (.mp hz' (.closed equivalent_zero))
  exact .mp hl (.closed left_zero_alpha)

private def moved_proved : KDerivation moved.encode := by
  have hi := universalInstance 0 31 source (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 source_proved) hi

/-- A literal equivalence from summand 31 to empty suffix 34 makes 31 zero.
Both zero binders are explicit, and no values are assumed distinct. -/
def addition_equiv_zero_left : KDerivation
    (imp (zeroCode 34 37) (imp (equivAt 31 34).encode (zeroCode 31 36))) := by
  have hi := universalInstance 1 34 moved (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 1 moved_proved) hi
  simpa [moved, source, rightZero, leftZero, equivAt, replace, rename, Formula.encode,
    Formula.not, zeroCode, neg] using h

/-- For a genuine equal cut 33=result 32 and its supplied suffix filter,
if right summand 31 is isomorphic to suffix 34, then summand 31 is zero.
The displayed syntactic names are distinct; their values may coincide. -/
def whole_cut_right_zero : KDerivation
    (imp (equal 33 32)
      (imp (filterGraph 32 34 35 (neg (member 33 35)))
        (imp (equivAt 31 34).encode (zeroCode 31 36)))) := by
  let E := equal 33 32
  let F := filterGraph 32 34 35 (neg (member 33 35))
  let Q := (equivAt 31 34).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [Q,F,E]
  have hq : Context Γ Q := .head _ _
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have he' : Context Γ (equal 32 33) := .mp he (.closed (equalitySymmetry 33 32))
  have hz : Context Γ (zeroCode 34 37) :=
    .mp hf (.mp he' (.closed (equal_cut_empty_suffix 32 33 34 35 37 (by decide))))
  exact .mp hq (.mp hz (.closed addition_equiv_zero_left))

theorem addition_equiv_zero_left_certificate :
    theoremCode (certificate addition_equiv_zero_left) =
      imp (zeroCode 34 37) (imp (equivAt 31 34).encode (zeroCode 31 36)) :=
  certificate_correct addition_equiv_zero_left

theorem whole_cut_right_zero_certificate :
    theoremCode (certificate whole_cut_right_zero) =
      imp (equal 33 32) (imp (filterGraph 32 34 35 (neg (member 33 35)))
        (imp (equivAt 31 34).encode (zeroCode 31 36))) :=
  certificate_correct whole_cut_right_zero

end PASoundness.PAtoCompactWholeCutZeroTransfer

#print axioms PASoundness.PAtoCompactWholeCutZeroTransfer.addition_equiv_zero_left
#print axioms PASoundness.PAtoCompactWholeCutZeroTransfer.whole_cut_right_zero
#print axioms PASoundness.PAtoCompactWholeCutZeroTransfer.addition_equiv_zero_left_certificate
#print axioms PASoundness.PAtoCompactWholeCutZeroTransfer.whole_cut_right_zero_certificate
