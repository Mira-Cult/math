import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactAdjunction
import PASoundness.CompactQuantifiers

/-! Construct the literal proposed addition formula at arguments (30,38,45)
from the specified cut 33 and suffix 40. This is an object-level K proof; it
assumes the four displayed witness facts and does not assert that these facts,
arbitrary addition totality, PA induction, or PA soundness have been proved. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorPackage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The actual proposed addition formula with second summand 38 and result 45. -/
def addition45 : Formula := replace 32 45 (replace 31 38 additionFormula)

private def body : Formula := namedBoth (namedEither (.equal 33 45) (.member 45 33))
  (namedBoth (equivAt 30 33) (namedBoth
    (.all 35 (namedFilterBody 45 34 35 (Formula.member 33 35).not)) (equivAt 38 34)))

private theorem addition_shape : addition45 = .ex 33 (.ex 34 body) := by decide
private theorem instantiated_shape : (replace 34 40 body).encode =
    both (either (equal 33 45) (member 45 33))
      (both (equivAt 30 33).encode
        (both (filterGraph 45 40 35 (neg (member 33 35))) (equivAt 38 40).encode)) := by rfl

/-- A cut belonging to the new result, an isomorphism from the first input to
that cut, its supplied suffix filter, and an isomorphism from the new second
input to that suffix give the exact literal addition relation. -/
def addition_from_cut_suffix : KDerivation
    (imp (member 45 33) (imp (equivAt 30 33).encode
      (imp (filterGraph 45 40 35 (neg (member 33 35)))
        (imp (equivAt 38 40).encode addition45.encode)))) := by
  have hintro34 : KDerivation (imp (replace 34 40 body).encode (existsCode 34 body.encode)) :=
    exists_variable_intro 34 40 body (by decide) (by decide) (by decide)
  have hintro33 : KDerivation (imp (existsCode 34 body.encode) addition45.encode) := by
    have h := CompactNamed.existsIntroduce 33 (.ex 34 body) (by decide)
    simpa only [addition_shape, Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt 38 40).encode, filterGraph 45 40 35 (neg (member 33 35)),
    (equivAt 30 33).encode, member 45 33]
  have heq : Context Γ (equivAt 38 40).encode := .head _ _
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 33 35))) := .hypothesis (by simp [Γ])
  have hc : Context Γ (equivAt 30 33).encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 45 33) := .hypothesis (by simp [Γ])
  have hbody : Context Γ (replace 34 40 body).encode := by
    rw [instantiated_shape]
    exact Context.conjunctionIntro (Context.disjunctionRight hm)
      (Context.conjunctionIntro hc (Context.conjunctionIntro hf heq))
  exact .mp (.mp hbody (.closed hintro34)) (.closed hintro33)

theorem addition_from_cut_suffix_certificate :
    theoremCode (certificate addition_from_cut_suffix) =
      imp (member 45 33) (imp (equivAt 30 33).encode
        (imp (filterGraph 45 40 35 (neg (member 33 35)))
          (imp (equivAt 38 40).encode addition45.encode))) :=
  certificate_correct addition_from_cut_suffix
end PASoundness.PAtoCompactAdditionSuccessorPackage
#print axioms PASoundness.PAtoCompactAdditionSuccessorPackage.addition_from_cut_suffix
#print axioms PASoundness.PAtoCompactAdditionSuccessorPackage.addition_from_cut_suffix_certificate
