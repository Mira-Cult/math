import PASoundness.PAtoCompactBijectionBackwardPreimage

/-! Pointwise preimage for the supplied suffix bijection in the multiplication
successor construction. This constructs finite K proof data from the literal
bijection and target membership, and retains the same graph. It does not
construct a row graph, prove multiplication totality or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixPreimageFive
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactBijectionBackwardPreimage
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Source 31, target 40 and graph 6 in the literal bijection formula. -/
def suffixBijection : Formula := replace 1 40 (replace 0 31 bijectionFormula)

/-- A guarded preimage at name `i`, queried at target name 5, with its
source-uniqueness clause; the graph remains the supplied graph 6. -/
def suffixWitness (i : Nat) : Formula := namedBoth (.member 31 i)
  (namedBoth (graphFormula 6 i 5)
    (.all 4 (.imp (namedBoth (.member 31 4) (graphFormula 6 4 5)) (.equal 4 i))))

/-- The same preimage, with its uniqueness clause projected away. -/
def preimageBody (i : Nat) : Formula :=
  namedBoth (.member 31 i) (graphFormula 6 i 5)

private def original : Formula := .imp bijectionFormula
  (.imp (.member 1 5) (.ex 7 (witnessBody 7 5)))

private def original_proof : KDerivation original.encode := by
  change KDerivation (imp bijectionFormula.encode
    (imp (member 1 5) (existsCode 7 (witnessBody 7 5).encode)))
  exact backward_preimage

private def moved : Formula := replace 0 31 original

private def proof_at31 : KDerivation moved.encode := by
  have hi := universalInstance 0 31 original (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 original_proof) hi

private def witness7 : KDerivation (imp suffixBijection.encode
    (imp (member 40 5) (existsCode 7 (suffixWitness 7).encode))) := by
  have hi := universalInstance 1 40 moved (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 1 proof_at31) hi
  have hs : replace 1 40 moved = .imp suffixBijection
      (.imp (.member 40 5) (.ex 7 (suffixWitness 7))) := by decide
  rw [hs] at hc
  exact hc

/-- Each target member has a source-guarded preimage with uniqueness. Name 41
is fresh for the free row-graph name 7 used by subsequent constructions. -/
def suffix_preimage_with_unique : KDerivation (imp suffixBijection.encode
    (imp (member 40 5) (existsCode 41 (suffixWitness 41).encode))) := by
  have ha := (existentialAlpha 7 41 (suffixWitness 7)
    (by decide) (by decide) (by decide)).1
  have hs : replace 7 41 (suffixWitness 7) = suffixWitness 41 := by decide
  rw [hs] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 40 5, suffixBijection.encode]
  have hm : Context Γ (member 40 5) := .head _ _
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 7 (suffixWitness 7).encode) :=
    .mp hm (.mp hb (.closed witness7))
  exact .mp hw (.closed ha)

/-- Each target member has a source-guarded graph preimage. No cleanliness
premise is needed for this direction. -/
def suffix_preimage : KDerivation (imp suffixBijection.encode
    (imp (member 40 5) (existsCode 41 (preimageBody 41).encode))) := by
  have hp : KDerivation (imp (suffixWitness 41).encode (preimageBody 41).encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let W := (suffixWitness 41).encode
    have hw : Context [W] W := .head [] _
    change Context [W] (both (member 31 41)
      (both (graphFormula 6 41 5).encode _)) at hw
    have h := Context.conjunctionIntro (Context.conjunctionLeft hw)
      (Context.conjunctionLeft (Context.conjunctionRight hw))
    simpa [preimageBody,namedBoth,Formula.encode,Formula.not,both,neg] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 40 5, suffixBijection.encode]
  have hm : Context Γ (member 40 5) := .head _ _
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  exact .mp (.mp hm (.mp hb (.closed suffix_preimage_with_unique)))
    (.closed (existsCongr 41 hp))

theorem suffix_preimage_with_unique_certificate :
    theoremCode (certificate suffix_preimage_with_unique) = imp suffixBijection.encode
      (imp (member 40 5) (existsCode 41 (suffixWitness 41).encode)) :=
  certificate_correct suffix_preimage_with_unique

theorem suffix_preimage_certificate : theoremCode (certificate suffix_preimage) =
    imp suffixBijection.encode (imp (member 40 5) (existsCode 41 (preimageBody 41).encode)) :=
  certificate_correct suffix_preimage
end PASoundness.PAtoCompactMultiplicationSuffixPreimageFive
#print axioms PASoundness.PAtoCompactMultiplicationSuffixPreimageFive.suffix_preimage_with_unique
#print axioms PASoundness.PAtoCompactMultiplicationSuffixPreimageFive.suffix_preimage
#print axioms PASoundness.PAtoCompactMultiplicationSuffixPreimageFive.suffix_preimage_with_unique_certificate
#print axioms PASoundness.PAtoCompactMultiplicationSuffixPreimageFive.suffix_preimage_certificate
