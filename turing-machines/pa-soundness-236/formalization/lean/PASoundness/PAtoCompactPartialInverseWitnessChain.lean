import PASoundness.PAtoCompactPartialInverseInsideWitness
import PASoundness.PAtoCompactPrefixAliasImage

/-! Eliminate the endpoint alias and image witnesses in the inside-source
partial-inverse step. The source bijection, successor graph, source
membership and old graph invariant remain explicit antecedents. This does not
eliminate the old graph, establish global induction, or prove a quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseWitnessChain
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPrefixAlias
open PASoundness.PAtoCompactPrefixAliasImage PASoundness.PAtoCompactPartialInverseImageWitness
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactPartialInversePairElim
open PASoundness.PAtoCompactPartialInverseInsideWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact existential next-prefix conclusion, with the new graph bound. -/
def result : Formula := .ex 7 nextInvariant

/-- The image witness can be eliminated while retaining the alias equality,
supplied successor and fixed old graph invariant. -/
def image_elimination : KDerivation
    (imp (existsCode 13 imageWitness)
      (imp (equal 12 8) (imp (successorCode 8 10 15)
        (imp partialInverse.encode result.encode)))) := by
  let I := imageWitness
  let E := equal 12 8
  let S := successorCode 8 10 15
  let P := partialInverse.encode
  let T : Formula := .imp (.equal 12 8) (.imp (namedSuccessor 8 10 15)
    (.imp partialInverse result))
  have hfresh : 13 ∉ T.names := by decide
  have hv : KDerivation (imp T.encode (allCode 13 T.encode)) := T.vacuity 13 hfresh
  have hlocal : KDerivation (imp I T.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,S,E,I]
    have hi : Context Γ I := .hypothesis (by simp [Γ])
    have he : Context Γ E := .hypothesis (by simp [Γ])
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have hu : Context Γ retained.encode :=
      Context.conjunctionIntro hi (Context.conjunctionIntro he (Context.conjunctionIntro hs hp))
    exact .mp hu (.closed pair_and_graph_eliminated)
  apply Context.closeEmpty
  apply Context.deduction
  have hex : Context [existsCode 13 I] (existsCode 13 I) := Context.head [] _
  have hall : Context [existsCode 13 I] (allCode 13 (imp I T.encode)) :=
    .closed (.generalize 13 hlocal)
  exact Context.existsElim hv hall hex

/-- Eliminate the alias and image witnesses supplied together by the exact
bijection/inside-source existential lemma. -/
def alias_image_elimination : KDerivation
    (imp aliasImage (imp (successorCode 8 10 15) (imp partialInverse.encode result.encode))) := by
  let S := successorCode 8 10 15
  let P := partialInverse.encode
  let T : Formula := .imp (namedSuccessor 8 10 15) (.imp partialInverse result)
  have hfresh : 12 ∉ T.names := by decide
  have hv : KDerivation (imp T.encode (allCode 12 T.encode)) := T.vacuity 12 hfresh
  have hlocal : KDerivation (imp (aliasBody imageAtAlias).encode T.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let A := (aliasBody imageAtAlias).encode
    let Γ := [P,S,A]
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have he : Context Γ (equal 12 8) := Context.conjunctionLeft ha
    have hi : Context Γ (existsCode 13 imageWitness) := Context.conjunctionRight ha
    exact .mp hp (.mp hs (.mp he (.mp hi (.closed image_elimination))))
  apply Context.closeEmpty
  apply Context.deduction
  have hex : Context [aliasImage] aliasImage := Context.head [] _
  have hall : Context [aliasImage] (allCode 12 (imp (aliasBody imageAtAlias).encode T.encode)) :=
    .closed (.generalize 12 hlocal)
  exact Context.existsElim hv hall hex

/-- The fixed-old-graph inside-source step, with the required original
bijection retained explicitly. -/
def inside_step_with_old_graph : KDerivation
    (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8) (imp partialInverse.encode result.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let B := bijectionFormula.encode
  let S := successorCode 8 10 15
  let M := member 0 8
  let P := partialInverse.encode
  let Γ := [P,M,S,B]
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hex : Context Γ aliasImage := .mp hm (.mp hb (.closed alias_image_exists))
  exact .mp hp (.mp hs (.mp hex (.closed alias_image_elimination)))

theorem inside_step_with_old_graph_certificate : theoremCode (certificate inside_step_with_old_graph) =
    imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8) (imp partialInverse.encode result.encode))) :=
  certificate_correct inside_step_with_old_graph

end PASoundness.PAtoCompactPartialInverseWitnessChain

#print axioms PASoundness.PAtoCompactPartialInverseWitnessChain.inside_step_with_old_graph
#print axioms PASoundness.PAtoCompactPartialInverseWitnessChain.inside_step_with_old_graph_certificate
