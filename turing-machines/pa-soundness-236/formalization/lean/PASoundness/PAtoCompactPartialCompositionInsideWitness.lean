import PASoundness.PAtoCompactCompositionSuppliedCombine
import PASoundness.PAtoCompactPartialCompositionPairElim

/-! Pair and graph witness elimination for a supplied inside-source partial
composition step. Both coverage directions remain explicit finite K proof-data
arguments. The selected images, successor and old invariant remain antecedents;
this does not assert full successor extension, induction, or graph collection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionInsideWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactCompositionSelectedImages PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.PAtoCompactCompositionSuppliedVacuity PASoundness.PAtoCompactCompositionSuppliedCombine
open PASoundness.PAtoCompactPartialCompositionPairElim
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The selected image witnesses, prefix successor and old invariant retained
when the pair and new graph are quantified and eliminated. -/
def retained : Formula := namedBoth firstImageBody (namedBoth secondImageBody
  (namedBoth (namedSuccessor 10 13 15) partialComposition))

theorem retained_fresh_16 : 16 ∉ retained.names := by decide
theorem retained_fresh_17 : 17 ∉ retained.names := by decide

theorem next_rename_alignment : nextPartial = nextInvariant17 := by decide

/-- Reassemble the full supplied premise under the curried pair/graph inputs. -/
def curried_step
    (forward : KDerivation (imp suppliedPremises.encode forwardCoverage.encode))
    (backward : KDerivation (imp suppliedPremises.encode backwardCoverage.encode)) :
    KDerivation (imp retained.encode (imp (pairFormula 16 10 12).encode
      (imp (adjoinCode 9 16 17 18) nextInvariant17.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [adjoinCode 9 16 17 18,(pairFormula 16 10 12).encode,retained.encode]
  have ha : Context Γ (adjoinCode 9 16 17 18) := Context.head _ _
  have hp : Context Γ (pairFormula 16 10 12).encode := .hypothesis (by simp [Γ])
  have hr : Context Γ retained.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstImageBody.encode := Context.conjunctionLeft hr
  have ht1 := Context.conjunctionRight hr
  have hs : Context Γ secondImageBody.encode := Context.conjunctionLeft ht1
  have ht2 := Context.conjunctionRight ht1
  have hsuc : Context Γ (successorCode 10 13 15) := Context.conjunctionLeft ht2
  have hold : Context Γ partialComposition.encode := Context.conjunctionRight ht2
  have hsupplied : Context Γ suppliedPremises.encode :=
    Context.conjunctionIntro hf (Context.conjunctionIntro hs
      (Context.conjunctionIntro hsuc (Context.conjunctionIntro hp
        (Context.conjunctionIntro ha hold))))
  have hn : Context Γ nextPartial.encode := .mp hsupplied (.closed (combine forward backward))
  rw [← next_rename_alignment]
  exact hn

/-- Construct/eliminate the pair and new graph, conditional on both exact
coverage proofs and the retained image, successor, and old-invariant inputs. -/
def retained_graph_exists
    (forward : KDerivation (imp suppliedPremises.encode forwardCoverage.encode))
    (backward : KDerivation (imp suppliedPremises.encode backwardCoverage.encode)) :
    KDerivation (imp retained.encode (existsCode 9 nextInvariant.encode)) :=
  eliminate_pair_and_graph retained retained_fresh_17 retained_fresh_16
    (curried_step forward backward)

/-- The same result with the four object-level inputs in curried order. -/
def inside_witness
    (forward : KDerivation (imp suppliedPremises.encode forwardCoverage.encode))
    (backward : KDerivation (imp suppliedPremises.encode backwardCoverage.encode)) :
    KDerivation (imp firstImageBody.encode (imp secondImageBody.encode
      (imp (successorCode 10 13 15) (imp partialComposition.encode
        (existsCode 9 nextInvariant.encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [partialComposition.encode,successorCode 10 13 15,
    secondImageBody.encode,firstImageBody.encode]
  have ho : Context Γ partialComposition.encode := Context.head _ _
  have hsuc : Context Γ (successorCode 10 13 15) := .hypothesis (by simp [Γ])
  have hs : Context Γ secondImageBody.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstImageBody.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ retained.encode := Context.conjunctionIntro hf
    (Context.conjunctionIntro hs (Context.conjunctionIntro hsuc ho))
  exact .mp hr (.closed (retained_graph_exists forward backward))

theorem inside_witness_certificate
    (forward : KDerivation (imp suppliedPremises.encode forwardCoverage.encode))
    (backward : KDerivation (imp suppliedPremises.encode backwardCoverage.encode)) :
    theoremCode (certificate (inside_witness forward backward)) =
      imp firstImageBody.encode (imp secondImageBody.encode
        (imp (successorCode 10 13 15) (imp partialComposition.encode
          (existsCode 9 nextInvariant.encode)))) :=
  certificate_correct (inside_witness forward backward)

end PASoundness.PAtoCompactPartialCompositionInsideWitness

#print axioms PASoundness.PAtoCompactPartialCompositionInsideWitness.inside_witness
#print axioms PASoundness.PAtoCompactPartialCompositionInsideWitness.inside_witness_certificate
