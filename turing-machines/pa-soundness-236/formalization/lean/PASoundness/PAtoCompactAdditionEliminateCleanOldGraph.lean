import PASoundness.PAtoCompactAdditionCleanEquivWitness
import PASoundness.PAtoCompactAdditionSuccessorWitnessIso
import PASoundness.PAtoCompactAdditionHideGraphWitness

/-! K construction of the new suffix and its equivalence from the actual old
quotient equivalence. The temporary clean old graph and new graph are hidden;
no transitivity of the suffix, addition totality or PA bridge is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionEliminateCleanOldGraph
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactAdditionRightContext PASoundness.PAtoCompactAdditionOldTargetFromBijection
open PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionSuccessorEquivStep PASoundness.PAtoCompactAdditionSuccessorWitnessIso
open PASoundness.PAtoCompactAdditionCleanEquivWitness PASoundness.PAtoCompactAdditionHideGraphWitness
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The old suffix filter, source successor, and transitivity of source and
whole result. No old or new graph is assumed. -/
def graphFreeAssumptions : Formula := namedBoth suffixF (namedBoth sourceS
  (namedBoth (.all 37 (.all 38 (transitiveBody 31 37 38)))
    (.all 37 (.all 38 (transitiveBody 32 37 38)))))

def oldEquiv : Formula := equivAt 31 34
def cleanOld : Formula := namedBoth oldMatrixAt oldClean
def resultSucc : Formula := namedSuccessor 32 45 39
def outsideCut : Formula := (Formula.member 33 32).not
def suffixAndEquiv : Formula := .ex 40 (namedBoth suffixWitness (equivAt 38 40))

private theorem cleanOld_shape : cleanOld =
    (namedBoth (namedBoth (replace 1 34 (replace 0 31 PASoundness.PAtoCompactOrderIsomorphism.bijectionFormula))
      (replace 1 34 (replace 0 31 PASoundness.PAtoCompactOrderIsomorphism.orderFormula)))
      (.all 19 (.imp (.member 6 19)
        (PASoundness.PAtoCompactGraphRestriction.edgePredicate 19 31 34)))) := by decide

private def supplied_graph : KDerivation (imp graphFreeAssumptions.encode
    (imp outsideCut.encode (imp resultSucc.encode
      (imp cleanOld.encode suffixAndEquiv.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [cleanOld.encode,resultSucc.encode,outsideCut.encode,graphFreeAssumptions.encode]
  have hc : Context Γ cleanOld.encode := .head _ _
  have hr : Context Γ resultSucc.encode := .hypothesis (by simp [Γ])
  have hn : Context Γ outsideCut.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ graphFreeAssumptions.encode := .hypothesis (by simp [Γ])
  have hf := Context.conjunctionLeft ha
  have hr1 := Context.conjunctionRight ha
  have hs := Context.conjunctionLeft hr1
  have ht := Context.conjunctionRight hr1
  have hm := Context.conjunctionLeft hc
  have hclean := Context.conjunctionRight hc
  have hh : Context Γ fixedHypotheses.encode := by
    change Context Γ (both suffixF.encode (both oldMatrixAt.encode
      (both oldClean.encode (both sourceS.encode
        (both (transitiveCode 31 37 38) (transitiveCode 32 37 38))))))
    exact Context.conjunctionIntro hf (Context.conjunctionIntro hm
      (Context.conjunctionIntro hclean (Context.conjunctionIntro hs ht)))
  have hw := Context.mp hr (Context.mp hn (Context.mp hh (.closed constructed_witness_equiv)))
  have hresult := Context.mp hw (.closed hide_graph_witnesses)
  exact hresult

/-- From the old quotient equivalence and the literal graph-free assumptions,
K constructs the new suffix and derives its quotient equivalence. The source
successor is name 38 and the whole-result successor is the independent name 45. -/
def eliminate_old_graph : KDerivation (imp oldEquiv.encode
    (imp graphFreeAssumptions.encode (imp outsideCut.encode
      (imp resultSucc.encode suffixAndEquiv.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [resultSucc.encode,outsideCut.encode,graphFreeAssumptions.encode,oldEquiv.encode]
  have hr : Context Γ resultSucc.encode := .head _ _
  have hn : Context Γ outsideCut.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ graphFreeAssumptions.encode := .hypothesis (by simp [Γ])
  have he : Context Γ oldEquiv.encode := .hypothesis (by simp [Γ])
  have hgraph : Context Γ (existsCode 6 cleanOld.encode) := by
    have h := Context.mp he (.closed clean_equiv_witness)
    rw [cleanOld_shape]
    exact h
  have hlocal : Context Γ (imp cleanOld.encode suffixAndEquiv.encode) :=
    .mp hr (.mp hn (.mp ha (.closed supplied_graph)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 6 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h1 : h = resultSucc.encode
    · subst h; exact resultSucc.vacuity 6 (by decide)
    · by_cases h2 : h = outsideCut.encode
      · subst h; exact outsideCut.vacuity 6 (by decide)
      · by_cases h3 : h = graphFreeAssumptions.encode
        · subst h; exact graphFreeAssumptions.vacuity 6 (by decide)
        · have h4 : h = oldEquiv.encode := by simpa [h1,h2,h3] using hh
          subst h; exact free_vacuity 6 oldEquiv (by decide)
  have hall := Context.generalize 6 hv hlocal
  exact Context.existsElim (free_vacuity 6 suffixAndEquiv (by decide)) hall hgraph

theorem eliminate_old_graph_certificate : theoremCode (certificate eliminate_old_graph) =
    imp oldEquiv.encode (imp graphFreeAssumptions.encode (imp outsideCut.encode
      (imp resultSucc.encode suffixAndEquiv.encode))) := certificate_correct eliminate_old_graph
end PASoundness.PAtoCompactAdditionEliminateCleanOldGraph
#print axioms PASoundness.PAtoCompactAdditionEliminateCleanOldGraph.eliminate_old_graph
#print axioms PASoundness.PAtoCompactAdditionEliminateCleanOldGraph.eliminate_old_graph_certificate
