import PASoundness.PAtoCompactMemberChosenConditional
import PASoundness.PAtoCompactSelectedCutOutputMatrix

/-! Eliminate the actual whole-output isomorphism graph only after a supplied
same-graph construction has produced both selected target witnesses. The
same-graph proof remains an explicit proof-data input. -/
namespace PASoundness.PAtoCompactMemberChosenGraphElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactMemberCutSelectedTarget PASoundness.PAtoCompactSelectedCutOutputMatrix
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem chosen_free_60 : 60 ∉ chosen.free := by
  have hcut : 60 ∉ (equivAt 100 33 41).free := by
    intro h
    have hh := equivAt_free 100 33 41 h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh <;> omega
  have hsuffix : 60 ∉ (equivAt 100 34 38).free := by
    intro h
    have hh := equivAt_free 100 34 38 h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh <;> omega
  have hmember : 60 ∉ (Formula.member 8 41).free := by decide
  have hfilter : 60 ∉ PAtoCompactMemberCutRawTargetIntro.targetSuffix.free := by decide
  have hbody : 60 ∉ chosenBody.free := by
    intro h
    simp only [chosenBody,namedBoth,Formula.free,Finset.union_empty,Finset.empty_union,Finset.mem_union] at h
    rcases h with h | h | h | h
    · exact hcut h
    · exact hsuffix h
    · exact hmember h
    · exact hfilter h
  intro h
  simp only [chosen,Formula.free,Finset.mem_erase] at h
  exact hbody h.2.2

/-- If a guard and one actual graph matrix suffice to construct `chosen`,
then the guard and the allocated whole-output equivalence suffice. The graph
witness 60 is retained until `chosen` is obtained. The syntactic freshness
of the guard and the same-graph proof are explicit inputs. -/
def chosen_from_output_graph (g : Formula) (hg60 : 60 ∉ g.free)
    (underGraph : KDerivation (imp g.encode (imp graphMatrix.encode chosen.encode))) :
    KDerivation (imp g.encode (imp (equivAt 100 32 8).encode chosen.encode)) := by
  let Γ := [g.encode]
  have hg : Context Γ g.encode := .head _ _
  have hpoint : Context (graphMatrix.encode :: Γ) chosen.encode := by
    have hm : Context (graphMatrix.encode :: Γ) graphMatrix.encode := .head _ _
    exact .mp hm (.mp (.under hg _) (.closed underGraph))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 60 h)) := by
    intro h hh
    have he : h = g.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 60 g hg60
  have hall := Context.generalize 60 hv (Context.deduction hpoint)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Δ := [(equivAt 100 32 8).encode,g.encode]
  have he : Context Δ (equivAt 100 32 8).encode := .head _ _
  have hex : Context Δ (existsCode 60 graphMatrix.encode) := by
    have h := Context.mp he (.closed graph_from_output_equivalence)
    simpa only [graphWitness,Formula.encode] using h
  exact Context.existsElim (free_vacuity 60 chosen chosen_free_60) (.under hall _) hex

theorem chosen_from_output_graph_certificate (g : Formula) (hg60 : 60 ∉ g.free)
    (underGraph : KDerivation (imp g.encode (imp graphMatrix.encode chosen.encode))) :
    theoremCode (certificate (chosen_from_output_graph g hg60 underGraph)) =
      imp g.encode (imp (equivAt 100 32 8).encode chosen.encode) := certificate_correct _
end PASoundness.PAtoCompactMemberChosenGraphElim

#print axioms PASoundness.PAtoCompactMemberChosenGraphElim.chosen_from_output_graph
#print axioms PASoundness.PAtoCompactMemberChosenGraphElim.chosen_from_output_graph_certificate
