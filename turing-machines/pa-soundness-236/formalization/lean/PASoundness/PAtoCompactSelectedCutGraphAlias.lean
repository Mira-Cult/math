import PASoundness.PAtoCompactSelectedCutGraphTransport
import PASoundness.PAtoCompactEquivalentEndpointAlias

/-! Retain the selected proper-cut image and its original graph edge while
converting the prepared segment isomorphism to the explicitly guarded
canonical alias formula. This does not construct a suffix isomorphism. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSelectedCutGraphAlias
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictedEquivalentTarget
open PASoundness.PAtoCompactEquivalentAliasInstantiation PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactLessRightSegmentTransport PASoundness.PAtoCompactSelectedCutGraphTransport
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- All components use the same target cut name 5 and the original graph 6.
The canonical isomorphism is under its explicit fresh-alias equality guards. -/
def selectedAliasBody : Formula := namedBoth image5 (guarded originalAliases)
def selectedAlias : Formula := .ex 5 selectedAliasBody

/-- Explicit K conversion of the prepared segment isomorphism into its
canonical guarded alias form, without discarding the original image edge. -/
def selected_cut_graph_alias : KDerivation
    (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp orderFormula.encode (imp bijectionFormula.encode selectedAlias.encode))))) := by
  have hp : KDerivation (imp selectedCutBody.encode selectedAliasBody.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [selectedCutBody.encode]
    have h : Context Γ selectedCutBody.encode := .head _ _
    have hi : Context Γ image5.encode := Context.conjunctionLeft h
    have he : Context Γ endpointTarget.encode := Context.conjunctionRight h
    have ha : Context Γ (guarded originalAliases).encode :=
      .mp he (.closed PASoundness.PAtoCompactEquivalentEndpointAlias.backward)
    simpa only [selectedAliasBody, namedBoth, Formula.not, Formula.encode,
      CompactProof.both, CompactProof.neg] using Context.conjunctionIntro hi ha
  have hlift : KDerivation (imp selectedCut.encode selectedAlias.encode) := by
    change KDerivation (imp (existsCode 5 selectedCutBody.encode)
      (existsCode 5 selectedAliasBody.encode))
    exact existsCongr 5 hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [bijectionFormula.encode,orderFormula.encode,sourceMember,targetTrans,sourceTrans]
  have hi : Context Γ bijectionFormula.encode := .head _ _
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ sourceMember := .hypothesis (by simp [Γ])
  have ht : Context Γ targetTrans := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have hcut : Context Γ selectedCut.encode :=
    .mp hi (.mp ho (.mp hc (.mp ht (.mp hs (.closed selected_cut_graph_transport)))))
  exact .mp hcut (.closed hlift)

theorem selected_cut_graph_alias_certificate :
    theoremCode (certificate selected_cut_graph_alias) =
      imp sourceTrans (imp targetTrans (imp sourceMember
        (imp orderFormula.encode (imp bijectionFormula.encode selectedAlias.encode)))) :=
  certificate_correct selected_cut_graph_alias

end PASoundness.PAtoCompactSelectedCutGraphAlias

#print axioms PASoundness.PAtoCompactSelectedCutGraphAlias.selected_cut_graph_alias
#print axioms PASoundness.PAtoCompactSelectedCutGraphAlias.selected_cut_graph_alias_certificate
