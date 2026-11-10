import PASoundness.PAtoCompactSuffixCleanWidenedWitness
import PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage
import PASoundness.PAtoCompactFirstSpanPathOutside
import PASoundness.PAtoCompactScopedActiveReplace

/-! The supplied clean first suffix bijection and literal filter yield the
collector's first whole-target forward clause. -/
namespace PASoundness.PAtoCompactFirstSuffixCollectorClause

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactSuffixCleanGraphGuard PASoundness.PAtoCompactSuffixGuardedForwardUpgrade
open PASoundness.PAtoCompactSuffixFilterForwardUpgrade PASoundness.PAtoCompactSuffixCleanWitness
open PASoundness.PAtoCompactSuffixCleanWidenedWitness
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem bijection_shape : suffixBijection = namedBoth suffixForward suffixBackward := by decide

private def upgradeFrame : Formula := .imp suffixForward
  (.imp PASoundness.PAtoCompactSuffixFilterForwardUpgrade.suffixFilter (.imp graphClean firstClause))

private def upgrade_cut40 : KDerivation (imp suffixForward.encode
    (imp PASoundness.PAtoCompactFirstSpanPathOutside.suffixFilter.encode
      (imp graphClean.encode firstClause.encode))) := by
  have hbase : KDerivation upgradeFrame.encode := by
    simpa only [upgradeFrame, Formula.encode] using forward_upgrade_from_filter
  have h := replace_derivation 33 40 upgradeFrame (by decide) (by decide) hbase
  have halign : replace 33 40 upgradeFrame = .imp suffixForward
      (.imp PASoundness.PAtoCompactFirstSpanPathOutside.suffixFilter (.imp graphClean firstClause)) := by decide
  rw [halign] at h
  exact h

/-- The actual graph6 and its filter supply firstClause, including uniqueness
against all whole-target competitors. -/
def first_collector_clause : KDerivation (imp firstBijection.encode
    (imp outsideGuard.encode firstClause.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [outsideGuard.encode, firstBijection.encode]
  have hg : Context Γ outsideGuard.encode := .head _ _
  have hb1 : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ suffixBijection.encode := by
    simpa only [firstBijection, PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection,
      suffixBijection] using hb1
  have hclean : Context Γ storedClean.encode := Context.conjunctionLeft hg
  have hfilter : Context Γ PASoundness.PAtoCompactFirstSpanPathOutside.suffixFilter.encode := Context.conjunctionRight hg
  rw [bijection_shape] at hb
  have hforward : Context Γ suffixForward.encode := Context.conjunctionLeft hb
  have hguard : Context Γ graphClean.encode := .mp hclean (.closed stored_clean_graph_guard)
  exact .mp hguard (.mp hfilter (.mp hforward (.closed upgrade_cut40)))

theorem first_collector_clause_certificate : theoremCode (certificate first_collector_clause) =
    imp firstBijection.encode (imp outsideGuard.encode firstClause.encode) := certificate_correct first_collector_clause

end PASoundness.PAtoCompactFirstSuffixCollectorClause

#print axioms PASoundness.PAtoCompactFirstSuffixCollectorClause.first_collector_clause
#print axioms PASoundness.PAtoCompactFirstSuffixCollectorClause.first_collector_clause_certificate
