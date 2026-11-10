import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactStagedEquivalenceAligned
import PASoundness.PAtoCompactDynamicTransitivityFinal

/-! Fixed-name quotient transitivity for the two components of a member-cut
addition witness. The target cut/suffix equivalences and both operand-domain
predicates are supplied; no suffix graph or addition output is constructed. -/
namespace PASoundness.PAtoCompactMemberCutQuotientChains
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactDynamicTransitivityFinal
open PASoundness.PAtoCompactStagedEquivalenceAlpha PASoundness.PAtoCompactStagedEquivalenceAligned

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The original literal addition witnesses use fixed cut 33 and suffix 34.
The two supplied allocated equivalences point from these original witnesses
to target cut 41 and target suffix 38. Values denoted by names may coincide. -/
def guard : Formula := namedBoth (domainAt 100 30) (namedBoth (domainAt 100 31)
  (namedBoth (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33)
    (namedBoth (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34)
      (namedBoth (equivAt 100 33 41) (equivAt 100 34 38)))))

def allocatedConclusion : Formula := namedBoth (equivAt 100 30 41) (equivAt 100 31 38)
def rawConclusion : Formula := namedBoth (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 41)
  (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 38)

private theorem old_cut_shape : PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33 =
    rawStaged 30 33 := by decide
private theorem old_suffix_shape : PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34 =
    rawStaged 31 34 := by decide
private theorem new_cut_shape : PASoundness.PAtoCompactOrdinalAddition.equivAt 30 41 =
    rawStaged 30 41 := by decide
private theorem new_suffix_shape : PASoundness.PAtoCompactOrdinalAddition.equivAt 31 38 =
    rawStaged 31 38 := by decide

/-- Compose the supplied original component isomorphisms with the supplied
cut and suffix isomorphisms. Candidate domains are needed only for the two
left endpoints 30 and 31; no distinctness of values is assumed. -/
def allocated_chains : KDerivation (imp guard.encode allocatedConclusion.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hd30 : Context Γ (domainAt 100 30).encode := Context.conjunctionLeft hg
  have h1 := Context.conjunctionRight hg
  have hd31 : Context Γ (domainAt 100 31).encode := Context.conjunctionLeft h1
  have h2 := Context.conjunctionRight h1
  have hrawCut0 : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode :=
    Context.conjunctionLeft h2
  have h3 := Context.conjunctionRight h2
  have hrawSuffix0 : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode :=
    Context.conjunctionLeft h3
  have h4 := Context.conjunctionRight h3
  have hcut : Context Γ (equivAt 100 33 41).encode := Context.conjunctionLeft h4
  have hsuffix : Context Γ (equivAt 100 34 38).encode := Context.conjunctionRight h4
  have hrawCut : Context Γ (rawStaged 30 33).encode := by simpa only [old_cut_shape] using hrawCut0
  have hrawSuffix : Context Γ (rawStaged 31 34).encode := by simpa only [old_suffix_shape] using hrawSuffix0
  have holdCut : Context Γ (equivAt 100 30 33).encode := .mp hrawCut
    (.closed (staged_to_allocated 30 33 (by decide) (by decide) (by decide) (by decide) (by decide)))
  have holdSuffix : Context Γ (equivAt 100 31 34).encode := .mp hrawSuffix
    (.closed (staged_to_allocated 31 34 (by decide) (by decide) (by decide) (by decide) (by decide)))
  have hnewCut : Context Γ (equivAt 100 30 41).encode :=
    .mp hcut (.mp holdCut (.mp hd30 (.closed (dynamic_transitivity 100 30 33 41 (by decide) (by decide) (by decide)))))
  have hnewSuffix : Context Γ (equivAt 100 31 38).encode :=
    .mp hsuffix (.mp holdSuffix (.mp hd31 (.closed (dynamic_transitivity 100 31 34 38 (by decide) (by decide) (by decide)))))
  exact Context.conjunctionIntro hnewCut hnewSuffix

/-- The same conclusions in the original literal addition syntax. -/
def raw_chains : KDerivation (imp guard.encode rawConclusion.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hc : Context Γ allocatedConclusion.encode := .mp hg (.closed allocated_chains)
  have hcut : Context Γ (equivAt 100 30 41).encode := Context.conjunctionLeft hc
  have hsuffix : Context Γ (equivAt 100 31 38).encode := Context.conjunctionRight hc
  have hrawCut : Context Γ (rawStaged 30 41).encode := .mp hcut
    (.closed (allocated_to_staged 30 41 (by decide) (by decide) (by decide) (by decide) (by decide)))
  have hrawSuffix : Context Γ (rawStaged 31 38).encode := .mp hsuffix
    (.closed (allocated_to_staged 31 38 (by decide) (by decide) (by decide) (by decide) (by decide)))
  have hc' : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 41).encode := by
    simpa only [new_cut_shape] using hrawCut
  have hs' : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 38).encode := by
    simpa only [new_suffix_shape] using hrawSuffix
  exact Context.conjunctionIntro hc' hs'

theorem allocated_chains_certificate : theoremCode (certificate allocated_chains) =
    imp guard.encode allocatedConclusion.encode := certificate_correct allocated_chains

theorem raw_chains_certificate : theoremCode (certificate raw_chains) =
    imp guard.encode rawConclusion.encode := certificate_correct raw_chains

end PASoundness.PAtoCompactMemberCutQuotientChains

#print axioms PASoundness.PAtoCompactMemberCutQuotientChains.allocated_chains
#print axioms PASoundness.PAtoCompactMemberCutQuotientChains.raw_chains
#print axioms PASoundness.PAtoCompactMemberCutQuotientChains.allocated_chains_certificate
#print axioms PASoundness.PAtoCompactMemberCutQuotientChains.raw_chains_certificate
