import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers

/-! Pointwise target uniqueness for a composed path at a selected prefix
endpoint. Both image-uniqueness clauses, source equality and all displayed
membership and graph hypotheses are explicit; no composite graph or choice
function is constructed. Code 1 is literal compact bottom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionOutputUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- Image 11 is unique for first-graph source 10 among members of 1. -/
def firstUnique : Formula := .all 4 (.imp
  (conj (.member 1 4) (graphFormula 6 10 4)) (.equal 4 11))

/-- Image 12 is unique for second-graph source 11 among members of 8. -/
def secondUnique : Formula := .all 4 (.imp
  (conj (.member 8 4) (graphFormula 7 11 4)) (.equal 4 12))

/-- Under the two supplied unique-image clauses, a queried guarded path with
source 2 equal to selected prefix 10 has target 3 equal to selected target 12.
Name 4 represents the queried intermediate; all graph-internal binders are
19–22 and no inequality of represented values is assumed. -/
def selected_output_unique : KDerivation
    (imp firstUnique.encode (imp secondUnique.encode (imp (equal 2 10)
      (imp (member 1 4) (imp (graphFormula 6 2 4).encode
        (imp (member 8 3) (imp (graphFormula 7 4 3).encode (equal 3 12)))))))) := by
  let fb : Formula := .imp
    (conj (.member 1 4) (graphFormula 6 10 4)) (.equal 4 11)
  let sb : Formula := .imp
    (conj (.member 8 4) (graphFormula 7 11 4)) (.equal 4 12)
  have hf : KDerivation (imp firstUnique.encode fb.encode) :=
    allSpecialize 4 fb (by decide)
  have hs := universalInstance 4 3 sb (by decide) (by decide) (by decide)
  have hss : replace 4 3 sb = .imp
      (conj (.member 8 3) (graphFormula 7 11 3)) (.equal 3 12) := by decide
  rw [hss] at hs
  have hsrc := (equalityReplace 2 10 (graphFormula 6 2 4) (by decide) (by decide)).1
  have hsrc' : replace 2 10 (graphFormula 6 2 4) = graphFormula 6 10 4 := by decide
  rw [hsrc'] at hsrc
  have hmid := (equalityReplace 4 11 (graphFormula 7 4 3) (by decide) (by decide)).1
  have hmid' : replace 4 11 (graphFormula 7 4 3) = graphFormula 7 11 3 := by decide
  rw [hmid'] at hmid
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 7 4 3).encode, member 8 3,
    (graphFormula 6 2 4).encode, member 1 4, equal 2 10,
    secondUnique.encode, firstUnique.encode]
  have hg2 : Context Γ (graphFormula 7 4 3).encode := Context.head _ _
  have hc : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have hg1 : Context Γ (graphFormula 6 2 4).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 1 4) := .hypothesis (by simp [Γ])
  have he : Context Γ (equal 2 10) := .hypothesis (by simp [Γ])
  have hu2 : Context Γ secondUnique.encode := .hypothesis (by simp [Γ])
  have hu1 : Context Γ firstUnique.encode := .hypothesis (by simp [Γ])
  have hg1' : Context Γ (graphFormula 6 10 4).encode := .mp hg1 (.mp he (.closed hsrc))
  have hu1' : Context Γ (imp (both (member 1 4) (graphFormula 6 10 4).encode)
      (equal 4 11)) := .mp hu1 (.closed hf)
  have heq : Context Γ (equal 4 11) := .mp (Context.conjunctionIntro hb hg1') hu1'
  have hg2' : Context Γ (graphFormula 7 11 3).encode := .mp hg2 (.mp heq (.closed hmid))
  have hu2' : Context Γ (imp (both (member 8 3) (graphFormula 7 11 3).encode)
      (equal 3 12)) := .mp hu2 (.closed hs)
  exact .mp (Context.conjunctionIntro hc hg2') hu2'

theorem selected_output_unique_certificate :
    theoremCode (certificate selected_output_unique) =
      imp firstUnique.encode (imp secondUnique.encode (imp (equal 2 10)
        (imp (member 1 4) (imp (graphFormula 6 2 4).encode
          (imp (member 8 3) (imp (graphFormula 7 4 3).encode (equal 3 12))))))) :=
  certificate_correct selected_output_unique

end PASoundness.PAtoCompactPartialCompositionOutputUnique

#print axioms PASoundness.PAtoCompactPartialCompositionOutputUnique.selected_output_unique
#print axioms PASoundness.PAtoCompactPartialCompositionOutputUnique.selected_output_unique_certificate
