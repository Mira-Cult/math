import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor

/-! Conditional, capture-safe instantiation of the proposed diagonal graph
soundness schema. This module assumes the schema; it does not establish a
graph, diagonal invariant, or equivalence relation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalSoundInstance
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism

/-- Strong diagonal soundness names: every graph edge has a source in 0 and
equal endpoints. This is a premise, not asserted as a theorem here. -/
def strongSoundness : Formula := .all 28 (.all 29
  (.imp (graphFormula 6 28 29) (namedBoth (.member 0 28) (.equal 28 29))))

/-- Its equality-only projection, convenient for bijection/order clauses. -/
def equalSoundness : Formula := .all 28 (.all 29
  (.imp (graphFormula 6 28 29) (.equal 28 29)))

/-- Projection is a finite K proof; no semantic model is invoked. -/
def strong_to_equal : KDerivation (imp strongSoundness.encode equalSoundness.encode) := by
  let G := (graphFormula 6 28 29).encode
  let M := member 0 28
  let E := equal 28 29
  have hlocal : KDerivation (imp (imp G (both M E)) (imp G E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have hg : Context [G, imp G (both M E)] G := Context.head _ _
    have hi : Context [G, imp G (both M E)] (imp G (both M E)) := .hypothesis (by simp)
    exact Context.conjunctionRight (.mp hg hi)
  exact allCongr 28 (allCongr 29 hlocal)

/-- Instance (2,3) of the equality-only soundness schema. -/
def instance_23 : KDerivation (imp equalSoundness.encode
    (imp (graphFormula 6 2 3).encode (equal 2 3))) := by
  let F : Formula := .imp (graphFormula 6 28 29) (.equal 28 29)
  let F2 : Formula := .imp (graphFormula 6 2 29) (.equal 2 29)
  have h1 := CompactNamed.universalInstance 28 2 (.all 29 F) (by decide) (by decide) (by decide)
  have hr1 : CompactNamed.replace 28 2 (.all 29 F) = .all 29 F2 := by decide
  rw [hr1] at h1
  have h2 := CompactNamed.universalInstance 29 3 F2 (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 29 3 F2 = .imp (graphFormula 6 2 3) (.equal 2 3) := by decide
  rw [hr2] at h2
  exact compose h1 h2

/-- Instance (2,4) of the equality-only soundness schema. -/
def instance_24 : KDerivation (imp equalSoundness.encode
    (imp (graphFormula 6 2 4).encode (equal 2 4))) := by
  let F : Formula := .imp (graphFormula 6 28 29) (.equal 28 29)
  let F2 : Formula := .imp (graphFormula 6 2 29) (.equal 2 29)
  have h1 := CompactNamed.universalInstance 28 2 (.all 29 F) (by decide) (by decide) (by decide)
  have hr1 : CompactNamed.replace 28 2 (.all 29 F) = .all 29 F2 := by decide
  rw [hr1] at h1
  have h2 := CompactNamed.universalInstance 29 4 F2 (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 29 4 F2 = .imp (graphFormula 6 2 4) (.equal 2 4) := by decide
  rw [hr2] at h2
  exact compose h1 h2

/-- Instance (4,3) of the equality-only soundness schema. -/
def instance_43 : KDerivation (imp equalSoundness.encode
    (imp (graphFormula 6 4 3).encode (equal 4 3))) := by
  let F : Formula := .imp (graphFormula 6 28 29) (.equal 28 29)
  let F4 : Formula := .imp (graphFormula 6 4 29) (.equal 4 29)
  have h1 := CompactNamed.universalInstance 28 4 (.all 29 F) (by decide) (by decide) (by decide)
  have hr1 : CompactNamed.replace 28 4 (.all 29 F) = .all 29 F4 := by decide
  rw [hr1] at h1
  have h2 := CompactNamed.universalInstance 29 3 F4 (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 29 3 F4 = .imp (graphFormula 6 4 3) (.equal 4 3) := by decide
  rw [hr2] at h2
  exact compose h1 h2

theorem sound_instance_certificates :
    theoremCode (certificate strong_to_equal) = imp strongSoundness.encode equalSoundness.encode ∧
    theoremCode (certificate instance_23) = imp equalSoundness.encode
      (imp (graphFormula 6 2 3).encode (equal 2 3)) ∧
    theoremCode (certificate instance_24) = imp equalSoundness.encode
      (imp (graphFormula 6 2 4).encode (equal 2 4)) ∧
    theoremCode (certificate instance_43) = imp equalSoundness.encode
      (imp (graphFormula 6 4 3).encode (equal 4 3)) :=
  ⟨certificate_correct strong_to_equal, certificate_correct instance_23,
    certificate_correct instance_24, certificate_correct instance_43⟩

end PASoundness.PAtoCompactDiagonalSoundInstance

#print axioms PASoundness.PAtoCompactDiagonalSoundInstance.strong_to_equal
#print axioms PASoundness.PAtoCompactDiagonalSoundInstance.instance_23
#print axioms PASoundness.PAtoCompactDiagonalSoundInstance.instance_24
#print axioms PASoundness.PAtoCompactDiagonalSoundInstance.instance_43
#print axioms PASoundness.PAtoCompactDiagonalSoundInstance.sound_instance_certificates
