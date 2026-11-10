import PASoundness.PAtoCompactDiagonalNoGarbageStep

/-! Quantified no-garbage preservation for one proposed diagonal graph step.
The successor/adjunction consequences, old invariant, and pair witness remain
explicit antecedents. This does not construct graphs or prove collection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalNoGarbageAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactDiagonalNoGarbageStep PASoundness.PAtoCompactOrderIsomorphism

/-- Every entry of the new graph is the adjoined point or an old entry. -/
def newEntryCases : Nat := allCode 9
  (imp (member 7 9) (either (equal 9 8) (member 6 9)))

/-- Every old graph entry carries an old-domain diagonal pair witness. -/
def oldNoGarbage : Nat := allCode 9 (imp (member 6 9) oldEntry)

/-- Every new graph entry carries a new-domain diagonal pair witness. -/
def newNoGarbage : Nat := allCode 9 (imp (member 7 9) newEntry)

def successorInclusion : Nat := allCode 3 (imp (member 0 3) (member 1 3))

/-- Name 9 does not occur in the explicit successor-inclusion schema. -/
def inclusion_vacuity : KDerivation
    (imp successorInclusion (allCode 9 successorInclusion)) := by
  let f : Formula := .all 3 (.imp (.member 0 3) (.member 1 3))
  have h := f.vacuity 9 (by decide)
  simpa [f, successorInclusion, Formula.encode] using h

/-- Name 9 does not occur in the successor endpoint membership. -/
def endpoint_vacuity : KDerivation
    (imp (member 1 0) (allCode 9 (member 1 0))) := by
  let f : Formula := .member 1 0
  have h := f.vacuity 9 (by decide)
  simpa [f, Formula.encode] using h

/-- Name 9 avoids the supplied diagonal-pair predicate and all its binders. -/
def pair_vacuity : KDerivation
    (imp (pairFormula 8 0 0).encode (allCode 9 (pairFormula 8 0 0).encode)) :=
  (pairFormula 8 0 0).vacuity 9 (by decide)

/-- Under the displayed global hypotheses, the new graph has no non-diagonal
entries. All proof data is object-level K derivability. -/
def no_garbage_all : KDerivation
    (imp newEntryCases (imp oldNoGarbage
      (imp successorInclusion (imp (member 1 0)
        (imp (pairFormula 8 0 0).encode newNoGarbage))))) := by
  let C := newEntryCases
  let O := oldNoGarbage
  let I := successorInclusion
  let K := member 1 0
  let P := (pairFormula 8 0 0).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [P,K,I,O,C]
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hk : Context Γ K := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hallI : Context Γ (allCode 9 I) := .mp hi (.closed inclusion_vacuity)
  have hallK : Context Γ (allCode 9 K) := .mp hk (.closed endpoint_vacuity)
  have hallP : Context Γ (allCode 9 P) := .mp hp (.closed pair_vacuity)
  have h0 := Context.allMP hc (.closed (.generalize 9 no_garbage_step))
  have h1 := Context.allMP ho h0
  have h2 := Context.allMP hallI h1
  have h3 := Context.allMP hallK h2
  exact Context.allMP hallP h3

theorem no_garbage_all_certificate : theoremCode (certificate no_garbage_all) =
    imp newEntryCases (imp oldNoGarbage
      (imp successorInclusion (imp (member 1 0)
        (imp (pairFormula 8 0 0).encode newNoGarbage)))) :=
  certificate_correct no_garbage_all

end PASoundness.PAtoCompactDiagonalNoGarbageAll

#print axioms PASoundness.PAtoCompactDiagonalNoGarbageAll.no_garbage_all
#print axioms PASoundness.PAtoCompactDiagonalNoGarbageAll.no_garbage_all_certificate
