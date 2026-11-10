import PASoundness.PAtoCompactAdditionOldSourceEdge
import PASoundness.PAtoCompactAdditionSuccessorGraphClean

/-! Transfer guarded old-target uniqueness for an old source to the graph
extended with the unequal top pair. The old uniqueness, old clean graph,
source membership, pair and graph adjunction are explicit K hypotheses. This
is not graph existence or the complete old-source witness transfer. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldSourceUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldSourceEdge
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldUniquePoint : Nat := imp (both (member 34 4) (graphFormula 6 2 4).encode) (equal 4 3)
def oldUnique : Nat := allCode 4 oldUniquePoint

def competitor_unique : KDerivation (imp oldUniquePoint (imp oldClean.encode
    (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp (member 31 2) (imp (graphFormula 9 2 4).encode (equal 4 3))))))) := by
  let U := oldUniquePoint
  let C := oldClean.encode
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let M := member 31 2
  let G := (graphFormula 9 2 4).encode
  let O := (graphFormula 6 2 4).encode
  let Γ := [G,M,P,A,C,U]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .head _ _
  have ho : Context Γ O := .mp hg (.mp hm (.mp hp (.mp ha (.closed old_source_edge))))
  have he : Context Γ (both (member 31 2) (member 34 4)) :=
    .mp ho (.mp hc (.closed (clean_endpoints 2 4 (by decide))))
  exact .mp (Context.conjunctionIntro (Context.conjunctionRight he) ho) hu

/-- The old guarded uniqueness for source 2 implies the stronger unguarded
new-graph uniqueness, under the supplied graph and old-source hypotheses. -/
def competitor_unique_all : KDerivation (imp oldUnique (imp oldClean.encode
    (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp (member 31 2) (allCode 4
        (imp (graphFormula 9 2 4).encode (equal 4 3)))))))) := by
  let U := oldUnique
  let C := oldClean.encode
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let M := member 31 2
  let Γ := [M,P,A,C,U]
  have vacC : KDerivation (imp C (allCode 4 C)) := oldClean.vacuity 4 (by decide)
  have vacA : KDerivation (imp A (allCode 4 A)) := by
    have h := (namedAdjoin 6 11 9 16).vacuity 4 (by decide)
    simpa [A,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h
  have vacP : KDerivation (imp P (allCode 4 P)) := (pairFormula 11 31 32).vacuity 4 (by decide)
  have vacM : KDerivation (imp M (allCode 4 M)) := membershipVacuity 31 2 4 (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .head _ _
  have h0 := Context.allMP hu (.closed (.generalize 4 competitor_unique))
  have h1 := Context.allMP (.mp hc (.closed vacC)) h0
  have h2 := Context.allMP (.mp ha (.closed vacA)) h1
  have h3 := Context.allMP (.mp hp (.closed vacP)) h2
  exact Context.allMP (.mp hm (.closed vacM)) h3

theorem competitor_unique_all_certificate : theoremCode (certificate competitor_unique_all) =
    imp oldUnique (imp oldClean.encode (imp (adjoinCode 6 11 9 16)
      (imp (pairFormula 11 31 32).encode (imp (member 31 2)
        (allCode 4 (imp (graphFormula 9 2 4).encode (equal 4 3))))))) :=
  certificate_correct competitor_unique_all
end PASoundness.PAtoCompactAdditionOldSourceUnique
#print axioms PASoundness.PAtoCompactAdditionOldSourceUnique.competitor_unique
#print axioms PASoundness.PAtoCompactAdditionOldSourceUnique.competitor_unique_all
#print axioms PASoundness.PAtoCompactAdditionOldSourceUnique.competitor_unique_all_certificate
