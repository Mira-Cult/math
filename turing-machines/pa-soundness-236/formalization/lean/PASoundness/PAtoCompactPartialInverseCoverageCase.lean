import PASoundness.PAtoCompactPartialInverseOldEdge
import PASoundness.PAtoCompactPartialInverseAliasCoverage
import PASoundness.PAtoCompactSuccessorInjective

/-! Pointwise forward coverage after a supplied partial-inverse successor step.
All witnesses and prefix alias are explicit assumptions. No full quantified
invariant, reverse/no-spurious direction, or induction is proved here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseCoverageCase
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactPartialInverseImageWitness
open PASoundness.PAtoCompactPartialInverseOldEdge PASoundness.PAtoCompactPartialInverseAliasCoverage
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldCoverage : Nat := imp oldPrefixRhs (graphFormula 7 3 2).encode

def A : Nat := adjoinCode 7 11 9 14
def P : Nat := (pairFormula 11 13 12).encode
def S : Nat := successorCode 8 10 15
def E : Nat := (graphFormula 6 2 3).encode
def N : Nat := (graphFormula 9 3 2).encode

/-- For a queried target 3 and source 2 in successor prefix 10, the original
edge gives a reverse edge in graph 9. The proof splits the exact supplied
successor graph into its endpoint and old-prefix cases. The alias `12=8`, old
coverage, bijection image witness, inverse pair and graph adjunction all remain
explicit assumptions. -/
def coverage_case : KDerivation
    (imp A (imp P (imp imageWitness (imp (equal 12 8) (imp oldCoverage
      (imp S (imp (member 1 3) (imp (member 10 2) (imp E N))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,member 10 2,member 1 3,S,oldCoverage,equal 12 8,imageWitness,P,A]
  have hg : Context Γ E := Context.head _ _
  have hx : Context Γ (member 10 2) := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hc : Context Γ (either (equal 2 8) (member 8 2)) :=
    .mp hx (.mp hs (.closed (successor_inspect 8 10 15 2 (by decide) (by decide) (by decide))))
  apply Context.disjunctionElim hc
  · let Δ := [equal 2 8,E,member 10 2,member 1 3,S,oldCoverage,equal 12 8,imageWitness,P,A]
    have he : Context Δ (equal 2 8) := Context.head _ _
    have hg' : Context Δ E := .hypothesis (by simp [Δ])
    have hm : Context Δ (member 1 3) := .hypothesis (by simp [Δ])
    have ha : Context Δ (equal 12 8) := .hypothesis (by simp [Δ])
    have hw : Context Δ imageWitness := .hypothesis (by simp [Δ])
    have hp : Context Δ P := .hypothesis (by simp [Δ])
    have hj : Context Δ A := .hypothesis (by simp [Δ])
    exact .mp hg' (.mp (Context.eqSymm he) (.mp ha (.mp hm (.mp hw (.mp hp
      (.mp hj (.closed alias_endpoint_coverage)))))))
  · let Δ := [member 8 2,E,member 10 2,member 1 3,S,oldCoverage,equal 12 8,imageWitness,P,A]
    have hold : Context Δ (member 8 2) := Context.head _ _
    have hg' : Context Δ E := .hypothesis (by simp [Δ])
    have hc' : Context Δ oldCoverage := .hypothesis (by simp [Δ])
    have hj : Context Δ A := .hypothesis (by simp [Δ])
    exact .mp (Context.conjunctionIntro hold hg') (.mp hc' (.mp hj (.closed retain_old_prefix_coverage)))

theorem coverage_case_certificate : theoremCode (certificate coverage_case) =
    imp A (imp P (imp imageWitness (imp (equal 12 8) (imp oldCoverage
      (imp S (imp (member 1 3) (imp (member 10 2) (imp E N)))))))) :=
  certificate_correct coverage_case

end PASoundness.PAtoCompactPartialInverseCoverageCase

#print axioms PASoundness.PAtoCompactPartialInverseCoverageCase.coverage_case
#print axioms PASoundness.PAtoCompactPartialInverseCoverageCase.coverage_case_certificate
