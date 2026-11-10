import PASoundness.PAtoCompactTransitiveClosure

/-! Projections from the exact prefix-successor graph used in the fixed-first
row construction. This is a finite K derivation, not row collection or
multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstSuccessorProjection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Every old prefix member remains in the successor prefix. -/
def successor_inclusion : KDerivation (imp (successorCode 0 1 2)
    (allCode 3 (imp (member 0 3) (member 1 3)))) := by
  let S := successorCode 0 1 2
  let F : Formula := .imp (.member 0 3) (.member 1 3)
  have hpoint : KDerivation (imp S F.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 0 3,S]
    have hm : Context Γ (member 0 3) := .head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have he : Context Γ (either (equal 3 0) (member 0 3)) :=
      Context.disjunctionRight (a := equal 3 0) hm
    exact .mp he (.mp hs (.closed (successor_include 0 1 2 3 (by decide) (by decide) (by decide))))
  have hv : KDerivation (imp S (allCode 3 S)) :=
    successor_vacuity 0 1 2 3 (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  have hs : Context [S] S := .head [] _
  have hp : Context [S] F.encode := .mp hs (.closed hpoint)
  exact Context.generalize 3 (by
    intro z hz
    have he : z = S := by simpa using hz
    subst z
    exact hv) hp

/-- The old prefix itself belongs to its successor. -/
def successor_endpoint : KDerivation (imp (successorCode 0 1 2) (member 1 0)) :=
  successor_contains_input 0 1 2 (by decide) (by decide)

/-- Both consequences hold for the same supplied successor graph. -/
def successor_prefix_projections : KDerivation (imp (successorCode 0 1 2)
    (both (allCode 3 (imp (member 0 3) (member 1 3))) (member 1 0))) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hs : Context [successorCode 0 1 2] (successorCode 0 1 2) := .head [] _
  exact Context.conjunctionIntro (.mp hs (.closed successor_inclusion))
    (.mp hs (.closed successor_endpoint))

theorem successor_prefix_projections_certificate :
    theoremCode (certificate successor_prefix_projections) = imp (successorCode 0 1 2)
      (both (allCode 3 (imp (member 0 3) (member 1 3))) (member 1 0)) :=
  certificate_correct successor_prefix_projections
end PASoundness.PAtoCompactFixedFirstSuccessorProjection
#print axioms PASoundness.PAtoCompactFixedFirstSuccessorProjection.successor_inclusion
#print axioms PASoundness.PAtoCompactFixedFirstSuccessorProjection.successor_endpoint
#print axioms PASoundness.PAtoCompactFixedFirstSuccessorProjection.successor_prefix_projections
#print axioms PASoundness.PAtoCompactFixedFirstSuccessorProjection.successor_prefix_projections_certificate
