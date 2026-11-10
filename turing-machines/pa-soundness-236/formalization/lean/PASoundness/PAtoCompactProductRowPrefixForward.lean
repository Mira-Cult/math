import PASoundness.PAtoCompactMultiplicationRowPrefixTransport
import PASoundness.PAtoCompactTransitiveClosure

/-! K transport of the literal row witness across an explicit successor
prefix. This proves only witness inclusion, not existence of a row graph or
an extensionality principle for represented pairs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductRowPrefixForward
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactMultiplicationRowPrefixTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Every old prefix member remains in the explicitly supplied successor. -/
def successor_inclusion : KDerivation
    (imp (successorCode 0 1 2) (allCode 3 (imp (member 0 3) (member 1 3)))) := by
  let S := successorCode 0 1 2
  have hlocal : KDerivation (imp S (imp (member 0 3) (member 1 3))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 0 3,S]
    have hm : Context Γ (member 0 3) := .head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hd : Context Γ (either (equal 3 0) (member 0 3)) := Context.disjunctionRight hm
    exact .mp hd (.mp hs (.closed (successor_include 0 1 2 3 (by decide) (by decide) (by decide))))
  have hv : KDerivation (imp S (allCode 3 S)) := successor_vacuity 0 1 2 3 (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  have hs : Context [S] S := .head _ _
  have hp : Context [S] (imp (member 0 3) (member 1 3)) := .mp hs (.closed hlocal)
  exact Context.generalize 3 (by
    intro h hh
    have he : h = S := by simpa using hh
    subst h
    exact hv) hp

/-- A row witness over the old prefix remains a row witness over its
successor. This is valid with no graph extensionality assumption. -/
def row_forward : KDerivation (imp (successorCode 0 1 2)
    (imp (rowWitness 0).encode (rowWitness 1).encode)) := by
  have h := row_witness_prefix_inclusion
  change KDerivation (imp (allCode 3 (imp (member 0 3) (member 1 3)))
    (imp (rowWitness 0).encode (rowWitness 1).encode)) at h
  exact compose successor_inclusion h

theorem row_forward_certificate : theoremCode (certificate row_forward) =
    imp (successorCode 0 1 2) (imp (rowWitness 0).encode (rowWitness 1).encode) :=
  certificate_correct row_forward
end PASoundness.PAtoCompactProductRowPrefixForward
#print axioms PASoundness.PAtoCompactProductRowPrefixForward.successor_inclusion
#print axioms PASoundness.PAtoCompactProductRowPrefixForward.row_forward
#print axioms PASoundness.PAtoCompactProductRowPrefixForward.row_forward_certificate
