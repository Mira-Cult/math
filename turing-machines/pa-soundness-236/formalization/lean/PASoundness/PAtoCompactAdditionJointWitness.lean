import PASoundness.PAtoCompactAdditionSuccessorPairGraphExists
import PASoundness.PAtoCompactAdditionSuccessorSuffixExists
import PASoundness.PAtoCompactAdditionSuccessorSuffixRebased45

/-! Joint finite K witness packaging for the proposed addition-successor
construction. The successor of the whole result is named 45, distinct from
38, the successor of the source in the graph-extension argument. This module
first retains an explicitly supplied existential suffix, then constructs it
from the displayed nonmembership, filter and successor assumptions. This does
not assert that the new graph is an isomorphism. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionJointWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactAdditionSuccessorPairGraphExists
open PASoundness.PAtoCompactAdditionSuccessorSuffixRebased45
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The suffix at 40 is the old suffix with result 32 adjoined and also
filters the separately named result successor 45. -/
def suffixBody : Nat := both (adjoinCode 34 32 40 41)
  (filterGraph 45 40 35 (neg (member 33 35)))

/-- The original suffix witness is retained while K constructs a pair object
for (31,32) and adjoins it to graph 6, using the very same pair witness. -/
def joint_witness : KDerivation (imp (existsCode 40 suffixBody)
    (existsCode 40 (both suffixBody
      (existsCode 11 (both (pairFormula 11 31 32).encode
        (existsCode 9 (adjoinCode 6 11 9 16))))))) := by
  let E := existsCode 11 (both (pairFormula 11 31 32).encode
    (existsCode 9 (adjoinCode 6 11 9 16)))
  have hp : KDerivation (imp suffixBody (both suffixBody E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.conjunctionIntro (.head _ _) (.closed addition_pair_graph_exists)
  exact existsCongr 40 hp

theorem joint_witness_certificate : theoremCode (certificate joint_witness) =
    imp (existsCode 40 suffixBody)
      (existsCode 40 (both suffixBody
        (existsCode 11 (both (pairFormula 11 31 32).encode
          (existsCode 9 (adjoinCode 6 11 9 16)))))) :=
  certificate_correct joint_witness

/-- The new suffix, pair and extended graph are all constructed in K from
the stated nonmembership, old filter and result-successor assumptions. The
result successor is 45; name 38 remains available for the source successor. -/
def joint_witness_exists : KDerivation
    (imp (neg (member 33 32))
      (imp (filterGraph 32 34 35 (neg (member 33 35)))
        (imp (successorCode 32 45 39)
          (existsCode 40 (both suffixBody
            (existsCode 11 (both (pairFormula 11 31 32).encode
              (existsCode 9 (adjoinCode 6 11 9 16))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode 32 45 39, filterGraph 32 34 35 (neg (member 33 35)),
    neg (member 33 32)]
  have hs : Context Γ (successorCode 32 45 39) := .head _ _
  have hf : Context Γ (filterGraph 32 34 35 (neg (member 33 35))) :=
    .hypothesis (by simp [Γ])
  have hn : Context Γ (neg (member 33 32)) := .hypothesis (by simp [Γ])
  have he : Context Γ (existsCode 40 suffixBody) := by
    simpa [suffixBody] using (.mp hs (.mp hf (.mp hn
      (.closed successor_suffix_exists_45))) : Context Γ _)
  exact .mp he (.closed joint_witness)

theorem joint_witness_exists_certificate :
    theoremCode (certificate joint_witness_exists) =
      imp (neg (member 33 32))
        (imp (filterGraph 32 34 35 (neg (member 33 35)))
          (imp (successorCode 32 45 39)
            (existsCode 40 (both suffixBody
              (existsCode 11 (both (pairFormula 11 31 32).encode
                (existsCode 9 (adjoinCode 6 11 9 16)))))))) :=
  certificate_correct joint_witness_exists
end PASoundness.PAtoCompactAdditionJointWitness
#print axioms PASoundness.PAtoCompactAdditionJointWitness.joint_witness
#print axioms PASoundness.PAtoCompactAdditionJointWitness.joint_witness_certificate
#print axioms PASoundness.PAtoCompactAdditionJointWitness.joint_witness_exists
#print axioms PASoundness.PAtoCompactAdditionJointWitness.joint_witness_exists_certificate
