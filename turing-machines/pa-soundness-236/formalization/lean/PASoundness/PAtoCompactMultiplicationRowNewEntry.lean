import PASoundness.PAtoCompactMultiplicationRowPrefixTransport
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactAdjunction

/-! New-point no-garbage branch for a represented multiplication row. The
chosen index, value, inner pair and outer pair are explicit supplied witnesses.
Their exact representatives are retained, with no extensionality or uniqueness
assumption. This does not construct the graph or prove totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowNewEntry
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactMultiplicationRowPrefixTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Replace the selected edge name by the equal entry name. -/
def edge_pair_transport : KDerivation (imp (equal 9 13)
    (imp (pairFormula 13 12 4).encode (pairFormula 9 12 4).encode)) := by
  have h := (equalityReplace 13 9 (pairFormula 13 12 4) (by decide) (by decide)).1
  have he : replace 13 9 (pairFormula 13 12 4) = pairFormula 9 12 4 := by decide
  rw [he] at h
  exact compose (equalitySymmetry 9 13) h

/-- The displayed chosen row index 0, map value 4, inner pair 12 and
outer pair 13 witness that an equal graph entry 9 is a new row entry. -/
def new_entry_is_row_witness : KDerivation (imp (member 1 0)
    (imp (member 31 0) (imp (graphFormula 6 0 4).encode
      (imp (pairFormula 12 30 0).encode (imp (pairFormula 13 12 4).encode
        (imp (equal 9 13) (rowWitness 1).encode)))))) := by
  let b := rowBody 1
  let b0 := replace 3 0 b
  have hp := exists_variable_intro 5 12 b0 (by decide) (by decide) (by decide)
  have hc := existsIntroduce 4 (.ex 5 b0) (by decide)
  have hi := exists_variable_intro 3 0 (.ex 4 (.ex 5 b)) (by decide) (by decide) (by decide)
  have hpShape : replace 5 12 b0 =
      namedBoth (.member 1 0) (namedBoth (.member 31 0)
        (namedBoth (graphFormula 6 0 4)
          (namedBoth (pairFormula 12 30 0) (pairFormula 9 12 4)))) := by decide
  have hiShape : replace 3 0 (.ex 4 (.ex 5 b)) = .ex 4 (.ex 5 b0) := by decide
  rw [hpShape] at hp
  rw [hiShape] at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 9 13, (pairFormula 13 12 4).encode,
    (pairFormula 12 30 0).encode, (graphFormula 6 0 4).encode, member 31 0, member 1 0]
  have he : Context Γ (equal 9 13) := .hypothesis (by simp [Γ])
  have hp13 : Context Γ (pairFormula 13 12 4).encode := .hypothesis (by simp [Γ])
  have hp12 : Context Γ (pairFormula 12 30 0).encode := .hypothesis (by simp [Γ])
  have hf : Context Γ (graphFormula 6 0 4).encode := .hypothesis (by simp [Γ])
  have hy : Context Γ (member 31 0) := .hypothesis (by simp [Γ])
  have hk : Context Γ (member 1 0) := .hypothesis (by simp [Γ])
  have hp9 : Context Γ (pairFormula 9 12 4).encode := .mp hp13 (.mp he (.closed edge_pair_transport))
  have hbody : Context Γ (both (member 1 0) (both (member 31 0)
      (both (graphFormula 6 0 4).encode
        (both (pairFormula 12 30 0).encode (pairFormula 9 12 4).encode)))) :=
    Context.conjunctionIntro hk (Context.conjunctionIntro hy
      (Context.conjunctionIntro hf (Context.conjunctionIntro hp12 hp9)))
  have hp' : Context Γ (existsCode 5 b0.encode) := by
    apply Context.mp _ (.closed hp)
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hbody
  have hc' := Context.mp hp' (.closed hc)
  have hi' := Context.mp hc' (.closed hi)
  change Context Γ (rowWitness 1).encode
  exact hi'

theorem new_entry_is_row_witness_certificate :
    theoremCode (certificate new_entry_is_row_witness) =
      imp (member 1 0) (imp (member 31 0) (imp (graphFormula 6 0 4).encode
        (imp (pairFormula 12 30 0).encode (imp (pairFormula 13 12 4).encode
          (imp (equal 9 13) (rowWitness 1).encode))))) :=
  certificate_correct new_entry_is_row_witness
end PASoundness.PAtoCompactMultiplicationRowNewEntry
#print axioms PASoundness.PAtoCompactMultiplicationRowNewEntry.edge_pair_transport
#print axioms PASoundness.PAtoCompactMultiplicationRowNewEntry.new_entry_is_row_witness
#print axioms PASoundness.PAtoCompactMultiplicationRowNewEntry.new_entry_is_row_witness_certificate
