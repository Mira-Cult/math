import PASoundness.PAtoCompactAdditionTopWitnessUnequal

/-! Capture-safe K equality transport for the top-source witness in the
unequal-top addition graph. This is a pointwise case only, not graph
bijectivity, addition totality, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionTopSourceTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdditionSuccessorGraphClean PASoundness.PAtoCompactAdditionTopWitnessUnequal
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The top witness body after replacing source 31 by an equal source 2. -/
def pointBody : Formula := namedBoth (.member 40 3)
  (namedBoth (graphFormula 9 2 3)
    (.all 4 (.imp (graphFormula 9 2 4) (.equal 4 3))))

/-- Explicit equality replacement transports the existential witness,
including uniqueness, to source 2. -/
def top_source_transport : KDerivation
    (imp (equal 2 31) (imp (existsCode 3 topSourceWitness.encode)
      (existsCode 3 pointBody.encode))) := by
  let f : Formula := .ex 3 topSourceWitness
  have h := (equalityReplace 31 2 f (by decide) (by decide)).1
  have hs : replace 31 2 f = .ex 3 pointBody := by decide
  rw [hs] at h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode 3 topSourceWitness.encode,equal 2 31]
  have he : Context Γ (equal 2 31) := .hypothesis (by simp [Γ])
  have hf : Context Γ (existsCode 3 topSourceWitness.encode) := .head _ _
  exact .mp hf (.mp (Context.eqSymm he) (.closed h))

/-- The top-source case under the literal equality and all original graph
hypotheses. The same witness works; no transitivity premise is needed. -/
def top_source_equal_case : KDerivation
    (imp (adjoinCode 34 32 40 41) (imp (adjoinCode 6 11 9 16)
      (imp (pairFormula 11 31 32).encode (imp oldClean.encode
        (imp (equal 2 31) (existsCode 3 pointBody.encode)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 2 31,oldClean.encode,(pairFormula 11 31 32).encode,
    adjoinCode 6 11 9 16,adjoinCode 34 32 40 41]
  have he : Context Γ (equal 2 31) := .head _ _
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ (pairFormula 11 31 32).encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (adjoinCode 6 11 9 16) := .hypothesis (by simp [Γ])
  have hs : Context Γ (adjoinCode 34 32 40 41) := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 3 topSourceWitness.encode) :=
    .mp hc (.mp hp (.mp ha (.mp hs (.closed top_source_witness))))
  exact .mp hw (.mp he (.closed top_source_transport))

theorem top_source_equal_case_certificate : theoremCode (certificate top_source_equal_case) =
    imp (adjoinCode 34 32 40 41) (imp (adjoinCode 6 11 9 16)
      (imp (pairFormula 11 31 32).encode (imp oldClean.encode
        (imp (equal 2 31) (existsCode 3 pointBody.encode))))) :=
  certificate_correct top_source_equal_case
end PASoundness.PAtoCompactAdditionTopSourceTransport
#print axioms PASoundness.PAtoCompactAdditionTopSourceTransport.top_source_transport
#print axioms PASoundness.PAtoCompactAdditionTopSourceTransport.top_source_equal_case
#print axioms PASoundness.PAtoCompactAdditionTopSourceTransport.top_source_equal_case_certificate
