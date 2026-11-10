import PASoundness.PAtoCompactGraphAdjoinPreserve

/-! Pointwise K preservation of an already-covered multiplication row index
when a single entry is adjoined to its represented graph. This retains the same
inner pair and output witnesses. It does not construct a complete row, prove
its no-garbage invariant, or establish multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowGraphPreserve
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactGraphAdjoinPreserve
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Index 3 is covered by graph g: the supplied map 6 maps 3 to 4,
5 represents the pair (30,3), and g has the edge (5,4). -/
def coverageBody (g : Nat) : Formula :=
  namedBoth (graphFormula 6 3 4)
    (namedBoth (pairFormula 5 30 3) (graphFormula g 5 4))

def coverage (g : Nat) : Formula := .ex 4 (.ex 5 (coverageBody g))

def extension : Formula := namedAdjoin 11 13 12 14
private theorem extension_code : extension.encode = adjoinCode 11 13 12 14 := by rfl

private def body_step : KDerivation (imp extension.encode
    (imp (coverageBody 11).encode (coverageBody 12).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(coverageBody 11).encode, extension.encode]
  have hb : Context Γ (coverageBody 11).encode := .head _ _
  have he : Context Γ extension.encode := .hypothesis (by simp [Γ])
  change Context Γ (both (graphFormula 6 3 4).encode
    (both (pairFormula 5 30 3).encode (graphFormula 11 5 4).encode)) at hb
  have he' : Context Γ (adjoinCode 11 13 12 14) := by simpa [extension_code] using he
  have hg : Context Γ (graphFormula 12 5 4).encode :=
    .mp (Context.conjunctionRight (Context.conjunctionRight hb))
      (.mp he' (.closed (adjoin_preserves_edge 11 13 12 14 5 4
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))))
  change Context Γ (both (graphFormula 6 3 4).encode
    (both (pairFormula 5 30 3).encode (graphFormula 12 5 4).encode))
  exact Context.conjunctionIntro (Context.conjunctionLeft hb)
    (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hb)) hg)

/-- Every covered row index remains covered after adjoining any point to its
old graph. The exact value and pair representatives are retained. -/
def coverage_preserved : KDerivation (imp extension.encode
    (imp (coverage 11).encode (coverage 12).encode)) := by
  have hv5 : KDerivation (imp extension.encode (allCode 5 extension.encode)) :=
    extension.vacuity 5 (by decide)
  have hv4 : KDerivation (imp extension.encode (allCode 4 extension.encode)) :=
    extension.vacuity 4 (by decide)
  exact conditionalExistsCongr 4 hv4 (conditionalExistsCongr 5 hv5 body_step)

theorem coverage_preserved_certificate : theoremCode (certificate coverage_preserved) =
    imp extension.encode (imp (coverage 11).encode (coverage 12).encode) :=
  certificate_correct coverage_preserved
end PASoundness.PAtoCompactMultiplicationRowGraphPreserve
#print axioms PASoundness.PAtoCompactMultiplicationRowGraphPreserve.coverage_preserved
#print axioms PASoundness.PAtoCompactMultiplicationRowGraphPreserve.coverage_preserved_certificate
