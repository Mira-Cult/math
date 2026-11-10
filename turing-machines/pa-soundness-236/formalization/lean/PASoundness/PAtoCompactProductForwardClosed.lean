import PASoundness.PAtoCompactProductForwardConditional
import PASoundness.PAtoCompactProductCleanForwardUnique
import PASoundness.PAtoCompactProductFilterReverseTriple

/-! The actual forward multiplication-matrix clause is preserved by the
specified K graph filter. This is finite proof data, not full matrix or
multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductForwardClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactProductCleanFilter PASoundness.PAtoCompactProductForwardConditional
open PASoundness.PAtoCompactMultiplicationCandidate
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Filtering graph 6 to valid nested product triples yields the exact
forward product clause at filtered graph 54, preserving the same domains. -/
noncomputable def forward_preserved : KDerivation (imp (filterCode 54)
    (imp forwardFormula.encode (forwardAt 54).encode)) := by
  have hreverse := PAtoCompactProductFilterReverseTriple.reverse_triple 3 4 9
  have hreverse' : KDerivation (imp (filterCode 54)
      (imp (PAtoCompactProductCleanForwardUnique.triple9 54).encode
        (PAtoCompactProductCleanForwardUnique.triple9 6).encode)) := by
    exact hreverse
  have h := PAtoCompactProductCleanForwardUnique.unique_transfer hreverse'
  have h' : KDerivation (imp (filterCode 54) (imp (unique 6).encode (unique 54).encode)) := by
    have he6 : unique 6 = PAtoCompactProductCleanForwardUnique.unique5 6 := by decide
    have he54 : unique 54 = PAtoCompactProductCleanForwardUnique.unique5 54 := by decide
    rw [he6,he54]
    exact h
  exact forward_from_uniqueness h'

theorem forward_preserved_certificate : theoremCode (certificate forward_preserved) =
    imp (filterCode 54) (imp forwardFormula.encode (forwardAt 54).encode) :=
  certificate_correct forward_preserved
end PASoundness.PAtoCompactProductForwardClosed
#print axioms PASoundness.PAtoCompactProductForwardClosed.forward_preserved
#print axioms PASoundness.PAtoCompactProductForwardClosed.forward_preserved_certificate
