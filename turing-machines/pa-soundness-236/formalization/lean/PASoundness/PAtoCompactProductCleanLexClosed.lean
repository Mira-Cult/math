import PASoundness.PAtoCompactProductCleanLexTransfer
import PASoundness.PAtoCompactProductFilterReverseTriple

/-! The exact product lexicographic clause is preserved by the supplied
product graph filter. Both reverse-triple premises of the transfer are actual
finite K derivations. Graph existence, preservation of the other product
clauses, and multiplication totality remain separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanLexClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactProductCleanFilter PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductCleanLexTransfer

/-- A filtered product graph inherits the original graph's lexicographic
clause; all graph names and the filter are literal object-language formulas. -/
def lex_preserved : KDerivation (imp (filterCode 54) (imp lexFormula.encode filteredLex.encode)) := by
  have h35 := PASoundness.PAtoCompactProductFilterReverseTriple.reverse_triple 3 4 5
  have h79 := PASoundness.PAtoCompactProductFilterReverseTriple.reverse_triple 7 8 9
  have h35' : KDerivation (imp (filterCode 54) (imp (tripleAt 54 3 4 5).encode
      (tripleAt 6 3 4 5).encode)) := by
    have ha : tripleAt 54 3 4 5 = PASoundness.PAtoCompactProductFilterReverseTriple.tripleAt 54 3 4 5 := by decide
    have hb : tripleAt 6 3 4 5 = PASoundness.PAtoCompactProductFilterReverseTriple.tripleAt 6 3 4 5 := by decide
    rw [ha, hb]
    exact h35
  have h79' : KDerivation (imp (filterCode 54) (imp (tripleAt 54 7 8 9).encode
      (tripleAt 6 7 8 9).encode)) := by
    have ha : tripleAt 54 7 8 9 = PASoundness.PAtoCompactProductFilterReverseTriple.tripleAt 54 7 8 9 := by decide
    have hb : tripleAt 6 7 8 9 = PASoundness.PAtoCompactProductFilterReverseTriple.tripleAt 6 7 8 9 := by decide
    rw [ha, hb]
    exact h79
  exact transfer_of_reverse h35' h79'

theorem lex_preserved_certificate : theoremCode (certificate lex_preserved) =
    imp (filterCode 54) (imp lexFormula.encode filteredLex.encode) :=
  certificate_correct lex_preserved
end PASoundness.PAtoCompactProductCleanLexClosed
#print axioms PASoundness.PAtoCompactProductCleanLexClosed.lex_preserved
#print axioms PASoundness.PAtoCompactProductCleanLexClosed.lex_preserved_certificate
