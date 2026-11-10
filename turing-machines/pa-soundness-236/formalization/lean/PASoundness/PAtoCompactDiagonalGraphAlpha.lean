import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactAdjunction

/-! Fixed binder alpha conversions used to compose diagonal-graph proof steps.
These are finite K derivations, not graph existence or induction results. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalGraphAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename the displayed successor test binder 2 to fresh name 4. -/
def successor_alpha : KDerivation (imp (successorCode 0 1 2) (successorCode 0 1 4)) := by
  let f := namedSuccessorBody 0 1 2
  have h := (CompactNamed.universalAlpha 2 4 f (by decide) (by decide) (by decide)).1
  have he : CompactNamed.replace 2 4 f = namedSuccessorBody 0 1 4 := by decide
  rw [he] at h
  simpa [f, successorCode, namedSuccessorBody, namedBoth, namedEither,
    CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

/-- Rename the displayed adjunction test binder 19 to fresh name 10. -/
def adjoin_alpha : KDerivation (imp (adjoinCode 6 8 7 19) (adjoinCode 6 8 7 10)) := by
  let f : CompactNamed.Formula := namedBoth
    (.imp (.member 7 19) (namedEither (.equal 19 8) (.member 6 19)))
    (.imp (namedEither (.equal 19 8) (.member 6 19)) (.member 7 19))
  let g : CompactNamed.Formula := namedBoth
    (.imp (.member 7 10) (namedEither (.equal 10 8) (.member 6 10)))
    (.imp (namedEither (.equal 10 8) (.member 6 10)) (.member 7 10))
  have h := (CompactNamed.universalAlpha 19 10 f (by decide) (by decide) (by decide)).1
  have he : CompactNamed.replace 19 10 f = g := by decide
  rw [he] at h
  simpa [f, g, adjoinCode, namedBoth, namedEither, CompactNamed.Formula.encode,
    CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

theorem graph_alpha_certificate :
    theoremCode (certificate successor_alpha) = imp (successorCode 0 1 2) (successorCode 0 1 4) ∧
    theoremCode (certificate adjoin_alpha) = imp (adjoinCode 6 8 7 19) (adjoinCode 6 8 7 10) :=
  ⟨certificate_correct successor_alpha, certificate_correct adjoin_alpha⟩

end PASoundness.PAtoCompactDiagonalGraphAlpha

#print axioms PASoundness.PAtoCompactDiagonalGraphAlpha.successor_alpha
#print axioms PASoundness.PAtoCompactDiagonalGraphAlpha.adjoin_alpha
#print axioms PASoundness.PAtoCompactDiagonalGraphAlpha.graph_alpha_certificate
