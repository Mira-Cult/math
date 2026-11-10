import PASoundness.PAtoCompactProductOutputSelectedCoordinatesUnique
import PASoundness.PAtoCompactProductOutputSelectedImageUnique
import PASoundness.PAtoCompactMultiplicationSingleTripleExtension

/-! A queried path at the selected source endpoint determines the selected
factor coordinates and image output, so the supplied new graph's selected
triple transports to that query. No existential paths are eliminated here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputSameSourceTriple

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputOutsidePath
open PASoundness.PAtoCompactProductOutputInsideSelected PASoundness.PAtoCompactProductOutputSelectedPath
open PASoundness.PAtoCompactProductOutputSelectedCoordinatesUnique PASoundness.PAtoCompactProductOutputSelectedImageUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def selectedTriple : Formula := tripleAt 9 30 31 33
def queriedTriple : Formula := tripleAt 9 56 57 60
def sameSourceGuard : Formula := namedBoth relocatedBody
  (namedBoth endpointGuard selectedTriple)

theorem query_triple_shape : replace 33 60 (replace 31 57 (replace 30 56 selectedTriple)) = queriedTriple := by decide

def same_source_triple : KDerivation (imp sameSourceGuard.encode
    (imp (equal 32 74) (imp payloadAt.encode queriedTriple.encode))) := by
  have h1 := (equalityReplace 30 56 selectedTriple (by decide) (by decide)).1
  have h2 := (equalityReplace 31 57 (replace 30 56 selectedTriple) (by decide) (by decide)).1
  have h3 := (equalityReplace 33 60 (replace 31 57 (replace 30 56 selectedTriple)) (by decide) (by decide)).1
  rw [query_triple_shape] at h3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [payloadAt.encode,equal 32 74,sameSourceGuard.encode]
  have hp : Context Γ payloadAt.encode := .head _ _
  have he : Context Γ (equal 32 74) := .hypothesis (by simp [Γ])
  have hg : Context Γ sameSourceGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both relocatedBody.encode (both endpointGuard.encode selectedTriple.encode)) := by
    simpa [sameSourceGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hsel := Context.conjunctionLeft hg'
  have hend := Context.conjunctionLeft (Context.conjunctionRight hg')
  have htriple := Context.conjunctionRight (Context.conjunctionRight hg')
  have hcoords := Context.mp hp (Context.mp he (Context.mp hend
    (Context.mp hsel (.closed same_source_coordinates))))
  have hsel' : Context Γ (both selectedReverse.encode selectedPair.encode) := by
    simpa [selected_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hsel
  have himage := Context.mp hp (Context.mp he
    (Context.mp (Context.conjunctionRight hsel') (.closed same_source_image)))
  have hq1 := Context.mp htriple (Context.mp (Context.eqSymm (Context.conjunctionLeft hcoords)) (.closed h1))
  have hq2 := Context.mp hq1 (Context.mp (Context.eqSymm (Context.conjunctionRight hcoords)) (.closed h2))
  exact .mp hq2 (.mp (Context.eqSymm himage) (.closed h3))

theorem same_source_triple_certificate : theoremCode (certificate same_source_triple) =
    imp sameSourceGuard.encode (imp (equal 32 74) (imp payloadAt.encode queriedTriple.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputSameSourceTriple

#print axioms PASoundness.PAtoCompactProductOutputSameSourceTriple.same_source_triple
#print axioms PASoundness.PAtoCompactProductOutputSameSourceTriple.same_source_triple_certificate
