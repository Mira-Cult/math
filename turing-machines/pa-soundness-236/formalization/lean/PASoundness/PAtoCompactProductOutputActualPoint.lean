import PASoundness.PAtoCompactProductOutputCollectionSource
import PASoundness.PAtoCompactProductOutputImageUnique

/-! Project a selected point of the actual source-domain path graph. The
supplied graph invariant and factor memberships are explicit; no forward
coverage or product matrix is inferred without point existence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputActualPoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputPartialBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def actualInvariant : Formula := replace 59 0 partialInvariant
def actualBody : Formula := namedBoth (.member 0 32) pairedBody
def actualPath : Formula := .ex 32 actualBody
def selectedGuard : Formula := namedBoth (.member 43 30)
  (namedBoth (.member 44 31) (.member 42 33))
def selectedTriple : Formula := tripleAt 58 30 31 33
def selectedPoint : Formula := .imp selectedGuard
  (namedBoth (.imp selectedTriple actualPath) (.imp actualPath selectedTriple))

theorem actual_invariant_shape : actualInvariant = .all 56 (.all 57 (.all 60
    (replace 59 0 (.imp endpointGuard (namedBoth (.imp targetTriple pathAt) (.imp pathAt targetTriple)))))) := by decide

def actual_instance : KDerivation (imp actualInvariant.encode selectedPoint.encode) := by
  let F := replace 59 0 (.imp endpointGuard (namedBoth (.imp targetTriple pathAt) (.imp pathAt targetTriple)))
  have h56 := universalInstance 56 30 (.all 57 (.all 60 F)) (by decide) (by decide) (by decide)
  have hs56 : replace 56 30 (.all 57 (.all 60 F)) = .all 57 (.all 60 (replace 56 30 F)) := by decide
  rw [hs56] at h56
  have h57 := universalInstance 57 31 (.all 60 (replace 56 30 F)) (by decide) (by decide) (by decide)
  have hs57 : replace 57 31 (.all 60 (replace 56 30 F)) = .all 60 (replace 57 31 (replace 56 30 F)) := by decide
  rw [hs57] at h57
  have h60 := universalInstance 60 33 (replace 57 31 (replace 56 30 F)) (by decide) (by decide) (by decide)
  have hs60 : replace 60 33 (replace 57 31 (replace 56 30 F)) = selectedPoint := by decide
  rw [hs60] at h60
  simpa [actual_invariant_shape, F, CompactNamed.Formula.encode] using compose h56 (compose h57 h60)

/-- A retained image body supplies both the target membership and the path
for the same source output and image value. -/
def selected_body_path : KDerivation (imp pairedBody.encode
    (both (member 42 33) actualPath.encode)) := by
  have hi := existsIntroduce 32 actualBody (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [pairedBody.encode]
  have hp : Context Γ pairedBody.encode := .head _ _
  have hp' : Context Γ (both sourceBody.encode imageBody.encode) := by
    simpa [pairedBody, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hp
  have hs : Context Γ (member 0 32) := by
    have hs' : Context Γ (both (member 0 32) (both
        (PAtoCompactMultiplicationCandidate.tripleFormula 30 31 32).encode
        (Formula.all 9 PAtoCompactProductOutputImageUnique.sourceUnique).encode)) := by
      simpa [PAtoCompactProductOutputImageUnique.source_shape, namedBoth, CompactNamed.Formula.not,
        CompactNamed.Formula.encode, both, neg] using Context.conjunctionLeft hp'
    exact Context.conjunctionLeft hs'
  have himage : Context Γ (member 42 33) := by
    have himage' : Context Γ (both (member 42 33) (both (graphFormula 40 32 33).encode
        (Formula.all 4 PAtoCompactProductOutputImageUnique.imageUnique).encode)) := by
      simpa [PAtoCompactProductOutputImageUnique.image_shape, namedBoth, CompactNamed.Formula.not,
        CompactNamed.Formula.encode, both, neg] using Context.conjunctionRight hp'
    exact Context.conjunctionLeft himage'
  have hb : Context Γ actualBody.encode := by
    simpa [actualBody, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hs hp
  have hpath : Context Γ actualPath.encode := by
    simpa [actualPath, CompactNamed.Formula.encode] using Context.mp hb (.closed hi)
  exact Context.conjunctionIntro himage hpath

/-- A selected body at a guarded factor pair is a triple in the supplied
actual graph, with its same target-output membership retained. -/
def selected_body_in_graph : KDerivation (imp actualInvariant.encode
    (imp (member 43 30) (imp (member 44 31) (imp pairedBody.encode
      (both (member 42 33) selectedTriple.encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [pairedBody.encode,member 44 31,member 43 30,actualInvariant.encode]
  have hp : Context Γ pairedBody.encode := .head _ _
  have hy : Context Γ (member 44 31) := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 43 30) := .hypothesis (by simp [Γ])
  have hi : Context Γ actualInvariant.encode := .hypothesis (by simp [Γ])
  have hbody := Context.mp hp (.closed selected_body_path)
  have hg : Context Γ selectedGuard.encode := by
    simpa [selectedGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hx (Context.conjunctionIntro hy (Context.conjunctionLeft hbody))
  have hpoint := Context.mp hg (Context.mp hi (.closed actual_instance))
  have hpoint' : Context Γ (both (imp selectedTriple.encode actualPath.encode)
      (imp actualPath.encode selectedTriple.encode)) := by
    simpa [selectedPoint, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hpoint
  have ht := Context.mp (Context.conjunctionRight hbody) (Context.conjunctionRight hpoint')
  exact Context.conjunctionIntro (Context.conjunctionLeft hbody) ht

theorem selected_body_in_graph_certificate : theoremCode (certificate selected_body_in_graph) =
    imp actualInvariant.encode (imp (member 43 30) (imp (member 44 31)
      (imp pairedBody.encode (both (member 42 33) selectedTriple.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputActualPoint

#print axioms PASoundness.PAtoCompactProductOutputActualPoint.actual_instance
#print axioms PASoundness.PAtoCompactProductOutputActualPoint.selected_body_path
#print axioms PASoundness.PAtoCompactProductOutputActualPoint.selected_body_in_graph
#print axioms PASoundness.PAtoCompactProductOutputActualPoint.selected_body_in_graph_certificate
