import PASoundness.PAtoCompactProductOutputInsideSelected
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactAdjunction

/-! The selected inside-source endpoint supplies the new-prefix path for its
selected factor pair and image output. The successor and selected witness are
explicit; no partial graph invariant is claimed here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputSelectedPath

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductOutputPreimagePoint PASoundness.PAtoCompactProductOutputInsideSelected

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def selectedReverse : Formula := replace 32 74 (replace 81 44 (replace 80 43 reverseBody))
def selectedPair : Formula := replace 32 74 PAtoCompactProductOutputImagePoint.pairedBody

theorem selected_shape : relocatedBody = namedBoth selectedReverse selectedPair := by decide
theorem selected_body_shape : replace 32 74 partialBody = namedBoth (.member 59 74) selectedPair := by decide

/-- The same inside endpoint 74 is in its successor prefix, and its retained
source/target witness introduces the corresponding existential path. -/
def selected_path : KDerivation (imp (successorCode 74 59 76)
    (imp relocatedBody.encode partialPath.encode)) := by
  have hi := exists_variable_intro 32 74 partialBody (by decide) (by decide) (by decide)
  rw [selected_body_shape] at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [relocatedBody.encode,successorCode 74 59 76]
  have hp : Context Γ relocatedBody.encode := .head _ _
  have hs : Context Γ (successorCode 74 59 76) := .hypothesis (by simp [Γ])
  have hp' : Context Γ (both selectedReverse.encode selectedPair.encode) := by
    simpa [selected_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode,
      both, neg] using hp
  have hd : Context Γ (either (equal 74 74) (member 74 74)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 74))
  have hm : Context Γ (member 59 74) :=
    .mp hd (.mp hs (.closed (successor_include 74 59 76 74 (by decide) (by decide) (by decide))))
  have hb : Context Γ (namedBoth (.member 59 74) selectedPair).encode := by
    simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hm (Context.conjunctionRight hp')
  simpa [partialPath, CompactNamed.Formula.encode] using Context.mp hb (.closed hi)

theorem selected_path_certificate : theoremCode (certificate selected_path) =
    imp (successorCode 74 59 76) (imp relocatedBody.encode partialPath.encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputSelectedPath

#print axioms PASoundness.PAtoCompactProductOutputSelectedPath.selected_path
#print axioms PASoundness.PAtoCompactProductOutputSelectedPath.selected_path_certificate
