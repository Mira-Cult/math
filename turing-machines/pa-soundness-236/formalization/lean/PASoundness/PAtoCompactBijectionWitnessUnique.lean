import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! Pointwise uniqueness under the exposed forward-bijection witness. This
constructs a K proof from literal syntax, not a graph or isomorphism. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactBijectionWitnessUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The forward-bijection witness body with chosen image 8, input 2, graph 6,
codomain 1 and quantified competing image 4. -/
def witnessAtEight : Formula := namedBoth (.member 1 8) (namedBoth (graphFormula 6 2 8)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 8))))

/-- Two displayed, codomain-guarded images of input 2 are equal, assuming the
actual forward-witness body at name 8. The fixed numeric labels are distinct
from the graph's internal binders; their denoted objects may coincide. -/
def images_equal_from_witness : KDerivation
    (imp witnessAtEight.encode
      (imp (member 1 3) (imp (graphFormula 6 2 3).encode
        (imp (member 1 5) (imp (graphFormula 6 2 5).encode (equal 3 5)))))) := by
  let F : Formula := .imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 8)
  let U : Formula := .all 4 F
  have h3 : KDerivation (imp U.encode
      (imp (both (member 1 3) (graphFormula 6 2 3).encode) (equal 3 8))) := by
    have h := CompactNamed.universalInstance 4 3 F (by decide) (by decide) (by decide)
    have hg : CompactNamed.replace 4 3 (graphFormula 6 2 4) = graphFormula 6 2 3 := by decide
    simpa [U, F, namedBoth, CompactNamed.Formula.encode, CompactNamed.replace,
      CompactNamed.rename, CompactProof.both, CompactProof.neg, hg] using h
  have h5 : KDerivation (imp U.encode
      (imp (both (member 1 5) (graphFormula 6 2 5).encode) (equal 5 8))) := by
    have h := CompactNamed.universalInstance 4 5 F (by decide) (by decide) (by decide)
    have hg : CompactNamed.replace 4 5 (graphFormula 6 2 4) = graphFormula 6 2 5 := by decide
    simpa [U, F, namedBoth, CompactNamed.Formula.encode, CompactNamed.replace,
      CompactNamed.rename, CompactProof.both, CompactProof.neg, hg] using h
  let W := witnessAtEight.encode
  let M3 := member 1 3
  let G3 := (graphFormula 6 2 3).encode
  let M5 := member 1 5
  let G5 := (graphFormula 6 2 5).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [G5,M5,G3,M3,W]
  have hw : Context Γ W := .hypothesis (by simp [Γ])
  have hm3 : Context Γ M3 := .hypothesis (by simp [Γ])
  have hg3 : Context Γ G3 := .hypothesis (by simp [Γ])
  have hm5 : Context Γ M5 := .hypothesis (by simp [Γ])
  have hg5 : Context Γ G5 := .head _ _
  have hu : Context Γ U.encode := Context.conjunctionRight (Context.conjunctionRight hw)
  have he3 : Context Γ (equal 3 8) :=
    .mp (Context.conjunctionIntro hm3 hg3) (.mp hu (.closed h3))
  have he5 : Context Γ (equal 5 8) :=
    .mp (Context.conjunctionIntro hm5 hg5) (.mp hu (.closed h5))
  exact Context.eqTrans he3 (Context.eqSymm he5)

theorem images_equal_from_witness_certificate :
    theoremCode (certificate images_equal_from_witness) =
      imp witnessAtEight.encode
        (imp (member 1 3) (imp (graphFormula 6 2 3).encode
          (imp (member 1 5) (imp (graphFormula 6 2 5).encode (equal 3 5))))) :=
  certificate_correct images_equal_from_witness

end PASoundness.PAtoCompactBijectionWitnessUnique

#print axioms PASoundness.PAtoCompactBijectionWitnessUnique.images_equal_from_witness
#print axioms PASoundness.PAtoCompactBijectionWitnessUnique.images_equal_from_witness_certificate
