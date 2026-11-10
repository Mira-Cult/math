import PASoundness.PAtoCompactOrderIsoInstance
import PASoundness.PAtoCompactZeroSuccessor

/-! A guarded old-element correspondence under a supplied successor
isomorphism matrix. This constructs neither the graph nor its edges. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOldImageContainedAligned
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def m7 : Formula := replace 2 7 orderMatrix
private def m2 : Formula := replace 4 2 m7
private def q7 : Formula := .all 4 (.all 3 (.all 5 m7))
private def q2 : Formula := .all 3 (.all 5 m2)

/-- The exact order matrix instantiated at source names 7,2 and target names
3,5, by capture-safe K universal instantiation. -/
def aligned_order_instance : KDerivation (imp orderFormula.encode m2.encode) := by
  have h2 : KDerivation (imp orderFormula.encode q7.encode) := by
    have h := CompactNamed.universalInstance 2 7 (.all 4 (.all 3 (.all 5 orderMatrix)))
      (by decide) (by decide) (by decide)
    have hs : replace 2 7 (.all 4 (.all 3 (.all 5 orderMatrix))) = q7 := by decide
    rw [hs] at h
    change KDerivation (imp orderFormula.encode q7.encode) at h
    exact h
  have h4 : KDerivation (imp q7.encode q2.encode) := by
    have h := CompactNamed.universalInstance 4 2 (.all 3 (.all 5 m7))
      (by decide) (by decide) (by decide)
    have hs : replace 4 2 (.all 3 (.all 5 m7)) = q2 := by decide
    simpa only [q7, Formula.encode, hs] using h
  have h3 := CompactNamed.allSpecialize 3 (.all 5 m2) (by decide)
  have h5 := CompactNamed.allSpecialize 5 m2 (by decide)
  exact compose h2 (compose h4 (compose h3 h5))

/-- Supplied successor graphs, exact order formula, source guard 7∈0,
target guard 3∈1 and graph edges 7→3 and 2→5 imply both `7∈2→3∈5`
and `3∈5→7∈2`. The maximal endpoint guards 2∈0 and 5∈1 are derived
from the raw successor graphs. Syntactic names are fixed and distinct;
their assigned objects may coincide. Code 1 remains literal self-membership. -/
def old_image_preimage_iff : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp (member 0 7) (imp (member 1 3)
        (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
          (both (imp (member 2 7) (member 5 3))
            (imp (member 5 3) (member 2 7)))))))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let O := orderFormula.encode
  let A := member 0 7
  let B := member 0 2
  let C := member 1 3
  let D := member 1 5
  let E := (graphFormula 6 7 3).encode
  let F := (graphFormula 6 2 5).encode
  let L := member 2 7
  let R := member 5 3
  let Guard := both A (both B (both C (both D (both E F))))
  let Matrix := imp Guard (both (imp L R) (imp R L))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [F,E,C,A,O,SY,SX]
  have hsx : Context Γ SX := .hypothesis (by simp [Γ])
  have hsy : Context Γ SY := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .head _ _
  have hb : Context Γ B := .mp hsx (.closed (successor_contains_input 2 0 9 (by decide) (by decide)))
  have hd : Context Γ D := .mp hsy (.closed (successor_contains_input 5 1 10 (by decide) (by decide)))
  have hm : Context Γ Matrix := by
    have hi : Context Γ m2.encode := .mp ho (.closed aligned_order_instance)
    change Context Γ Matrix at hi
    exact hi
  have hg : Context Γ Guard := Context.conjunctionIntro ha (Context.conjunctionIntro hb
    (Context.conjunctionIntro hc (Context.conjunctionIntro hd (Context.conjunctionIntro he hf))))
  exact .mp hg hm

theorem old_image_preimage_iff_certificate :
    theoremCode (certificate old_image_preimage_iff) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp orderFormula.encode (imp (member 0 7) (imp (member 1 3)
          (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
            (both (imp (member 2 7) (member 5 3))
              (imp (member 5 3) (member 2 7))))))))) :=
  certificate_correct old_image_preimage_iff

end PASoundness.PAtoCompactOldImageContainedAligned

#print axioms PASoundness.PAtoCompactOldImageContainedAligned.old_image_preimage_iff
#print axioms PASoundness.PAtoCompactOldImageContainedAligned.old_image_preimage_iff_certificate
