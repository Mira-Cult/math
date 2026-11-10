import PASoundness.PAtoCompactRestrictedMatrixClosed
import PASoundness.CompactQuantifiers

/-! Eliminate the supplied original equivalence graph after constructing a
restricted matrix. The output remains an explicit matrix, not canonical E. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedFromEquivalent
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactRestrictedMatrix
open PASoundness.PAtoCompactRestrictedMatrixClosed
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def forward : Formula := .all 7 (.imp (.member 2 7)
  (.ex 3 PASoundness.PAtoCompactRestrictedForwardUnique.restrictedWitness))
private def backward : Formula := .all 3 (.imp (.member 5 3)
  (.ex 7 PASoundness.PAtoCompactRestrictedBackwardWitness.restrictedWitness))
private def order : Formula := .all 30 (.all 31 (.all 32 (.all 33
  (.imp (namedBoth (.member 2 30) (namedBoth (.member 2 31)
    (namedBoth (.member 5 32) (namedBoth (.member 5 33)
      (namedBoth (graphFormula 8 30 32) (graphFormula 8 31 33))))))
    (namedBoth (.imp (.member 31 30) (.member 33 32))
      (.imp (.member 33 32) (.member 31 30)))))))

/-- Named version of the output existential, used only to establish the
required vacuity for the original graph name 6. -/
def target : Formula := .ex 8 (namedBoth (namedBoth forward backward) order)

theorem target_code : target.encode = existsCode 8 restrictedMatrix := by
  rfl

/-- K derives existence of the full displayed restricted matrix from the
original exact isomorphism formula and supplied raw successor/transitivity
hypotheses. Its original graph witness 6 is eliminated using explicit
vacuity of every retained formula. This still does not identify the target
with the canonical E formula at the new endpoints. -/
def restricted_from_equivalent : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12)
        (imp equivalentFormula.encode (existsCode 8 restrictedMatrix))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let T := transitiveCode 5 11 12
  let B := bijectionFormula.encode
  let O := orderFormula.encode
  let W := both B O
  let Goal : Formula := .imp (.all 9 (namedSuccessorBody 2 0 9))
    (.imp (.all 10 (namedSuccessorBody 5 1 10))
      (.imp (.all 11 (.all 12 (transitiveBody 5 11 12))) target))
  have hv : KDerivation (imp Goal.encode (allCode 6 Goal.encode)) :=
    Goal.vacuity 6 (by decide)
  have hstep : KDerivation (imp W Goal.encode) := by
    change KDerivation (imp W (imp SX (imp SY (imp T target.encode))))
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [T,SY,SX,W]
    have hw : Context Γ W := .hypothesis (by simp [Γ])
    have hsx : Context Γ SX := .hypothesis (by simp [Γ])
    have hsy : Context Γ SY := .hypothesis (by simp [Γ])
    have ht : Context Γ T := .head _ _
    have hb : Context Γ B := Context.conjunctionLeft hw
    have ho : Context Γ O := Context.conjunctionRight hw
    have hmatrix : Context Γ (existsCode 8 restrictedMatrix) :=
      .mp hb (.mp ho (.mp ht (.mp hsy (.mp hsx (.closed restricted_matrix_closed)))))
    simpa only [target_code] using hmatrix
  have helim : KDerivation (imp equivalentFormula.encode Goal.encode) := by
    change KDerivation (imp (existsCode 6 W) Goal.encode)
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 6 hstep))
      (Context.head [] (existsCode 6 W))
  change KDerivation (imp SX (imp SY (imp T
    (imp equivalentFormula.encode (existsCode 8 restrictedMatrix)))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equivalentFormula.encode,T,SY,SX]
  have he : Context Γ equivalentFormula.encode := .head _ _
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hy : Context Γ SY := .hypothesis (by simp [Γ])
  have hx : Context Γ SX := .hypothesis (by simp [Γ])
  have hg : Context Γ Goal.encode := .mp he (.closed helim)
  have hg' : Context Γ (imp SX (imp SY (imp T target.encode))) := hg
  simpa only [target_code] using (.mp ht (.mp hy (.mp hx hg')))

theorem restricted_from_equivalent_certificate :
    theoremCode (certificate restricted_from_equivalent) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp (transitiveCode 5 11 12)
          (imp equivalentFormula.encode (existsCode 8 restrictedMatrix)))) :=
  certificate_correct restricted_from_equivalent

end PASoundness.PAtoCompactRestrictedFromEquivalent

#print axioms PASoundness.PAtoCompactRestrictedFromEquivalent.restricted_from_equivalent
#print axioms PASoundness.PAtoCompactRestrictedFromEquivalent.restricted_from_equivalent_certificate
