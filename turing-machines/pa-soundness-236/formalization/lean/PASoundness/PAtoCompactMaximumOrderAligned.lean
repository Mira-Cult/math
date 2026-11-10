import PASoundness.PAtoCompactOrderIsoInstance

/-! A capture-safe K instance of the exact order-isomorphism clause.
All domain guards and graph edges remain explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMaximumOrderAligned
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def m8 : Formula := replace 5 8 orderMatrix
private def m7 : Formula := replace 2 7 m8
private def m2 : Formula := replace 4 2 m7
private def m5 : Formula := replace 3 5 m2
private def m3 : Formula := replace 8 3 m5
private def q8 : Formula := .all 2 (.all 4 (.all 3 (.all 8 m8)))
private def q7 : Formula := .all 4 (.all 3 (.all 8 m7))
private def q2 : Formula := .all 3 (.all 8 m2)
private def q5 : Formula := .all 8 m5

/-- Capture-safe instantiation of the order clause at the concrete source
and target names 7,2 and 5,3. The intermediate name 8 is a syntactic
eigenvariable; denoted objects may coincide. -/
def aligned_order_instance : KDerivation (imp orderFormula.encode m3.encode) := by
  have halpha := (CompactNamed.universalAlpha 5 8 orderMatrix (by decide) (by decide) (by decide)).1
  have hq8 : KDerivation (imp orderFormula.encode q8.encode) := by
    have h := allCongr 2 (allCongr 4 (allCongr 3 halpha))
    simpa only [orderFormula, orderMatrix, q8, m8, Formula.encode] using h
  have h2 : KDerivation (imp q8.encode q7.encode) := by
    have h := CompactNamed.universalInstance 2 7 (.all 4 (.all 3 (.all 8 m8)))
      (by decide) (by decide) (by decide)
    have hs : replace 2 7 (.all 4 (.all 3 (.all 8 m8))) = q7 := by decide
    simpa only [q8, Formula.encode, hs] using h
  have h4 : KDerivation (imp q7.encode q2.encode) := by
    have h := CompactNamed.universalInstance 4 2 (.all 3 (.all 8 m7))
      (by decide) (by decide) (by decide)
    have hs : replace 4 2 (.all 3 (.all 8 m7)) = q2 := by decide
    simpa only [q7, Formula.encode, hs] using h
  have h3 : KDerivation (imp q2.encode q5.encode) := by
    have h := CompactNamed.universalInstance 3 5 (.all 8 m2)
      (by decide) (by decide) (by decide)
    have hs : replace 3 5 (.all 8 m2) = q5 := by decide
    simpa only [q2, Formula.encode, hs] using h
  have h8 : KDerivation (imp q5.encode m3.encode) := by
    have h := CompactNamed.universalInstance 8 3 m5 (by decide) (by decide) (by decide)
    simpa only [q5, m3, Formula.encode] using h
  exact compose hq8 (compose h2 (compose h4 (compose h3 h8)))

/-- From the actual quantified order clause, the four domain guards and
both supplied graph edges, the proper preimage 7∈2 entails 5∈3. -/
def proper_preimage_order : KDerivation
    (imp orderFormula.encode
      (imp (member 0 7) (imp (member 0 2)
        (imp (member 1 5) (imp (member 1 3)
          (imp (graphFormula 6 7 5).encode (imp (graphFormula 6 2 3).encode
            (imp (member 2 7) (member 3 5))))))))) := by
  let A := member 0 7
  let B := member 0 2
  let C := member 1 5
  let D := member 1 3
  let E := (graphFormula 6 7 5).encode
  let F := (graphFormula 6 2 3).encode
  let L := member 2 7
  let R := member 3 5
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
  apply Context.deduction
  let Γ := [L,F,E,D,C,B,A,orderFormula.encode]
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .head _ _
  have hm : Context Γ Matrix := by
    have hi : Context Γ m3.encode := .mp ho (.closed aligned_order_instance)
    change Context Γ Matrix at hi
    exact hi
  have hg : Context Γ Guard := Context.conjunctionIntro ha (Context.conjunctionIntro hb
    (Context.conjunctionIntro hc (Context.conjunctionIntro hd (Context.conjunctionIntro he hf))))
  exact .mp hl (Context.conjunctionLeft (.mp hg hm))

theorem proper_preimage_order_certificate :
    theoremCode (certificate proper_preimage_order) =
      imp orderFormula.encode
        (imp (member 0 7) (imp (member 0 2)
          (imp (member 1 5) (imp (member 1 3)
            (imp (graphFormula 6 7 5).encode (imp (graphFormula 6 2 3).encode
              (imp (member 2 7) (member 3 5)))))))) :=
  certificate_correct proper_preimage_order

end PASoundness.PAtoCompactMaximumOrderAligned

#print axioms PASoundness.PAtoCompactMaximumOrderAligned.proper_preimage_order
#print axioms PASoundness.PAtoCompactMaximumOrderAligned.proper_preimage_order_certificate
