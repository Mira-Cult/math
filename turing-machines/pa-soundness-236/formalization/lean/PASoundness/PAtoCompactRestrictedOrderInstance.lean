import PASoundness.PAtoCompactOrderIsoInstance

/-! A capture-safe K order-matrix instance at four fresh coordinate names.
Graph existence, endpoint restriction and quotient laws are not asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedOrderInstance
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def m30 : Formula := replace 2 30 orderMatrix
private def m31 : Formula := replace 4 31 m30
private def m32 : Formula := replace 3 32 m31
private def m33 : Formula := replace 5 33 m32
private def q30 : Formula := .all 4 (.all 3 (.all 5 m30))
private def q31 : Formula := .all 3 (.all 5 m31)
private def q32 : Formula := .all 5 m32

/-- Instantiate the exact order clause at source coordinates 30,31 and
target coordinates 32,33. The four destination names are fresh for the
remaining binders; denoted objects need not be distinct. -/
def order_instance_fresh : KDerivation (imp orderFormula.encode m33.encode) := by
  have h2 : KDerivation (imp orderFormula.encode q30.encode) := by
    have h := CompactNamed.universalInstance 2 30 (.all 4 (.all 3 (.all 5 orderMatrix)))
      (by decide) (by decide) (by decide)
    have hs : replace 2 30 (.all 4 (.all 3 (.all 5 orderMatrix))) = q30 := by decide
    rw [hs] at h
    simpa only [orderFormula, orderMatrix, Formula.encode] using h
  have h4 : KDerivation (imp q30.encode q31.encode) := by
    have h := CompactNamed.universalInstance 4 31 (.all 3 (.all 5 m30))
      (by decide) (by decide) (by decide)
    have hs : replace 4 31 (.all 3 (.all 5 m30)) = q31 := by decide
    simpa only [q30, Formula.encode, hs] using h
  have h3 : KDerivation (imp q31.encode q32.encode) := by
    have h := CompactNamed.universalInstance 3 32 (.all 5 m31)
      (by decide) (by decide) (by decide)
    have hs : replace 3 32 (.all 5 m31) = q32 := by decide
    simpa only [q31, Formula.encode, hs] using h
  have h5 : KDerivation (imp q32.encode m33.encode) := by
    have h := CompactNamed.universalInstance 5 33 m32 (by decide) (by decide) (by decide)
    simpa only [q32, m33, Formula.encode] using h
  exact compose h2 (compose h4 (compose h3 h5))

/-- With all four endpoint guards and both supplied graph edges, K derives
both directions of membership-order preservation. -/
def guarded_order_fresh : KDerivation
    (imp orderFormula.encode
      (imp (member 0 30) (imp (member 0 31)
        (imp (member 1 32) (imp (member 1 33)
          (imp (graphFormula 6 30 32).encode (imp (graphFormula 6 31 33).encode
            (both (imp (member 31 30) (member 33 32))
              (imp (member 33 32) (member 31 30)))))))))) := by
  let A := member 0 30
  let B := member 0 31
  let C := member 1 32
  let D := member 1 33
  let E := (graphFormula 6 30 32).encode
  let F := (graphFormula 6 31 33).encode
  let L := member 31 30
  let R := member 33 32
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
  let Γ := [F,E,D,C,B,A,orderFormula.encode]
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .head _ _
  have hm : Context Γ Matrix := by
    have hi : Context Γ m33.encode := .mp ho (.closed order_instance_fresh)
    change Context Γ Matrix at hi
    exact hi
  have hg : Context Γ Guard := Context.conjunctionIntro ha (Context.conjunctionIntro hb
    (Context.conjunctionIntro hc (Context.conjunctionIntro hd (Context.conjunctionIntro he hf))))
  exact .mp hg hm

theorem guarded_order_fresh_certificate :
    theoremCode (certificate guarded_order_fresh) =
      imp orderFormula.encode
        (imp (member 0 30) (imp (member 0 31)
          (imp (member 1 32) (imp (member 1 33)
            (imp (graphFormula 6 30 32).encode (imp (graphFormula 6 31 33).encode
              (both (imp (member 31 30) (member 33 32))
                (imp (member 33 32) (member 31 30))))))))) :=
  certificate_correct guarded_order_fresh

end PASoundness.PAtoCompactRestrictedOrderInstance

#print axioms PASoundness.PAtoCompactRestrictedOrderInstance.order_instance_fresh
#print axioms PASoundness.PAtoCompactRestrictedOrderInstance.guarded_order_fresh
#print axioms PASoundness.PAtoCompactRestrictedOrderInstance.guarded_order_fresh_certificate
