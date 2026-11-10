import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers

/-! Literal reverse-image existence projected from the two supplied
bijections. These K proofs do not construct a graph or assert transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityReverseExtract
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The second source bijection: domain 1, codomain 8, graph 7. -/
def secondBijection : Formula := replace 6 7 (replace 0 1 (replace 1 8 bijectionFormula))

private def fBody : Formula := match bijectionFormula with
  | .imp (.imp _ (.imp (.all _ f) _)) _ => f
  | _ => .bottom
private def fWitness : Formula := match fBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom
private def fAt10 : Formula := replace 3 10 fWitness
private def fSimple : Formula := ((Formula.member 0 2).imp (graphFormula 6 2 10).not).not

private def f_projection : KDerivation (imp fAt10.encode fSimple.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have h := Context.head [] fAt10.encode
  change Context [fAt10.encode] (both (member 0 2)
    (both (graphFormula 6 2 10).encode _)) at h
  exact Context.conjunctionIntro (Context.conjunctionLeft h)
    (Context.conjunctionLeft (Context.conjunctionRight h))

/-- A member of B has a preimage in A with a literal f-edge. -/
def f_preimage : KDerivation (imp bijectionFormula.encode
    (imp (member 1 10) (existsCode 2 (both (member 0 2) (graphFormula 6 2 10).encode)))) := by
  have hs := universalInstance 3 10 fBody (by decide) (by decide) (by decide)
  have hbody : replace 3 10 fBody = .imp (.member 1 10) (.ex 2 fAt10) := by decide
  rw [hbody] at hs
  have hm := existsCongr 2 f_projection
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 10, bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hbody : Context Γ (allCode 3 fBody.encode) := by
    change Context Γ (both _ (allCode 3 fBody.encode)) at hb
    exact Context.conjunctionRight hb
  have he : Context Γ (existsCode 2 fAt10.encode) :=
    .mp (Context.head _ _) (.mp hbody (.closed hs))
  exact .mp he (.closed hm)

private def gBody : Formula := match secondBijection with
  | .imp (.imp _ (.imp (.all _ f) _)) _ => f
  | _ => .bottom
private def gWitness : Formula := match gBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom
private def gSimple : Formula := ((Formula.member 1 2).imp (graphFormula 7 2 3).not).not
private def gSimple10 : Formula := ((Formula.member 1 10).imp (graphFormula 7 10 3).not).not

private def g_projection : KDerivation (imp gWitness.encode gSimple.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have h := Context.head [] gWitness.encode
  change Context [gWitness.encode] (both (member 1 2)
    (both (graphFormula 7 2 3).encode _)) at h
  exact Context.conjunctionIntro (Context.conjunctionLeft h)
    (Context.conjunctionLeft (Context.conjunctionRight h))

/-- A member of C has a preimage in B with a literal g-edge. The preimage
binder is alpha-renamed from 2 to 10; the same witness occurs in both parts. -/
def g_preimage : KDerivation (imp secondBijection.encode
    (imp (member 8 3) (existsCode 10 (both (member 1 10) (graphFormula 7 10 3).encode)))) := by
  have hs : KDerivation (imp (allCode 3 gBody.encode) gBody.encode) :=
    allSpecialize 3 gBody (by decide)
  have hm := existsCongr 2 g_projection
  have ha := (existentialAlpha 2 10 gSimple (by decide) (by decide) (by decide)).1
  have hrename : replace 2 10 gSimple = gSimple10 := by decide
  rw [hrename] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 8 3, secondBijection.encode]
  have hb : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (allCode 3 gBody.encode) := by
    change Context Γ (both _ (allCode 3 gBody.encode)) at hb
    exact Context.conjunctionRight hb
  have hi : Context Γ gBody.encode := .mp hg (.closed hs)
  have he : Context Γ (existsCode 2 gWitness.encode) := .mp (Context.head _ _) hi
  exact .mp (.mp he (.closed hm)) (.closed ha)

theorem f_preimage_certificate : theoremCode (certificate f_preimage) =
    imp bijectionFormula.encode
      (imp (member 1 10) (existsCode 2 (both (member 0 2) (graphFormula 6 2 10).encode))) :=
  certificate_correct f_preimage

theorem g_preimage_certificate : theoremCode (certificate g_preimage) =
    imp secondBijection.encode
      (imp (member 8 3) (existsCode 10 (both (member 1 10) (graphFormula 7 10 3).encode))) :=
  certificate_correct g_preimage

end PASoundness.PAtoCompactConditionalTransitivityReverseExtract

#print axioms PASoundness.PAtoCompactConditionalTransitivityReverseExtract.f_preimage
#print axioms PASoundness.PAtoCompactConditionalTransitivityReverseExtract.g_preimage
