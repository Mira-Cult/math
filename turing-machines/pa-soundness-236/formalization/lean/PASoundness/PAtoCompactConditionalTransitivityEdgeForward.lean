import PASoundness.PAtoCompactConditionalTransitivityPoint
import PASoundness.CompactFreshen

/-! Forward image existence for an explicitly supplied restricted composite
graph. The source bijections and composition graph are assumptions. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityEdgeForward
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactConditionalTransitivityPoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def secondBijection : Formula := replace 6 7 (replace 0 1 (replace 1 8 bijectionFormula))

private def firstBody : Formula := match bijectionFormula with
  | .imp (.imp (.all _ f) _) _ => f
  | _ => .bottom
private def firstWitness : Formula := match firstBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom
private def firstAt10 : Formula := replace 3 10 firstWitness
private def secondBody : Formula := match secondBijection with
  | .imp (.imp (.all _ f) _) _ => f
  | _ => .bottom
private def secondWitness : Formula := match secondBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom
private def secondAt10 : Formula := replace 2 10 secondWitness

def imageBody : Formula := namedBoth (.member 8 3) (graphFormula 9 2 3)
def image : Formula := .ex 3 imageBody
def premises : Formula := namedBoth bijectionFormula (namedBoth secondBijection
  (namedBoth composition (.member 0 2)))

private theorem premises_names_lt : ∀ v ∈ premises.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ premises.names.sup id at hm
  have hb : premises.names.sup id < 30 := by decide
  omega
private def freshPremises := freshen premises 30 premises_names_lt
private def premisesVacuity (v : Nat) (h : v ∉ freshPremises.formula.names) :
    KDerivation (imp premises.encode (allCode v premises.encode)) :=
  compose freshPremises.equivalent.forward
    (compose (freshPremises.formula.vacuity v h)
      (allCongr v freshPremises.equivalent.backward))

private theorem image_names_lt : ∀ v ∈ image.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ image.names.sup id at hm
  have hb : image.names.sup id < 30 := by decide
  omega
private def freshImage := freshen image 30 image_names_lt
private def imageVacuity (v : Nat) (h : v ∉ freshImage.formula.names) :
    KDerivation (imp image.encode (allCode v image.encode)) :=
  compose freshImage.equivalent.forward
    (compose (freshImage.formula.vacuity v h)
      (allCongr v freshImage.equivalent.backward))

/-- Every source member has an image in the target under the supplied
composite graph. The middle and target witnesses are existentially eliminated
in K; the output retains the same target witness in membership and edge. -/
def forward_image : KDerivation (imp premises.encode image.encode) := by
  have hs1 : KDerivation (imp (allCode 2 firstBody.encode) firstBody.encode) :=
    allSpecialize 2 firstBody (by decide)
  have ha1 := (existentialAlpha 3 10 firstWitness (by decide) (by decide) (by decide)).1
  have hs2 := universalInstance 2 10 secondBody (by decide) (by decide) (by decide)
  have he2 : replace 2 10 secondBody = .imp (.member 1 10) (.ex 3 secondAt10) := by decide
  rw [he2] at hs2
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [premises.encode]
  have h : Context Γ premises.encode := Context.head [] _
  have hf : Context Γ bijectionFormula.encode := Context.conjunctionLeft h
  have htail := Context.conjunctionRight h
  have hg : Context Γ secondBijection.encode := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hc : Context Γ composition.encode := Context.conjunctionLeft htail
  have ha : Context Γ (member 0 2) := Context.conjunctionRight htail
  have hfirst : Context Γ (allCode 2 firstBody.encode) := by
    change Context Γ (both (allCode 2 firstBody.encode) _) at hf
    exact Context.conjunctionLeft hf
  have hwitness : Context Γ (existsCode 3 firstWitness.encode) := by
    have hh : Context Γ firstBody.encode := .mp hfirst (.closed hs1)
    exact .mp ha hh
  have hwitness10 : Context Γ (existsCode 10 firstAt10.encode) := .mp hwitness (.closed ha1)
  have hinner : Context (secondAt10.encode :: firstAt10.encode :: Γ) image.encode := by
    let Δ := secondAt10.encode :: firstAt10.encode :: Γ
    have h1 : Context Δ firstAt10.encode := .under (Context.head Γ _) _
    have h2 : Context Δ secondAt10.encode := Context.head _ _
    have hmid : Context Δ (member 1 10) := Context.conjunctionLeft h1
    have hedgeF : Context Δ (graphFormula 6 2 10).encode :=
      Context.conjunctionLeft (Context.conjunctionRight h1)
    have htarget : Context Δ (member 8 3) := Context.conjunctionLeft h2
    have hedgeG : Context Δ (graphFormula 7 10 3).encode :=
      Context.conjunctionLeft (Context.conjunctionRight h2)
    have hc' : Context Δ composition.encode := .under (.under hc _) _
    have ha' : Context Δ (member 0 2) := .under (.under ha _) _
    have hedge : Context Δ edge.encode :=
      .mp hedgeG (.mp hedgeF (.mp hmid (.mp htarget (.mp ha' (.mp hc' (.closed chain_to_edge))))))
    have hb : Context Δ imageBody.encode := Context.conjunctionIntro htarget hedge
    exact .mp hb (.closed (existsIntroduce 3 imageBody (by decide)))
  have hsecond : Context (firstAt10.encode :: Γ) (existsCode 3 secondAt10.encode) := by
    let Δ := firstAt10.encode :: Γ
    have h1 : Context Δ firstAt10.encode := Context.head _ _
    have hm : Context Δ (member 1 10) := Context.conjunctionLeft h1
    have hg' : Context Δ secondBijection.encode := .under hg _
    have hs : Context Δ (allCode 2 secondBody.encode) := by
      change Context Δ (both (allCode 2 secondBody.encode) _) at hg'
      exact Context.conjunctionLeft hg'
    exact .mp hm (.mp hs (.closed hs2))
  have hv3 : ∀ f, f ∈ firstAt10.encode :: Γ → KDerivation (imp f (allCode 3 f)) := by
    intro f hf
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hf
    by_cases heq : f = firstAt10.encode
    · subst f
      exact firstAt10.vacuity 3 (by decide)
    · have heq' : f = premises.encode := hf.resolve_left heq
      subst f
      exact premisesVacuity 3 (by decide)
  have h10 : Context (firstAt10.encode :: Γ) image.encode :=
    Context.existsElim (imageVacuity 3 (by decide))
      (Context.generalize 3 hv3 (Context.deduction hinner)) hsecond
  have hv10 : ∀ f, f ∈ Γ → KDerivation (imp f (allCode 10 f)) := by
    intro f hf
    have heq : f = premises.encode := by simpa [Γ] using hf
    subst f
    exact premisesVacuity 10 (by decide)
  exact Context.existsElim (imageVacuity 10 (by decide))
    (Context.generalize 10 hv10 (Context.deduction h10)) hwitness10

theorem forward_image_certificate : theoremCode (certificate forward_image) =
    imp premises.encode image.encode := certificate_correct forward_image

end PASoundness.PAtoCompactConditionalTransitivityEdgeForward

#print axioms PASoundness.PAtoCompactConditionalTransitivityEdgeForward.forward_image
#print axioms PASoundness.PAtoCompactConditionalTransitivityEdgeForward.forward_image_certificate
