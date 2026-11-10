import PASoundness.PAtoCompactConditionalTransitivityTargetAll
import PASoundness.PAtoCompactConditionalTransitivityEdgeForward
import PASoundness.CompactFreshen

/-! The exact forward bijection clause from an explicitly supplied restricted
composition graph and the two original bijections. No graph existence or full
quotient transitivity is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityForwardClause
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityTargetAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def uniqueBody : Formula := .imp (namedBoth (.member 8 4) (graphFormula 9 2 4)) (.equal 4 3)
def witnessBody : Formula := namedBoth (.member 8 3)
  (namedBoth (graphFormula 9 2 3) (.all 4 uniqueBody))
def selected : Formula := .ex 3 witnessBody
def forwardClause : Formula := .all 2 (.imp (.member 0 2) selected)

/-- The constructed formula is literally the first conjunct of the target
bijection, whose domain is 0, codomain is 8, and graph is 9. -/
theorem forward_clause_exact : (match
    (replace 6 9 (replace 1 8 bijectionFormula)) with
  | .imp (.imp first _) _ => first
  | _ => .truth) = forwardClause := by decide

private theorem background_names_lt : ∀ v ∈ background.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ background.names.sup id at hm
  have hb : background.names.sup id < 30 := by decide
  omega
private def freshBackground := freshen background 30 background_names_lt
private def backgroundVacuity (v : Nat) (h : v ∉ freshBackground.formula.names) :
    KDerivation (imp background.encode (allCode v background.encode)) :=
  compose freshBackground.equivalent.forward
    (compose (freshBackground.formula.vacuity v h)
      (allCongr v freshBackground.equivalent.backward))

private theorem selected_names_lt : ∀ v ∈ selected.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ selected.names.sup id at hm
  have hb : selected.names.sup id < 30 := by decide
  omega
private def freshSelected := freshen selected 30 selected_names_lt
private def selectedVacuity (v : Nat) (h : v ∉ freshSelected.formula.names) :
    KDerivation (imp selected.encode (allCode v selected.encode)) :=
  compose freshSelected.equivalent.forward
    (compose (freshSelected.formula.vacuity v h)
      (allCongr v freshSelected.equivalent.backward))

/-- The first literal target-bijection conjunct follows from the two actual
bijections and the explicitly supplied restricted composition. -/
def forward_clause : KDerivation (imp background.encode forwardClause.encode) := by
  let R := PAtoCompactConditionalTransitivityEdgeForward.imageBody
  let M : Formula := .member 0 2
  let Γ := [background.encode]
  have hlocal : Context Γ (imp M.encode selected.encode) := by
    apply Context.deduction
    let Δ := [M.encode,background.encode]
    have hm : Context Δ M.encode := Context.head _ _
    have hb : Context Δ background.encode := .hypothesis (by simp [Δ])
    have htarget : Context Δ targetFamily.encode := .mp hb (.closed target_family)
    have hf : Context Δ bijectionFormula.encode := Context.conjunctionLeft hb
    have hg : Context Δ PAtoCompactConditionalTransitivityEdgeForward.secondBijection.encode :=
      Context.conjunctionLeft (Context.conjunctionRight hb)
    have hc : Context Δ composition.encode := Context.conjunctionRight (Context.conjunctionRight hb)
    have hpre : Context Δ PAtoCompactConditionalTransitivityEdgeForward.premises.encode :=
      Context.conjunctionIntro hf (Context.conjunctionIntro hg (Context.conjunctionIntro hc hm))
    have hrow : Context Δ (existsCode 3 R.encode) := by
      simpa only [PAtoCompactConditionalTransitivityEdgeForward.image, Formula.encode, R] using
        (.mp hpre (.closed PAtoCompactConditionalTransitivityEdgeForward.forward_image))
    have hselected : Context (R.encode :: Δ) selected.encode := by
      let Θ := R.encode :: Δ
      have hr : Context Θ R.encode := Context.head _ _
      have hmem : Context Θ (member 8 3) := Context.conjunctionLeft hr
      have hedge : Context Θ (graphFormula 9 2 3).encode := Context.conjunctionRight hr
      have hm' : Context Θ M.encode := .hypothesis (by simp [Θ, Δ])
      have ht : Context Θ targetFamily.encode := .under htarget _
      have h2 := allSpecialize 2 (.all 3 (.all 5 targetBody)) (by decide)
      have h3 := allSpecialize 3 (.all 5 targetBody) (by decide)
      have h5 := universalInstance 5 4 targetBody (by decide) (by decide) (by decide)
      let B4 : Formula := .imp (.member 0 2) (.imp (.member 8 3) (.imp (.member 8 4)
        (.imp (graphFormula 9 2 3) (.imp (graphFormula 9 2 4) (.equal 4 3)))))
      have heq : replace 5 4 targetBody = B4 := by decide
      rw [heq] at h5
      have hbody : Context Θ B4.encode := .mp (.mp (.mp ht (.closed h2)) (.closed h3)) (.closed h5)
      have huni : Context Θ uniqueBody.encode := by
        apply Context.deduction
        let A := both (member 8 4) (graphFormula 9 2 4).encode
        let Ξ := A :: Θ
        have hx : Context Ξ A := Context.head _ _
        have hdom : Context Ξ (member 8 4) := Context.conjunctionLeft hx
        have hedge' : Context Ξ (graphFormula 9 2 4).encode := Context.conjunctionRight hx
        have hu : Context Ξ B4.encode := .under hbody _
        exact .mp hedge' (.mp (.under hedge _) (.mp hdom (.mp (.under hmem _) (.mp (.under hm' _) hu))))
      have hv4 : ∀ f, f ∈ Θ → KDerivation (imp f (allCode 4 f)) := by
        intro f hf
        simp only [Θ, Δ, List.mem_cons, List.not_mem_nil, or_false] at hf
        by_cases hR : f = R.encode
        · subst f; exact R.vacuity 4 (by decide)
        · by_cases hM : f = M.encode
          · subst f; exact M.vacuity 4 (by decide)
          · have hB : f = background.encode := (hf.resolve_left hR).resolve_left hM
            subst f; exact backgroundVacuity 4 (by decide)
      have hall : Context Θ (allCode 4 uniqueBody.encode) := Context.generalize 4 hv4 huni
      have hw : Context Θ witnessBody.encode :=
        Context.conjunctionIntro hmem (Context.conjunctionIntro hedge hall)
      exact .mp hw (.closed (existsIntroduce 3 witnessBody (by decide)))
    have hv3 : ∀ f, f ∈ Δ → KDerivation (imp f (allCode 3 f)) := by
      intro f hf
      simp only [Δ, List.mem_cons, List.not_mem_nil, or_false] at hf
      by_cases hM : f = M.encode
      · subst f; exact M.vacuity 3 (by decide)
      · have hB : f = background.encode := hf.resolve_left hM
        subst f; exact backgroundVacuity 3 (by decide)
    exact Context.existsElim (selectedVacuity 3 (by decide))
      (Context.generalize 3 hv3 (Context.deduction hselected)) hrow
  have hv2 : ∀ f, f ∈ Γ → KDerivation (imp f (allCode 2 f)) := by
    intro f hf
    have he : f = background.encode := by simpa [Γ] using hf
    subst f
    exact backgroundVacuity 2 (by decide)
  exact Context.closeEmpty (Context.deduction (Context.generalize 2 hv2 hlocal))

theorem forward_clause_certificate : theoremCode (certificate forward_clause) =
    imp background.encode forwardClause.encode := certificate_correct forward_clause

end PASoundness.PAtoCompactConditionalTransitivityForwardClause

#print axioms PASoundness.PAtoCompactConditionalTransitivityForwardClause.forward_clause
#print axioms PASoundness.PAtoCompactConditionalTransitivityForwardClause.forward_clause_certificate
