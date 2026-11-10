import PASoundness.PAtoCompactConditionalTransitivitySourceAll
import PASoundness.PAtoCompactConditionalTransitivityEdgeReverse
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.CompactFreshen

/-! Assemble the literal reverse bijection clause from the proved guarded
source-uniqueness family and an explicitly supplied preimage-existence proof.
This constructs neither that proof nor a composition graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityReverseClause
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivitySecondUnique
open PASoundness.PAtoCompactConditionalTransitivitySourceComposite
open PASoundness.PAtoCompactConditionalTransitivitySourceAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def simpleWitness : Formula := namedBoth (.member 0 2) (graphFormula 9 2 3)
def candidateBodyOperand : Formula := namedBoth (.member 0 4) (graphFormula 9 4 3)
def candidateBody : Formula := .imp candidateBodyOperand (.equal 4 2)
def uniqueTest : Formula := .all 4 candidateBody
def fullWitness : Formula := namedBoth (.member 0 2)
  (namedBoth (graphFormula 9 2 3) uniqueTest)
def rightClause : Formula := .all 3 (.imp (.member 8 3) (.ex 2 fullWitness))

private theorem background_names_lt : ∀ v ∈ background.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ background.names.sup id at hm
  have hb : background.names.sup id < 30 := by decide
  omega

private def freshBackground := freshen background 30 background_names_lt
private theorem fresh_no2 : 2 ∉ freshBackground.formula.names := by decide
private theorem fresh_no3 : 3 ∉ freshBackground.formula.names := by decide
private theorem fresh_no4 : 4 ∉ freshBackground.formula.names := by decide
private def backgroundVacuity (v : Nat) (h : v ∉ freshBackground.formula.names) :
    KDerivation (imp background.encode (allCode v background.encode)) :=
  compose freshBackground.equivalent.forward
    (compose (freshBackground.formula.vacuity v h)
      (allCongr v freshBackground.equivalent.backward))

private def family_at32 : KDerivation (imp family.encode (allCode 4 PAtoCompactConditionalTransitivitySourceAll.point.encode)) := by
  have h3 := allSpecialize 3 (.all 2 (.all 4 PAtoCompactConditionalTransitivitySourceAll.point)) (by decide)
  have h2 := allSpecialize 2 (.all 4 PAtoCompactConditionalTransitivitySourceAll.point) (by decide)
  exact compose h3 h2

/-- Every supplied simple preimage can be enriched by the actual quantified
uniqueness condition, retaining exactly the same preimage name 2. -/
private def witness_enrich : KDerivation
    (imp background.encode (imp (member 8 3) (imp simpleWitness.encode fullWitness.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let W := simpleWitness.encode
  let M := member 8 3
  let B := background.encode
  let Γ := [W,M,B]
  have hw : Context Γ W := Context.head _ _
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 2) := Context.conjunctionLeft hw
  have he : Context Γ edge.encode := Context.conjunctionRight hw
  have hall : Context Γ (allCode 4 PAtoCompactConditionalTransitivitySourceAll.point.encode) :=
    .mp (.mp hb (.closed source_unique_all)) (.closed family_at32)
  have hp : Context Γ PAtoCompactConditionalTransitivitySourceAll.point.encode :=
    .mp hall (.closed (allSpecialize 4 PAtoCompactConditionalTransitivitySourceAll.point (by decide)))
  have hlocal : Context Γ candidateBody.encode := by
    apply Context.deduction
    let Δ := candidateBodyOperand.encode :: Γ
    have hc : Context Δ candidateBodyOperand.encode := Context.head _ _
    have ha' : Context Δ (member 0 4) := Context.conjunctionLeft hc
    have he' : Context Δ secondEdge.encode := Context.conjunctionRight hc
    have hp' : Context Δ PAtoCompactConditionalTransitivitySourceAll.point.encode := Context.under hp _
    have hg : Context Δ guard.encode := Context.conjunctionIntro (Context.under hm _)
      (Context.conjunctionIntro (Context.under ha _) (Context.conjunctionIntro ha'
        (Context.conjunctionIntro (Context.under he _) he')))
    exact .mp hg hp'
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro f hf
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hf
    by_cases hW : f = W
    · subst f
      exact simpleWitness.vacuity 4 (by decide)
    · by_cases hM : f = M
      · subst f
        exact (Formula.member 8 3).vacuity 4 (by decide)
      · have hB : f = B := (hf.resolve_left hW).resolve_left hM
        subst f
        exact backgroundVacuity 4 fresh_no4
  have hu : Context Γ uniqueTest.encode := Context.generalize 4 hv hlocal
  exact Context.conjunctionIntro ha (Context.conjunctionIntro he hu)

/-- The supplied preimage-existence derivation is the sole additional
premise. No graph collection or existence theorem is hidden in this wrapper. -/
def right_of_existence
    (hexists : KDerivation (imp background.encode
      (imp (member 8 3) (existsCode 2 simpleWitness.encode)))) :
    KDerivation (imp background.encode rightClause.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let B := background.encode
  let M := member 8 3
  let Γ := [B]
  have hb : Context Γ B := Context.head _ _
  have hlocal : Context Γ (imp M (existsCode 2 fullWitness.encode)) := by
    apply Context.deduction
    let Δ := [M,B]
    have hm : Context Δ M := Context.head _ _
    have hb' : Context Δ B := Context.under hb M
    have he : Context Δ (existsCode 2 simpleWitness.encode) :=
      .mp hm (.mp hb' (.closed hexists))
    have hi : Context Δ (imp simpleWitness.encode fullWitness.encode) :=
      .mp hm (.mp hb' (.closed witness_enrich))
    have hv : ∀ h, h ∈ Δ → KDerivation (imp h (allCode 2 h)) := by
      intro f hf
      simp only [Δ, List.mem_cons, List.not_mem_nil, or_false] at hf
      by_cases hM : f = M
      · subst f
        exact (Formula.member 8 3).vacuity 2 (by decide)
      · have hB : f = B := hf.resolve_left hM
        subst f
        exact backgroundVacuity 2 fresh_no2
    have hall : Context Δ (allCode 2 (imp simpleWitness.encode fullWitness.encode)) :=
      Context.generalize 2 hv hi
    exact exists_map_context hall he
  have hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro f hf
    have hB : f = B := by simpa [Γ] using hf
    subst f
    exact backgroundVacuity 3 fresh_no3
  exact Context.generalize 3 hv3 hlocal

theorem right_of_existence_certificate
    (hexists : KDerivation (imp background.encode
      (imp (member 8 3) (existsCode 2 simpleWitness.encode)))) :
    theoremCode (certificate (right_of_existence hexists)) =
      imp background.encode rightClause.encode := certificate_correct (right_of_existence hexists)

/-- The supplied composition and both literal bijections derive the exact
reverse clause; preimage existence is constructed by the imported K proof. -/
def right_clause : KDerivation (imp background.encode rightClause.encode) := by
  have hexists : KDerivation (imp background.encode
      (imp (member 8 3) (existsCode 2 simpleWitness.encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 8 3, background.encode]
    have hm : Context Γ (member 8 3) := Context.head _ _
    have hb : Context Γ background.encode := .hypothesis (by simp [Γ])
    have hf : Context Γ bijectionFormula.encode := Context.conjunctionLeft hb
    have hg : Context Γ secondBijection.encode := Context.conjunctionLeft (Context.conjunctionRight hb)
    have hc : Context Γ composition.encode := Context.conjunctionRight (Context.conjunctionRight hb)
    exact .mp hm (.mp hc (.mp hg (.mp hf
      (.closed PAtoCompactConditionalTransitivityEdgeReverse.reverse_edge_exists_curried))))
  exact right_of_existence hexists

/-- The clause is literally the right conjunct of the renamed target
bijection, with codomain 8 and graph 9. -/
def targetBijection : Formula := replace 6 9 (replace 1 8 bijectionFormula)
def targetRight : Formula := match targetBijection with
  | .imp (.imp _ (.imp right _)) _ => right
  | _ => .truth

theorem rightClause_exact : rightClause = targetRight := by decide

theorem right_clause_certificate : theoremCode (certificate right_clause) =
    imp background.encode rightClause.encode := certificate_correct right_clause

end PASoundness.PAtoCompactConditionalTransitivityReverseClause

#print axioms PASoundness.PAtoCompactConditionalTransitivityReverseClause.right_of_existence
#print axioms PASoundness.PAtoCompactConditionalTransitivityReverseClause.right_of_existence_certificate
#print axioms PASoundness.PAtoCompactConditionalTransitivityReverseClause.right_clause
#print axioms PASoundness.PAtoCompactConditionalTransitivityReverseClause.right_clause_certificate
