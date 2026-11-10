import PASoundness.PAtoCompactProductCleanFilter
import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactGraphContextElim
import PASoundness.PAtoCompactGraphVacuity19
import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactMultiplicationCandidate

/-! Literal K edge preservation for the valid-triple filter. This does not
construct product graphs, prove the product matrix, collect a row, or establish
multiplication totality. Graphs and endpoint membership are explicit inputs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanRetain
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactProductCleanFilter PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactGraphContextElim PASoundness.PAtoCompactGraphVacuity19
open PASoundness.PAtoCompactGraphWitnessRules PASoundness.PAtoCompactMultiplicationCandidate
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def inner53 : Formula := namedBoth (pairFormula 53 3 4) (pairFormula 19 53 5)
private def inner52 : Formula := namedBoth (.member 2 52)
  (.ex 53 (namedBoth (pairFormula 53 3 4) (pairFormula 19 53 52)))
private def inner51 : Formula := namedBoth (.member 1 51)
  (.ex 52 (namedBoth (.member 2 52)
    (.ex 53 (namedBoth (pairFormula 53 3 51) (pairFormula 19 53 52)))))
private def inner50 : Formula := namedBoth (.member 0 50)
  (.ex 51 (namedBoth (.member 1 51)
    (.ex 52 (namedBoth (.member 2 52)
      (.ex 53 (namedBoth (pairFormula 53 50 51) (pairFormula 19 53 52)))))))

/-- Actual old endpoints and the two pair witnesses establish that this
edge satisfies the filter predicate, with no graph or semantic assumption. -/
def predicate_intro : KDerivation (imp (member 0 3) (imp (member 1 4)
    (imp (member 2 5) (imp (pairFormula 18 3 4).encode
      (imp (pairFormula 19 18 5).encode (cleanPredicate 19).encode))))) := by
  have i53 := exists_variable_intro 53 18 inner53 (by decide) (by decide) (by decide)
  have r53 : replace 53 18 inner53 = namedBoth (pairFormula 18 3 4) (pairFormula 19 18 5) := by decide
  rw [r53] at i53
  have i52 := exists_variable_intro 52 5 inner52 (by decide) (by decide) (by decide)
  have r52 : replace 52 5 inner52 = namedBoth (.member 2 5) (.ex 53 inner53) := by decide
  rw [r52] at i52
  have i51 := exists_variable_intro 51 4 inner51 (by decide) (by decide) (by decide)
  have r51 : replace 51 4 inner51 = namedBoth (.member 1 4) (.ex 52 inner52) := by decide
  rw [r51] at i51
  have i50 := exists_variable_intro 50 3 inner50 (by decide) (by decide) (by decide)
  have r50 : replace 50 3 inner50 = namedBoth (.member 0 3) (.ex 51 inner51) := by decide
  rw [r50] at i50
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 19 18 5).encode, (pairFormula 18 3 4).encode,
    member 2 5, member 1 4, member 0 3]
  have h19 : Context Γ (pairFormula 19 18 5).encode := .head _ _
  have h18 : Context Γ (pairFormula 18 3 4).encode := .hypothesis (by simp [Γ])
  have h5 : Context Γ (member 2 5) := .hypothesis (by simp [Γ])
  have h4 : Context Γ (member 1 4) := .hypothesis (by simp [Γ])
  have h3 : Context Γ (member 0 3) := .hypothesis (by simp [Γ])
  have a53 : Context Γ (namedBoth (pairFormula 18 3 4) (pairFormula 19 18 5)).encode := by
    simpa [namedBoth,Formula.encode,both,neg] using Context.conjunctionIntro h18 h19
  have e53 : Context Γ (Formula.ex 53 inner53).encode := .mp a53 (.closed i53)
  have a52 : Context Γ (namedBoth (.member 2 5) (.ex 53 inner53)).encode := by
    simpa [namedBoth,Formula.encode,both,neg] using Context.conjunctionIntro h5 e53
  have e52 : Context Γ (Formula.ex 52 inner52).encode := .mp a52 (.closed i52)
  have a51 : Context Γ (namedBoth (.member 1 4) (.ex 52 inner52)).encode := by
    simpa [namedBoth,Formula.encode,both,neg] using Context.conjunctionIntro h4 e52
  have e51 : Context Γ (Formula.ex 51 inner51).encode := .mp a51 (.closed i51)
  have a50 : Context Γ (namedBoth (.member 0 3) (.ex 51 inner51)).encode := by
    simpa [namedBoth,Formula.encode,both,neg] using Context.conjunctionIntro h3 e51
  have e50 : Context Γ (Formula.ex 50 inner50).encode := .mp a50 (.closed i50)
  simpa only [cleanPredicate, inner50] using e50

theorem predicate_intro_certificate : theoremCode (certificate predicate_intro) =
    imp (member 0 3) (imp (member 1 4)
      (imp (member 2 5) (imp (pairFormula 18 3 4).encode
        (imp (pairFormula 19 18 5).encode (cleanPredicate 19).encode)))) :=
  certificate_correct predicate_intro

private def filterNamed : Formula := .all 55 (namedFilterBody 6 54 55 (cleanPredicate 55))
private theorem filter_named_code : filterNamed.encode = filterCode 54 := by rfl
private def contextForm : Formula := namedBoth filterNamed
  (namedBoth (.member 0 3) (namedBoth (.member 1 4) (.member 2 5)))
def tripleAt (g : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 3 4) (graphFormula g 18 5))

/-- At the original graph name this is exactly the multiplication triple. -/
theorem triple_at_original : tripleAt 6 = tripleFormula 3 4 5 := by rfl

/-- A valid old graph edge at pair-name 18 is present in the supplied
filtered graph. The filter and all three endpoint memberships are explicit. -/
def retain_graph_edge : KDerivation (imp (filterCode 54) (imp (member 0 3)
    (imp (member 1 4) (imp (member 2 5) (imp (pairFormula 18 3 4).encode
      (imp (graphFormula 6 18 5).encode (graphFormula 54 18 5).encode)))))) := by
  let F := filterCode 54
  let P := (pairFormula 18 3 4).encode
  let X := member 0 3
  let Y := member 1 4
  let Z := member 2 5
  let Γ := [P,Z,Y,X,F]
  have hvF : KDerivation (imp F (allCode 19 F)) := by
    simpa only [filter_named_code] using filterNamed.vacuity 19 (by decide)
  have hvP : KDerivation (imp P (allCode 19 P)) := by
    exact (pairFormula 18 3 4).vacuity 19 (by decide)
  have hvX : KDerivation (imp X (allCode 19 X)) := by
    exact (Formula.member 0 3).vacuity 19 (by decide)
  have hvY : KDerivation (imp Y (allCode 19 Y)) := by
    exact (Formula.member 1 4).vacuity 19 (by decide)
  have hvZ : KDerivation (imp Z (allCode 19 Z)) := by
    exact (Formula.member 2 5).vacuity 19 (by decide)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 19 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases hp : h = P
    · subst h; exact hvP
    by_cases hz : h = Z
    · subst h; exact hvZ
    by_cases hy : h = Y
    · subst h; exact hvY
    by_cases hx : h = X
    · subst h; exact hvX
    have hf : h = F := by simpa [hp,hz,hy,hx] using hh
    subst h
    exact hvF
  let W := both (member 6 19) (pairFormula 19 18 5).encode
  have hstep : Context Γ (imp W (graphFormula 54 18 5).encode) := by
    apply Context.deduction
    have hw : Context (W :: Γ) W := Context.head Γ W
    have hf : Context (W :: Γ) F := .hypothesis (by simp [Γ])
    have hp : Context (W :: Γ) P := .hypothesis (by simp [Γ])
    have hx : Context (W :: Γ) X := .hypothesis (by simp [Γ])
    have hy : Context (W :: Γ) Y := .hypothesis (by simp [Γ])
    have hz : Context (W :: Γ) Z := .hypothesis (by simp [Γ])
    have hpair := Context.conjunctionRight hw
    have hpred : Context (W :: Γ) (cleanPredicate 19).encode :=
      .mp hpair (.mp hp (.mp hz (.mp hy (.mp hx (.closed predicate_intro)))))
    have hfilter := Context.mp hf (.closed filter_at_graph_witness)
    have hm : Context (W :: Γ) (member 54 19) :=
      .mp (Context.conjunctionIntro (Context.conjunctionLeft hw) hpred) (Context.conjunctionRight hfilter)
    exact .mp (Context.conjunctionIntro hm hpair) (.closed (graph_intro 54 18 5))
  have hg : Context Γ (imp (graphFormula 6 18 5).encode (graphFormula 54 18 5).encode) :=
    graph_context_imp Γ 6 18 5 (graphFormula 54 18 5) hv (graph_vacuity_19 54 18 5) hstep
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hg

/-- The valid triple itself is preserved by the supplied filter. Its inner
pair witness is existential and need not be supplied separately. -/
def retain_triple : KDerivation (imp (filterCode 54) (imp (member 0 3)
    (imp (member 1 4) (imp (member 2 5)
      (imp (tripleAt 6).encode (tripleAt 54).encode))))) := by
  let E := contextForm.encode
  let A := (namedBoth (pairFormula 18 3 4) (graphFormula 6 18 5)).encode
  let B := (namedBoth (pairFormula 18 3 4) (graphFormula 54 18 5)).encode
  have hv : KDerivation (imp E (allCode 18 E)) := contextForm.vacuity 18 (by decide)
  have hi : KDerivation (imp E (imp A B)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,E]
    have ha : Context Γ A := .head _ _
    have he : Context Γ E := .hypothesis (by simp [Γ])
    have hf : Context Γ (filterCode 54) := by
      simpa [E,contextForm,namedBoth,Formula.encode,both,neg,filter_named_code] using Context.conjunctionLeft he
    have hs := Context.conjunctionRight he
    have hx : Context Γ (member 0 3) := Context.conjunctionLeft hs
    have hy : Context Γ (member 1 4) := Context.conjunctionLeft (Context.conjunctionRight hs)
    have hz : Context Γ (member 2 5) := Context.conjunctionRight (Context.conjunctionRight hs)
    have hp : Context Γ (pairFormula 18 3 4).encode := Context.conjunctionLeft ha
    have hg : Context Γ (graphFormula 6 18 5).encode := Context.conjunctionRight ha
    have ht : Context Γ (graphFormula 54 18 5).encode :=
      .mp hg (.mp hp (.mp hz (.mp hy (.mp hx (.mp hf (.closed retain_graph_edge))))))
    simpa [B,namedBoth,Formula.encode,both,neg] using Context.conjunctionIntro hp ht
  have hh := conditionalExistsCongr 18 hv hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 2 5,member 1 4,member 0 3,filterCode 54]
  have hz : Context Γ (member 2 5) := .head _ _
  have hy : Context Γ (member 1 4) := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 0 3) := .hypothesis (by simp [Γ])
  have hf : Context Γ (filterCode 54) := .hypothesis (by simp [Γ])
  have he : Context Γ E := by
    simpa [E,contextForm,namedBoth,Formula.encode,both,neg,filter_named_code] using
      Context.conjunctionIntro hf (Context.conjunctionIntro hx (Context.conjunctionIntro hy hz))
  simpa [tripleAt,A,B,Formula.encode] using Context.mp he (.closed hh)

theorem retain_graph_edge_certificate : theoremCode (certificate retain_graph_edge) =
    imp (filterCode 54) (imp (member 0 3)
      (imp (member 1 4) (imp (member 2 5) (imp (pairFormula 18 3 4).encode
        (imp (graphFormula 6 18 5).encode (graphFormula 54 18 5).encode))))) :=
  certificate_correct retain_graph_edge

theorem retain_triple_certificate : theoremCode (certificate retain_triple) =
    imp (filterCode 54) (imp (member 0 3) (imp (member 1 4) (imp (member 2 5)
      (imp (tripleAt 6).encode (tripleAt 54).encode)))) := certificate_correct retain_triple

end PASoundness.PAtoCompactProductCleanRetain
#print axioms PASoundness.PAtoCompactProductCleanRetain.predicate_intro
#print axioms PASoundness.PAtoCompactProductCleanRetain.predicate_intro_certificate

#print axioms PASoundness.PAtoCompactProductCleanRetain.retain_graph_edge
#print axioms PASoundness.PAtoCompactProductCleanRetain.retain_triple
#print axioms PASoundness.PAtoCompactProductCleanRetain.retain_triple_certificate

#print axioms PASoundness.PAtoCompactProductCleanRetain.triple_at_original
#print axioms PASoundness.PAtoCompactProductCleanRetain.retain_graph_edge_certificate
