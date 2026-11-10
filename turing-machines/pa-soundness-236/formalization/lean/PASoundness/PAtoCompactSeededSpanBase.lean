import PASoundness.PAtoCompactCommonSourceSpanBase
import PASoundness.PAtoCompactAdjunction

/-! Empty-prefix base for collecting a common-source span on top of an
arbitrary supplied seed graph. The output graph is the same supplied seed at
the base, so K constructs the existential witness without assuming the seed
or either image object is a candidate. This does not prove the successor
step, collection, or addition congruence. -/
namespace PASoundness.PAtoCompactSeededSpanBase

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactZeroTransitive PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactCommonSourceSpanBase

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A seed edge at graph 14 or a common-source path in the processed prefix
counts as an output edge at graph 9, restricted to the image endpoints. -/
def seededSpan : Formula := .all 2 (.all 3
  (.imp (namedBoth (.member 0 2) (.member 8 3))
    (namedBoth
      (.imp (graphFormula 9 2 3) (namedEither (graphFormula 14 2 3) spanPath))
      (.imp (namedEither (graphFormula 14 2 3) spanPath) (graphFormula 9 2 3)))))

def seedAtSameGraph : Formula := replace 9 14 seededSpan

private def point : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth
    (.imp (graphFormula 14 2 3) (namedEither (graphFormula 14 2 3) spanPath))
    (.imp (namedEither (graphFormula 14 2 3) spanPath) (graphFormula 14 2 3)))

private theorem point_syntax : seedAtSameGraph = .all 2 (.all 3 point) := by decide

/-- A zero processed prefix has no common-source path, independently of the
input graphs and both image objects. -/
def zero_prefix_no_path : KDerivation (imp (zeroCode 10 11) (neg spanPath.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [zeroCode 10 11]
  have hz : Context Γ (zeroCode 10 11) := .head _ _
  have hlocal : Context Γ (imp spanPathBody.encode 1) := by
    apply Context.deduction
    let Δ := [spanPathBody.encode,zeroCode 10 11]
    have hb : Context Δ spanPathBody.encode := .head _ _
    have hm : Context Δ (member 10 4) := Context.conjunctionLeft (Context.conjunctionRight hb)
    have hzero : Context Δ (zeroCode 10 11) := .hypothesis (by simp [Δ])
    have hn : Context Δ (neg (member 10 4)) :=
      .mp hzero (.closed (zero_excludes 10 11 4 (by decide) (by decide)))
    exact .mp hm hn
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    have he : h = zeroCode 10 11 := by simpa [Γ] using hh
    subst h
    exact zero_graph_vacuity 10 11 4 (by decide) (by decide)
  have hall := Context.generalize 4 hv hlocal
  apply Context.deduction
  have he : Context (spanPath.encode :: Γ) (existsCode 4 spanPathBody.encode) := by
    simpa only [spanPath, Formula.encode] using Context.head Γ spanPath.encode
  exact Context.existsElim (explosion (allCode 4 1)) (.under hall _) he

/-- Under a zero processed prefix, the seed graph itself realizes the full
endpoint-guarded seeded-span invariant. -/
def zero_prefix_seed_invariant : KDerivation
    (imp (zeroCode 10 11) seedAtSameGraph.encode) := by
  let Γ := [zeroCode 10 11]
  have hz : Context Γ (zeroCode 10 11) := .head _ _
  have hn : Context Γ (neg spanPath.encode) := .mp hz (.closed zero_prefix_no_path)
  have hpoint : Context Γ point.encode := by
    apply Context.deduction
    let D := both (member 0 2) (member 8 3)
    let G := (graphFormula 14 2 3).encode
    let P := spanPath.encode
    let Δ := [D,zeroCode 10 11]
    have hnot : Context Δ (neg P) := .under hn _
    have hf : Context Δ (imp G (either G P)) := by
      apply Context.deduction
      exact Context.disjunctionLeft (b := P) (.head _ _)
    have hb : Context Δ (imp (either G P) G) := by
      apply Context.deduction
      let Θ := either G P :: Δ
      have he : Context Θ (either G P) := .head _ _
      apply Context.disjunctionElim he
      · exact .head _ _
      · exact Context.explode G (.mp (.head _ _) (.under (.under hnot _) _))
    exact Context.conjunctionIntro hf hb
  have hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = zeroCode 10 11 := by simpa [Γ] using hh
    subst h
    exact zero_graph_vacuity 10 11 3 (by decide) (by decide)
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = zeroCode 10 11 := by simpa [Γ] using hh
    subst h
    exact zero_graph_vacuity 10 11 2 (by decide) (by decide)
  have hall : Context Γ seedAtSameGraph.encode := by
    simpa only [point_syntax, Formula.encode] using
      Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)
  exact Context.closeEmpty (Context.deduction hall)

/-- The supplied seed itself yields an actual output-graph existential for
the zero processed prefix. -/
def zero_prefix_seed_graph_exists : KDerivation
    (imp (zeroCode 10 11) (existsCode 9 seededSpan.encode)) := by
  have hi := exists_variable_intro 9 14 seededSpan (by decide) (by decide) (by decide)
  change KDerivation (imp seedAtSameGraph.encode (existsCode 9 seededSpan.encode)) at hi
  exact compose zero_prefix_seed_invariant hi

theorem zero_prefix_seed_graph_exists_certificate :
    theoremCode (certificate zero_prefix_seed_graph_exists) =
      imp (zeroCode 10 11) (existsCode 9 seededSpan.encode) :=
  certificate_correct zero_prefix_seed_graph_exists

end PASoundness.PAtoCompactSeededSpanBase

#print axioms PASoundness.PAtoCompactSeededSpanBase.seededSpan
#print axioms PASoundness.PAtoCompactSeededSpanBase.seedAtSameGraph
#print axioms PASoundness.PAtoCompactSeededSpanBase.zero_prefix_no_path
#print axioms PASoundness.PAtoCompactSeededSpanBase.zero_prefix_seed_invariant
#print axioms PASoundness.PAtoCompactSeededSpanBase.zero_prefix_seed_graph_exists
#print axioms PASoundness.PAtoCompactSeededSpanBase.zero_prefix_seed_graph_exists_certificate
