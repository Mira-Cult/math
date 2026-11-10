import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.PAtoCompactFreeVacuity

/-! Zero-prefix base for collecting the span of two graphs over one common
candidate input. The two graph images and their endpoint objects may be
non-candidates. This finite K base proof constructs an empty partial span; it
does not prove the successor step or collect the full span graph. -/
namespace PASoundness.PAtoCompactCommonSourceSpanBase

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactZeroTransitive PASoundness.PAtoCompactPartialInverseBase
open PASoundness.PAtoCompactPartialCompositionBase PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Domains 0 and 8 are the two image objects; 1 is the common input, with
input graphs 6 and 7, output graph 9, and common-input prefix 10. A path uses
one common witness 4 in both input graphs. -/
def spanPathBody : Formula := namedBoth (.member 1 4)
  (namedBoth (.member 10 4)
    (namedBoth (graphFormula 6 4 2) (graphFormula 7 4 3)))

def spanPath : Formula := .ex 4 spanPathBody

def spanComposition : Formula := .all 2 (.all 3
  (.imp (namedBoth (.member 0 2) (.member 8 3))
    (namedBoth (.imp (graphFormula 9 2 3) spanPath)
      (.imp spanPath (graphFormula 9 2 3)))))

theorem spanComposition_free : spanComposition.free = {0,1,6,7,8,9,10} := by decide

/-- A zero common-input prefix and zero output graph satisfy the span
invariant. No candidate condition is needed for either image endpoint. -/
def empty_prefix_empty_span : KDerivation
    (imp (zeroCode 10 11) (imp (zeroCode 9 12) spanComposition.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let ZP := zeroCode 10 11
  let ZH := zeroCode 9 12
  let G := (graphFormula 9 2 3).encode
  let T := spanPath.encode
  let Y := both (member 0 2) (member 8 3)
  let Γ := [ZH,ZP]
  have hp : Context Γ ZP := .hypothesis (by simp [Γ])
  have hh : Context Γ ZH := .head _ _
  have hng : Context Γ (neg G) :=
    .mp hh (.closed (zero_has_no_edge 9 12 2 3 (by decide) (by decide) (by decide)))
  have hforward : Context Γ (imp G T) := by
    apply Context.deduction
    exact Context.explode T (.mp (.head _ _) (.under hng _))
  have hlocal : Context Γ (imp spanPathBody.encode G) := by
    apply Context.deduction
    let Δ := [spanPathBody.encode,ZH,ZP]
    have hbody : Context Δ spanPathBody.encode := .head _ _
    have hprefix : Context Δ (member 10 4) :=
      Context.conjunctionLeft (Context.conjunctionRight hbody)
    have hz : Context Δ ZP := .hypothesis (by simp [Δ])
    have hnot : Context Δ (neg (member 10 4)) :=
      .mp hz (.closed (zero_excludes 10 11 4 (by decide) (by decide)))
    exact Context.explode G (.mp hprefix hnot)
  have hv4 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh'
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh'
    by_cases he : h = ZH
    · subst h
      exact zero_graph_vacuity 9 12 4 (by decide) (by decide)
    · have he' : h = ZP := hh'.resolve_left he
      subst h
      exact zero_graph_vacuity 10 11 4 (by decide) (by decide)
  have hall4 := Context.generalize 4 hv4 hlocal
  have hback : Context Γ (imp T G) := by
    apply Context.deduction
    have ht : Context (T :: Γ) (existsCode 4 spanPathBody.encode) := by
      simpa only [T, spanPath, Formula.encode] using (Context.head Γ T)
    exact Context.existsElim (free_vacuity 4 (graphFormula 9 2 3) (by decide))
      (.under hall4 _) ht
  have hpoint : Context Γ (imp Y (both (imp G T) (imp T G))) :=
    Context.lift (Context.conjunctionIntro hforward hback) Y
  have hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh'
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh'
    by_cases he : h = ZH
    · subst h
      exact zero_graph_vacuity 9 12 3 (by decide) (by decide)
    · have he' : h = ZP := hh'.resolve_left he
      subst h
      exact zero_graph_vacuity 10 11 3 (by decide) (by decide)
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh'
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh'
    by_cases he : h = ZH
    · subst h
      exact zero_graph_vacuity 9 12 2 (by decide) (by decide)
    · have he' : h = ZP := hh'.resolve_left he
      subst h
      exact zero_graph_vacuity 10 11 2 (by decide) (by decide)
  exact Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)

/-- K constructs an actual empty-output-graph witness for a supplied zero
prefix; it does not assume existence of either input graph. -/
def empty_prefix_span_exists : KDerivation
    (imp (zeroCode 10 11) (existsCode 9 spanComposition.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Z := zeroCode 10 11
  let Γ := [Z]
  have hz : Context Γ Z := .head _ _
  have hi : Context Γ (imp (zeroCode 9 12) spanComposition.encode) :=
    .mp hz (.closed empty_prefix_empty_span)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 9 h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_graph_vacuity 10 11 9 (by decide) (by decide)
  have hall := Context.generalize 9 hv hi
  exact exists_map_context hall (.closed empty_graph_exists)

theorem empty_prefix_span_exists_certificate :
    theoremCode (certificate empty_prefix_span_exists) =
      imp (zeroCode 10 11) (existsCode 9 spanComposition.encode) :=
  certificate_correct empty_prefix_span_exists

end PASoundness.PAtoCompactCommonSourceSpanBase

#print axioms PASoundness.PAtoCompactCommonSourceSpanBase.spanPathBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanBase.spanPath
#print axioms PASoundness.PAtoCompactCommonSourceSpanBase.spanComposition
#print axioms PASoundness.PAtoCompactCommonSourceSpanBase.spanComposition_free
#print axioms PASoundness.PAtoCompactCommonSourceSpanBase.empty_prefix_empty_span
#print axioms PASoundness.PAtoCompactCommonSourceSpanBase.empty_prefix_span_exists
#print axioms PASoundness.PAtoCompactCommonSourceSpanBase.empty_prefix_span_exists_certificate
