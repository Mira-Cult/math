import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactAdjunction

/-! A conditional finite K lift from same-witness outer-edge reflection to
product-triple reflection, at queried coordinates 7, 8 and 5. The outer edge
is alpha-rebound from 19 to 63, and both pair witnesses are retained. The
edge-classification proof remains an explicit input; no graph extensionality,
product graph construction, or multiplication totality is asserted. -/
namespace PASoundness.PAtoCompactProductTripleReflectionLift
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactAdjunction
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Actual queried inner pair; labels 7 and 8 are the two coordinates. -/
def coordinates : Formula := pairFormula 18 7 8
/-- Exact outer graph member at a selectable witness name. -/
def outer (g e : Nat) : Formula := namedBoth (.member g e) (pairFormula e 18 5)
/-- Product triple using graph g and the displayed coordinates. -/
def triple (g : Nat) : Formula := .ex 18 (namedBoth coordinates (graphFormula g 18 5))
/-- The same triple with the outer graph witness rebound to 63. -/
def expanded (g : Nat) : Formula := .ex 18 (.ex 63 (namedBoth coordinates (outer g 63)))
/-- Exact pair descriptions used by the supplied pointwise edge reflection. -/
def queryPairs : Formula := namedBoth (pairFormula 63 18 5) coordinates

private def expand64 : KDerivation (imp (triple 64).encode (expanded 64).encode) := by
  have halpha := (existentialAlpha 19 63 (outer 64 19) (by decide) (by decide) (by decide)).1
  have hshape : replace 19 63 (outer 64 19) = outer 64 63 := by decide
  rw [hshape] at halpha
  have hg : KDerivation (imp (graphFormula 64 18 5).encode (existsCode 63 (outer 64 63).encode)) := by
    change KDerivation (imp (existsCode 19 (outer 64 19).encode) (existsCode 63 (outer 64 63).encode))
    exact halpha
  have hpair : KDerivation (imp coordinates.encode (imp (outer 64 63).encode
      (namedBoth coordinates (outer 64 63)).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(outer 64 63).encode,coordinates.encode]
    have ho : Context Γ (outer 64 63).encode := .head _ _
    have hc : Context Γ coordinates.encode := .hypothesis (by simp [Γ])
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using Context.conjunctionIntro hc ho
  have hc := conditionalExistsCongr 63 (coordinates.vacuity 63 (by decide)) hpair
  have hin : KDerivation (imp (namedBoth coordinates (graphFormula 64 18 5)).encode
      (existsCode 63 (namedBoth coordinates (outer 64 63)).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [(namedBoth coordinates (graphFormula 64 18 5)).encode]
    have h : Context Γ (both coordinates.encode (graphFormula 64 18 5).encode) := by
      simpa [Γ,namedBoth,Formula.not,Formula.encode,both,neg] using (Context.head [] _)
    exact .mp (.mp (Context.conjunctionRight h) (.closed hg))
      (.mp (Context.conjunctionLeft h) (.closed hc))
  simpa [triple,expanded,Formula.encode] using existsCongr 18 hin

private def fold10 : KDerivation (imp (expanded 10).encode (triple 10).encode) := by
  let target := namedBoth coordinates (graphFormula 10 18 5)
  let source := namedBoth coordinates (outer 10 63)
  have hi := exists_variable_intro 19 63 (outer 10 19) (by decide) (by decide) (by decide)
  have hshape : replace 19 63 (outer 10 19) = outer 10 63 := by decide
  rw [hshape] at hi
  have hg : KDerivation (imp (outer 10 63).encode (graphFormula 10 18 5).encode) := by
    change KDerivation (imp (outer 10 63).encode (existsCode 19 (outer 10 19).encode))
    exact hi
  have hlocal : KDerivation (imp source.encode target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [source.encode]
    have h : Context Γ (both coordinates.encode (outer 10 63).encode) := by
      simpa [Γ,source,namedBoth,Formula.not,Formula.encode,both,neg] using (Context.head [] _)
    have hedge := Context.mp (Context.conjunctionRight h) (.closed hg)
    simpa [target,namedBoth,Formula.not,Formula.encode,both,neg] using
      Context.conjunctionIntro (Context.conjunctionLeft h) hedge
  have hv : KDerivation (imp target.encode (allCode 63 target.encode)) :=
    free_vacuity 63 target (by decide)
  have hin : KDerivation (imp (existsCode 63 source.encode) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 63 hlocal)) (.head [] _)
  simpa [expanded,triple,source,target,Formula.encode] using existsCongr 18 hin

/-- If the exact outer edge can be reflected under H while retaining the two
pair descriptions, the corresponding full triple reflects. Freshness keeps
H independent of the two existential witness labels. -/
def triple_reflection_of_edge
    (H : Formula) (h18 : 18 ∉ H.names) (h63 : 63 ∉ H.names)
    (edge : KDerivation (imp H.encode (imp queryPairs.encode
      (imp (member 64 63) (member 10 63))))) :
    KDerivation (imp H.encode (imp (triple 64).encode (triple 10).encode)) := by
  have hlocal : KDerivation (imp H.encode
      (imp (namedBoth coordinates (outer 64 63)).encode
        (namedBoth coordinates (outer 10 63)).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(namedBoth coordinates (outer 64 63)).encode,H.encode]
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have hw : Context Γ (both coordinates.encode (both (member 64 63) (pairFormula 63 18 5).encode)) := by
      simpa [Γ,outer,namedBoth,Formula.not,Formula.encode,both,neg] using (Context.head [H.encode] _)
    have hp : Context Γ queryPairs.encode := by
      simpa [queryPairs,namedBoth,Formula.not,Formula.encode,both,neg] using
        Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight hw)) (Context.conjunctionLeft hw)
    have hm : Context Γ (member 10 63) :=
      .mp (Context.conjunctionLeft (Context.conjunctionRight hw)) (.mp hp (.mp hh (.closed edge)))
    have ho : Context Γ (outer 10 63).encode := by
      simpa [outer,namedBoth,Formula.not,Formula.encode,both,neg] using
        Context.conjunctionIntro hm (Context.conjunctionRight (Context.conjunctionRight hw))
    simpa [Γ,namedBoth,Formula.not,Formula.encode,both,neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hw) ho
  have h63' := conditionalExistsCongr 63 (H.vacuity 63 h63) hlocal
  have h18' := conditionalExistsCongr 18 (H.vacuity 18 h18) h63'
  have hm : KDerivation (imp H.encode (imp (expanded 64).encode (expanded 10).encode)) := by
    simpa [expanded,Formula.encode] using h18'
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(triple 64).encode,H.encode]
  have ht : Context Γ (triple 64).encode := .head _ _
  have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
  exact .mp (.mp (.mp ht (.closed expand64)) (.mp hh (.closed hm))) (.closed fold10)

theorem triple_reflection_of_edge_certificate
    (H : Formula) (h18 : 18 ∉ H.names) (h63 : 63 ∉ H.names)
    (edge : KDerivation (imp H.encode (imp queryPairs.encode
      (imp (member 64 63) (member 10 63))))) :
    theoremCode (certificate (triple_reflection_of_edge H h18 h63 edge)) =
      imp H.encode (imp (triple 64).encode (triple 10).encode) :=
  certificate_correct (triple_reflection_of_edge H h18 h63 edge)
end PASoundness.PAtoCompactProductTripleReflectionLift
#print axioms PASoundness.PAtoCompactProductTripleReflectionLift.triple_reflection_of_edge
#print axioms PASoundness.PAtoCompactProductTripleReflectionLift.triple_reflection_of_edge_certificate
